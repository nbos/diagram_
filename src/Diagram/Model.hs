{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Diagram.Model (module Diagram.Model) where

import Control.Lens hiding ((:>))
import Control.Exception (assert)
import Control.Monad.Primitive (PrimMonad)
import Control.Monad

import Data.Word
import Data.Maybe
import Data.Monoid
import Data.Tuple.Extra
import qualified Data.List as L
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IM

import Numeric.SpecFunctions (logFactorial)
import Numeric.MathFunctions.Comparison

import Streaming hiding (Sum,first)
import qualified Streaming.Prelude as S
import qualified Diagram.Streaming as S

import Data.Trie (Trie(..))
import qualified Data.Trie as Trie
import qualified Data.Trie.Internal as Trie
import qualified Diagram.Trie as Trie

import Diagram.Dynamic (BoxedVec)
import qualified Diagram.Dynamic as DMV
import Diagram.Rules (Rules)
import qualified Diagram.Rules as R
import Diagram.Util

err :: [Char] -> a
err = error . ("Diagram.Model: " ++)

data Weight = Weight {
  _weightNum   :: !Int, -- ^ Number of times this distr. is sampled
  _weightDenom :: !Int, -- ^ Number of samples in this distribution
  _weightRes   :: !Double -- ^ `num / denom`
} deriving (Show,Eq)
makeLenses ''Weight

checkWeight :: Weight -> a -> a
checkWeight w@(Weight num denom res)
  | num > denom =
      err $ "Numerator should be less or equal to denominator: "
      ++ show w
  | not $ within 100 res $ fromIntegral num / fromIntegral denom =
      err $ "Weight value is not equal to num/denom ("
      ++ show (ulpDistance res $ fromIntegral num / fromIntegral denom)
      ++ " ULPs of difference (tolerance 100)): " ++ show w
  | otherwise = id

zeroWeight :: Weight
zeroWeight = Weight 0 0 0.0

weightFromRatio :: Int -> Int -> Weight
weightFromRatio num denom | denom > 0 = Weight num denom res
                          | otherwise = zeroWeight
  where res = fromIntegral num / fromIntegral denom

-- | The log (base e) of a multinomial coefficient. The total (the `n`)
-- has the true value, but since the counts (the `k`s) are mostly just
-- the parent's, we only store the counts claimed by this context
-- (i.e. distinct from the parents)
data Coef = Coef {
  _coefTotal  :: !Int,          -- ^ The sum of the counts
  _coefClaims :: !(IntMap Int), -- ^ Counts that differ from parent's
  _coefLog    :: !Double        -- ^ Log (nat) of the coefficient
} deriving (Show)
makeLenses ''Coef

checkCoef :: Coef -> a -> a
checkCoef c@(Coef total m lc)
  | sum m > total = err $ "Coef total is too high: " ++ show c
  | lc > logFactorial total - sum (logFactorial <$> m) =
      err $ "Coef value is too high: " ++ show c
  | otherwise = id

zeroCoef :: Coef
zeroCoef = Coef 0 IM.empty (-inf)

-- | Construct a root Coef from a map of counts
rootCoef :: IntMap Int -> Coef
rootCoef counts | total > 0 = Coef total counts res
                | otherwise = zeroCoef
  where total = sum counts
        res = logFactorial total
              - sum (logFactorial <$> counts)

-- | The information content of our model in a certain context, factored
-- as a weighted log-multinomial coefficient. The information content of
-- the model is the sum of terms.
data Term = Term {
  _termWeight :: !Weight, -- ^ Weight factor
  _termCoef   :: !Coef,   -- ^ (log-)Coefficient factor
  _termRes    :: !Double  -- ^ Product of weight and log-coef
} deriving (Show)
makeLenses ''Term

checkTerm :: Term -> a -> a
checkTerm t@(Term weight@(Weight _ denom w) coef@(Coef total _ lc) res)
  | denom /= total =
      err $ "Weight denom is not equal to Coef total: " ++ show t
  | not $ within 100 res $ w * lc =
      err $ "Term value is not equal to weight * logCoef ("
      ++ show (ulpDistance res (w*lc))
      ++ " ULPs of difference (tolerance 100)): " ++ show t
  | otherwise = checkCoef coef . checkWeight weight

-- | Construct a root Term from a map of counts
rootTerm :: IntMap Int -> Term
rootTerm counts | total > 0 = Term weight coef $ coef^.coefLog
                | otherwise = Term zeroWeight zeroCoef 0.0
  where coef = rootCoef counts
        total = coef^.coefTotal
        weight = Weight total total 1.0

fromFactors :: Weight -> Coef -> Term
fromFactors w c = Term w c $ w^.weightRes * c^.coefLog

-- | Construct a Term with no claim (snd) from its parent, given the
-- number of times that context will appear and deduct that same amount
-- from the parent's term (fst) (the sum of numerators has to remain
-- constant in the model)
emptyFromParent :: Int -> Term -> (Term, Term)
emptyFromParent num (Term (Weight pNum denom _) pCoef _) =
  assert (denom == pCoef^.coefTotal)
  assert (num <= pNum) ( fromFactors pWeight' pCoef,
                         fromFactors weight coef )
  where
    pNum' = pNum - num
    pWeight' = weightFromRatio pNum' denom

    weight = weightFromRatio num denom
    coef = pCoef & coefClaims .~ IM.empty

-- | Check if a term claims a symbol
claims :: Term -> Int -> Bool
claims = flip IM.member . (^.termCoef.coefClaims)

----------
-- TRIE --
----------

checkTrie :: ContextTrie -> a -> a
checkTrie ctxs = foldr ((.) . checkLineageOf) id $
                 Trie.keys ctxs
  where
    checkLineageOf :: ByteString -> a -> a
    checkLineageOf bs = -- check lineage starting w/ root
      let lineage = fmap (snd . snd3) $ reverse $ Trie.matches ctxs bs
      in go IM.empty lineage

    go _ [] = id
    go acc (t@(Term _ (Coef total m lc) _):rest)
      | sum counts /= total =
          err $ "Realized counts don't sum to stored total "
          ++ show (sum counts, total) ++ ": " ++ show t
          ++ "\n\n in trie \n\n" ++ Trie.showTrie ctxs

      | not $ within 100 lc logCoef =
          err $ "Computed log-Coef is not equal to stored value ("
          ++ show (ulpDistance lc logCoef)
          ++ " ULPs of difference (tolerance 100). Should be "
          ++ show logCoef ++ " but term is:\n" ++ show t
          ++ "\n\n with actual counts \n\n" ++ show counts
          ++ "\n\n in trie \n\n" ++ Trie.showTrie ctxs

      -- TODO: check num? (against what?)

      | otherwise = go counts rest . checkTerm t
      where
        counts = IM.union acc m
        logCoef = logFactorial total
                  - sum (logFactorial <$> counts)

-----------
-- MODEL --
-----------

type ContextTrie = Trie (Maybe Int, Term) -- Nothing iff root/top Term

-- | A model is a set of contexts (ordered by rev-suffix) with frequency
-- counts that are inherited and otherwise deviate only by each
-- context's own claims to certain counts of certain symbols
data Model m = Model {
  _modelRules    :: !(Rules m), -- inv construction rules
  _modelCtxKeys  :: !(BoxedVec m ByteString), -- rev-extensions
  _modelContexts :: !ContextTrie -- suffix trie :: revExt -> (s, Term)
}
makeLenses ''Model

-- | Construct a 0-gram model from the counts of the symbols in the
-- data, which corresponds to a single term for the distribution in
-- the empty context
singleton :: PrimMonad m => IntMap Int -> m (Model m)
singleton im = do
  rs <- R.new
  cks <- DMV.fromList $ BS.singleton <$> [0..255]

  let -- fold construct all terms from a root prior
      fromRoot :: Term -> Int -> (Term, (ByteString, (Maybe Int, Term)))
      fromRoot t s = (BS.singleton $ toEnum s,) . (Just s,)
              <$> emptyFromParent s t
      (root, ts) = L.mapAccumL fromRoot (rootTerm im) $ IM.keys im

      ctxs = assert (root^.termWeight.weightNum == 1 || IM.null im)
             Trie.fromList $ (BS.empty, (Nothing, root)) : ts

  return $ Model rs cks ctxs

-- | Sum up the terms, giving the information content (nats) of the
-- whole string w.r.t. the model
information :: Model m -> Double
information = sumOf $ modelContexts . folded . _2 . termRes

revExtension :: PrimMonad m => Model m -> Int -> Stream (Of Word8) m ()
revExtension = effect . fmap (S.each . BS.unpack) .: ctxKey

ctxKey :: PrimMonad m => Model m -> Int -> m ByteString
ctxKey (Model _ ctxKeys _) = DMV.read ctxKeys

----------------------
-- PATTERN MATCHING --
----------------------

-- | Try to match the construction of a symbol s1 at the end of a list
-- of symbols given in reverse order. The patterns that resolve to a
-- Just are [s1,..], [s1B,s1A,..], [s1B,s1AB,s1AA,..],
-- [s1B,s1AB,s1AAB,s1AAA,..], and so on, where (sA,sB) are the
-- components of a joint symbol s. Returns matched pattern in reverse
-- (back to normal orientation) (fst) and remainder of the list (snd).
cMatchRev :: PrimMonad m => Model m -> Int -> [Int] -> m (Maybe ([Int], [Int]))
cMatchRev (Model rs _ _) = flip go []
  where
    go _ _ [] = return Nothing
    go s1 cPref1 (s:rest)
      | s1 == s = return $ Just (s1:cPref1, rest)
      | otherwise = do
          R.invLookup s1 rs >>= 
            \case Just (sA,sB) | sB == s -> go sA (sB:cPref1) rest
                  _else -> return Nothing

-- | Try to match the extension of a symbol s0 at the end of a list of
-- symbols given in reverse order. This is just string comparison
-- between the extensions of the given symbols. Return the remaining
-- rev-extension of the rev-list of symbols if the match is successful.
eMatchRev :: PrimMonad m => Model m -> Int -> [Int] -> m (Maybe (Stream (Of Word8) m ()))
eMatchRev mdl@(Model _ ctxKeys _) s0 str = do
  bs <- DMV.read ctxKeys s0
  ffmap snd $ -- m, Maybe
    S.eq (S.each $ BS.unpack bs) $
    S.splitAt (BS.length bs) $
    S.mapM_ (revExtension mdl) $
    S.each str

cResolveFwd :: PrimMonad m => Model m -> [Int] -> m [Int]
cResolveFwd = undefined -- FIXME: TODO

-- | Given a model and a stream of atoms, return all the symbols (atomic
-- or constructed) whose reversed extension matches the head of the
-- stream
eResolveBwd :: PrimMonad m => Model m -> Stream (Of Word8) m r -> m [Int]
eResolveBwd = fmap (mapMaybe fst) .: resolveCtx -- discard Terms and root

-- | Given a reverse stream of previous atoms, return the terms
-- associated with this context, from root to largest construction. You
-- probably want to reverse this list because claims down the list
-- supersede earlier claims.
resolveCtx :: PrimMonad m =>
              Model m -> Stream (Of Word8) m r -> m [(Maybe Int, Term)]
resolveCtx = fmap snd3 .: Trie.resolveGeneric BS.empty . _modelContexts

---------------
-- INSERTION --
---------------

-- | Given a pair of symbols and the number of times the prefixes (from
-- large to small, from itself to its first atom) appear
insert :: PrimMonad m => (Int,Int) -> IntMap Int -> Model m ->
          m (Double, Int, Model m)
insert (s0,s1) im mdl@(Model rs ctxKeys ctxTrie) = do
  ctx0 <- ctxKey mdl s0 -- rev-extension of s3

  -- 1) remove counts from e-suffixes of s0 to c-prefixes of s1 -----------
  let (cPref1s, introCounts) = unzip $ IM.toDescList im -- big to small

      -- tasks
      subInter :: [ContextTrie -> (Double, ContextTrie)]
      subInter = zipWith (subCount ctx0) cPref1s introCounts

  -- 2) remove counts within s1 (e-suffixes of s0+{c-prefix of s1}) -------
  intraCtxs <- forM cPref1s $ \s ->
    R.invLookup s rs >>=
    \case Nothing -> return (ctx0, s)
          Just (sA,sB) -> (,sB) . (ctx0 <>) <$> ctxKey mdl sA

  let cumCounts = init $ scanr (+) 0 introCounts

      -- tasks
      subIntra :: [ContextTrie -> (Double, ContextTrie)]
      subIntra = zipWith (uncurry subCount) intraCtxs cumCounts

  -- 3) add the n01 s0-s1's -----------------------------------------------
      n01 = assertId (== sum introCounts) $ head cumCounts

      -- task
      addInter :: ContextTrie -> (Double, ContextTrie)
      addInter = adjustCount ctx0 s1 $ ($ n01) . assert . (== 0)

  -- 4) make term for s01 (as a context) ----------------------------------
  (s01,rs') <- R.push (s0,s1) rs
  ctx1 <- ctxKey mdl s1
  let ctx01 = ctx1 <> ctx0 -- flip bc rev-extension
  ctxKeys' <- assert (DMV.length ctxKeys == s01)
              DMV.push ctxKeys ctx01

  let (parentKey, (pS, parentTerm), _) = fromJust $ Trie.match ctxTrie ctx01
      (parentTerm', t01) = emptyFromParent n01 parentTerm

      -- task
      addTerm :: ContextTrie -> (Double, ContextTrie)
      addTerm = (0.0,) . Trie.insert ctx01 (Just s01, t01)
                . Trie.insert parentKey (pS, parentTerm')

  -- All together:
      (ctxTrie', deltas) = L.mapAccumR (swap .: (&)) ctxTrie $
                           addTerm : addInter : subIntra ++ subInter

  return (sum deltas, -- loss
          s01, -- new symbol
          Model rs' ctxKeys' ctxTrie') -- updated model
  where
    -- | Given a context as a ByteString, a symbol predicted and a
    -- count, lookup the term claiming that symbol and subtract the
    -- count, updating the value of affected terms. TODO: return loss
    subCount :: ByteString -> Int -> Int -> ContextTrie -> (Double, ContextTrie)
    subCount _   _ 0 = (0.0,) -- short circuit 0s
    subCount ctx s n = case L.find (flip claims s . snd . snd) $ eSuffixes ctx of
      Nothing -> err $ "Diagram.Model.insert.subCount: "
                       ++ "Can't find symbol " ++ show s
                       ++ " in context lineage: " ++ show (eSuffixes ctx)
      Just (claimant, _) -> adjustCount claimant s (+(-n))
                   

    -- | Lookup the context trie with a maximal context, returning the
    -- matching terms from most specific (exact match if there) to most
    -- general (root)
    eSuffixes :: ByteString -> [(ByteString, (Maybe Int, Term))]
    eSuffixes = fmap (fst3 &&& snd3) . reverse . Trie.matches ctxTrie


-- | Modify the count of a symbol in a context given as a bytestring key
-- (rev-extension of the context symbol). This changes the claim for the
-- symbol in the context (assumes a claim is there) and propagates
-- implications for inheriting terms
adjustCount :: ByteString -> Int -> (Int -> Int) ->
               ContextTrie -> (Double, ContextTrie)
adjustCount k s f ctxs = (getSum delta, ctxs')
  where
    -- split subtrie from trie
    subtrie = Trie.submap k ctxs
    rest = Trie.deleteSubmap k ctxs

    -- change the coef in the root
    (mOldCount1, subtrie') = flip Trie.mapRootF subtrie $
      \t -> t & _2.termCoef.coefClaims
            %%~ IM.updateLookupWithKey (const $ nothingIf (== 0) . f) s
    oldCount1 = fromMaybe 0 mOldCount1
    newCount1 = f oldCount1

    -- propagate change in children
    updateInherited :: (Maybe Int, Term) -> Maybe (Sum Double, (Maybe Int, Term))
    updateInherited (ms,t)
      | s `IM.member` (t^.termCoef.coefClaims) = Nothing
      | otherwise = let (dlt,t') = substCoefFactor oldCount1 newCount1 t
                    in Just (Sum dlt, (ms,t'))

    (delta, subtrie'') = Trie.mapAccumWhile updateInherited subtrie'

    -- merge subtrie back into trie
    ctxs' = flip2 Trie.mergeBy rest subtrie'' $
            err "adjustCount: Conflicting tries"

-- | Update the coefficient of a term where a symbol had `oldCount` to
-- one where it is `newCount`. Does not affect term claims, so works on
-- inherited counts and doesn't require symbol's key.
substCoefFactor :: Int -> Int -> Term -> (Double, Term)
substCoefFactor oldCount newCount t@(Term (Weight num denom _)
                                      (Coef total m lc) val)
  | oldCount == newCount = (0.0, t) -- shortcurcuit id's
  | otherwise = (delta, Term newWeight (Coef total' m lc') val')
  where
    countDelta = newCount - oldCount
    denom' = denom + countDelta
    newWeight@(Weight _ _ w') = weightFromRatio num denom'

    total' = assert (denom == total)
             assert (denom' >= 0) denom'

    countCoefDelta = logFactorial oldCount - logFactorial newCount
    totalCoefDelta = -logFactorial total + logFactorial total'
    lc' = lc + totalCoefDelta + countCoefDelta

    val' = w' * lc'
    delta = val' - val
