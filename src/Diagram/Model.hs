{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE LambdaCase, TupleSections #-}
{-# LANGUAGE RankNTypes, ScopedTypeVariables #-}
module Diagram.Model (module Diagram.Model) where

import Control.Lens
import Control.Exception (assert)
import Control.Monad.ST
import Control.Monad

import Data.STRef
import Data.Maybe
import qualified Data.List as L
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IM

import Numeric.SpecFunctions (logFactorial)
import Numeric.MathFunctions.Comparison (within, ulpDistance)

import qualified Data.Vector as B
import qualified Data.Vector.Generic as V
import qualified Data.Vector.Generic.Mutable as MV

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
fromCounts :: IntMap Int -> Term
fromCounts counts | total > 0 = Term weight coef $ coef^.coefLog
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

-----------
-- MODEL --
-----------

type Model = ModelT Term (B.Vector Term) -- immutable
type MModel s = ModelT (STRef s Term) (B.MVector s Term) -- mutable

-- | A model is a set of contexts (ordered by rev-suffix) with frequency
-- counts that are inherited and otherwise deviate only by each
-- context's own claims to certain counts of certain symbols
data ModelT r v = Model {
  _constrRules :: !Rules, -- symbols of the model
  _rootTerm    :: !r,     -- term of the empty construction
  _symbolTerms :: !v      -- term for each symbol
} deriving (Show)
makeLenses ''ModelT

-- | Construct a 0-gram model from the counts of the symbols in the
-- data, which corresponds to a single term for the distribution in
-- the empty context
singleton :: IntMap Int -> Model
singleton im = assert (root^.termWeight.weightNum == 1 || IM.null im)
               Model R.empty root $ B.fromList ts
  where
    rootInit = fromCounts im :: Term
    (root, ts) = L.mapAccumL (flip emptyFromParent) rootInit $ IM.keys im

-- | Sum up the terms, giving the information content (nats) of the
-- whole string w.r.t. the model
information :: Model -> Double
information (Model _ t0 ts) = t0^.termRes + sumOf (folded.termRes) ts

checkTerms :: Model -> a -> a
checkTerms mdl@(Model rs t0 ts) = foldr ((.) . checkLineageOf) id [0..R.numSymbols rs]
  where
    checkLineageOf :: Int -> a -> a
    checkLineageOf s = -- check lineage starting w/ root
      let lineage = (t0:) $ reverse $ (ts V.!) <$> R.suffixes rs s
      in go IM.empty lineage

    go _ [] = id
    go acc (t@(Term _ (Coef total m lc) _):rest)
      | sum counts /= total =
          err $ "Inherited counts don't sum to stored total "
          ++ show (sum counts, total) ++ ": " ++ show t
          ++ "\n\n in model \n\n" ++ show mdl

      | not $ within 100 lc logCoef =
          err $ "Computed log-Coef is not equal to stored value ("
          ++ show (ulpDistance lc logCoef)
          ++ " ULPs of difference (tolerance 100). Should be "
          ++ show logCoef ++ " but term is:\n" ++ show t
          ++ "\n\n with actual counts \n\n" ++ show counts
          ++ "\n\n in model \n\n" ++ show mdl

      -- TODO: check num? (against what?)

      | otherwise = go counts rest . checkTerm t
      where
        counts = IM.union acc m
        logCoef = logFactorial total
                  - sum (logFactorial <$> counts)

---------------
-- INSERTION --
---------------

-- | Given a pair of symbols and the number of times the prefixes (from
-- large to small, from itself to its first atom) appear
insert :: Model -> (Int,Int) -> Int -> (Maybe Int, Int) -> (Double, Int, Model)
insert (Model rs root terms) (s0,s1) n (suf0,pre1) = runST $ do

  -- thaw model
  mutTerms <- B.thaw terms
  mutRoot <- newSTRef root
  let adjust = adjustCount $ Model rs mutRoot mutTerms

  -- 0) remove n edges from suf0 to pre1
  d0 <- adjust suf0 pre1 (+(-n))

  -- 1) remove edges from pre1 (exclusive) to s1 (inclusive)
  let cPref1s = tail $ L.dropWhile (/= pre1) $ -- excluding pre1
                reverse $ R.prefixes rs s1 -- from small to big

  d1s <- forM cPref1s $ \cPref1 ->
    case R.invLookup rs cPref1 of
      Nothing -> return 0.0
      Just (cPref1A, cPref1B) -> adjust (Just cPref1A) cPref1B (+(-n))

  -- 2) add the n01 s0-s1's
  d2 <- adjust (Just s0) s1 (\oldCount -> assert (oldCount == 0) n)

  -- make term for s01 (no impact on loss, keep lazy)
  let (s01,rs') = R.push (s0,s1) rs
  t1 <- MV.read mutTerms s1
  let (t1', t01) = emptyFromParent n t1
  MV.write mutTerms s1 t1'

  -- freeze
  terms' <- V.freeze mutTerms
  root' <- readSTRef mutRoot

  return ( d0 + sum d1s + d2
         , assert (s01 == V.length terms') s01
         , Model rs' root' $ V.snoc terms' t01 )

-- | Modify the count of a symbol in a context given as a bytestring key
-- (rev-extension of the context symbol). This changes the claim for the
-- symbol in the context (assumes a claim is there) and propagates
-- implications for inheriting terms
adjustCount :: MModel s -> Maybe Int -> Int -> (Int -> Int) -> ST s Double
adjustCount (Model rs root ts) s0 s1 f = do
  -- read root of the affected subtrie
  t0 <- maybe (readSTRef root) (MV.read ts) s0
  let (mOldCount1, t0') = t0 & termCoef.coefClaims
        %%~ IM.updateLookupWithKey (\_ -> nothingIf (== 0) . f) s1
      oldCount1 = fromMaybe 0 mOldCount1
      newCount1 = f oldCount1
      substRes = substCoefFactor oldCount1 newCount1

      sc0s = maybe [0..255] (R.withAsSnd rs) s0
      (d0, t0'') = substRes t0'

  -- write root
  maybe (writeSTRef root t0'') (flip (MV.write ts) t0'') s0

  -- rec worker
  let go s = do
        t <- MV.read ts s
        if s1 `IM.member` (t^.termCoef.coefClaims)
          then return 0.0
          else do let (d,t') = substRes t
                  MV.write ts s t'
                  ds <- forM (R.withAsSnd rs s) go -- rec
                  return $ sum (d:ds)

  ds <- forM sc0s go -- propagate
  return $ sum (d0:ds)

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
