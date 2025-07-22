{-# LANGUAGE TupleSections #-}
module Diagram.Variety (module Diagram.Variety) where

import Control.Monad.ST
import Control.Monad

import Data.STRef
import Data.Ratio
import qualified Data.List as L
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Strict as M

import qualified Data.Vector as B
import qualified Data.Vector.Unboxed as U
import qualified Data.Vector.Generic as V
import qualified Data.Vector.Generic.Mutable as MV

import Streaming hiding (first)
import qualified Streaming.Prelude as S

import Math.Combinatorics.Exact.Factorial (factorial)
import qualified Codec.Arithmetic.Combinatorics as Comb
import qualified Codec.Arithmetic.Variety as Var
import Codec.Arithmetic.Variety.BitVec (BitVec)

import Diagram.Rules (Rules)
import qualified Diagram.Rules as R
import Diagram.Candidates (Candidate(..),PPType(..))
import qualified Diagram.Candidates as C
import Diagram.Util

data Model = Model
  -- parameters --
  !Rules -- ^ rs :: construction rules
  !(U.Vector Int) -- ^ ks :: symbol construction counts
  !(U.Vector Int) -- ^ kCs :: symbol complementary counts (n - k)

  -- cached values --
  !Int -- ^ n0 :: V.sum $ V.take 256 ks
  !(U.Vector Int) -- ^ nc :: non-constructive ctxs (n - sum ks)
  !(B.Vector [Int]) -- ^ af :: symbols where i appears as first
  !(B.Vector [Int]) -- ^ as :: symbols where i appears as second

-- | Construction
fromParams :: Rules -> U.Vector Int -> U.Vector Int -> Model
fromParams rs ks kCs = Model rs ks kCs n0 nc af as
  where
    len = R.numSymbols rs
    n0 = V.sum $ V.take 256 ks
    nc = V.generate len $ \s ->
      let n = (ks V.! s) + (kCs V.! s)
      in n - sum ((ks V.!) <$> (af V.! s))
    af = R.asFsts rs
    as = R.asSnds rs

numSymbols :: Model -> Int
numSymbols (Model rs _ _ _ _ _ _) = R.numSymbols rs

-----------------
-- CATEGORICAL --
-----------------

type Categorical a = ( Int -- total count
                     , [(a, Int)] ) -- bins (must sum to total)

rootDistr :: Model -> Categorical Int
rootDistr (Model _ ks _ n0 _ _ _) = (n0, sks)
  where sks = filter ((>0) . snd) $
              zip [0..] $ V.toList $ V.take 256 ks

distr :: Model -> Int -> Categorical (Maybe Int)
distr (Model _ ks kCs _ nc af _) s = (n, sks)
  where
    n = (ks V.! s) + (kCs V.! s) -- n = k + kC
    saf = af V.! s
    sks = filter ((>0) . snd) $
          (Nothing, nc V.! s) :
          zip (Just <$> saf) ((ks V.!) <$> saf)

compositeDistrs :: Model -> [Categorical (Maybe Int)]
compositeDistrs mdl = distr mdl <$>
                      [256..numSymbols mdl - 1]

-- | Compute the multinomial coefficient with parameters matching those
-- of the given categorical distirbution, i.e. the variety of the
-- given distribution
multinomial :: Categorical a -> Integer
multinomial (n,ks) = factorial n
                     `div` product (factorial . snd <$> ks)

----------------
-- CANDIDATES --
----------------

-- | Return a map containing multiples of -n for predictions that are
-- supplanted by the introduction of the candidate and +n for the
-- candidate
deltaCounts :: Rules -> Candidate -> IntMap Int
deltaCounts rs c@(Candidate (_,s1) pp n) = case C.ppType rs c of
  Atomic -> L.foldl' (flip dockM) im0 $
            takeUntil (== pp) $ R.prefixes rs s1
  S1IsSnd -> dockM pp im0
  _else  -> dockM pp $
            L.foldl' (flip dockM) im0 $
            takeUntil (== snd (rs R.! pp)) $ R.prefixes rs s1
  where
    s01 = R.numSymbols rs
    im0 = IM.singleton s01 n -- n times s01 regardless of shape
    dockM s = IM.insertWith (+) s (-n)

insert :: Model -> Candidate -> (Int, Model)
insert (Model rs ks kCs n0 nc af as) c = runST $ do
  mutks <- V.unsafeThaw $ V.snoc ks k
  mutkCs <- V.unsafeThaw $ V.snoc kCs k
  n0ref <- newSTRef n0
  mutnc <- V.unsafeThaw $ V.snoc nc 0 -- n - sum ks

  forM_ deltas $ \(s,delta) -> do
    MV.modify mutks (+delta) s
    MV.modify mutnc (+delta) s
    case rs R.!? s of
      Nothing -> modifySTRef n0ref (+delta)
      Just (sA,sB) -> do
        -- FIXME --
        MV.modify mutnc (+(-delta)) sA

  ks' <- V.unsafeFreeze mutks
  kCs' <- V.unsafeFreeze mutkCs
  n0' <- readSTRef n0ref
  nc' <- V.unsafeFreeze mutnc

  return (s01, Model rs' ks' kCs' n0' nc' af' as')

  where
    Candidate (s0,s1) _ k = c
    (s01, rs') = R.push (s0,s1) rs
    af' = af V.// [(s0, s01:(af V.! s0))] -- cons s01 at s0
    as' = as V.// [(s1, s01:(as V.! s1))] -- cons s01 at s1
    deltas = IM.toAscList $ deltaCounts rs c

-- | Equivalent to deltaCodeLen in variety space, the factor to multiply
-- the old variety to get the new variety after adding this candidate
ratioVariety :: Model -> Candidate -> Ratio Integer
ratioVariety (Model rs ks kCs n0 nc af as) c =
  let m = L.foldl' (flip id) M.empty $
          (<$> IM.toList (deltaCounts rs c)) $ \(s, delta) ->
        minsert (Just s) (M.singleton Nothing delta)
        . minsert (fst <$> (rs R.!? s)) (M.singleton (Just s) delta)

  ----------------- FIXME ----------------------

  in product $ (<$> M.toList m) $ \(ctx, ds) ->
    let n = maybe n0 (ks V.!) ctx -- n0 is the n for the Nothing ctx
        (as,bs) = unzip $ (<$> M.toList ds) $ \(mp, d) -> case mp of
          Nothing -> let
            in undefined

          Just p -> let k = ks V.! p
                    in (k, k+d) -- (old k, new k)
        dn = sum bs - sum as
        n' = n0 + dn
        num = product $ factorial <$> (n':as)
        denom = product $ factorial <$> (n:bs)
    in num % denom
  where
    minsert = M.insertWith $ M.unionWith (+)
    Candidate (s0,s1) pp _ = c

-------------------
-- SERIALIZATION --
-------------------

-- | Encode a list of predictions
encode :: Rules -> [Int] -> BitVec
encode rs ps = Var.encode $ rval:vals
  where
    (rmsp,msps) = str2msps rs ps
    (_,rval) = Comb.rankMultisetPermutation rmsp
    (_,vals) = unzip $ Comb.rankMultisetPermutation <$> msps

-- | Represent a string of predictions (symbols) multiset permutations
-- determining all transitions for each inference state (root
-- transitions at head, then transitions for each symbol 0..). Nothing
-- are non-constructive transitions, while Just are constructions.
str2msps :: Rules -> [Int] -> ([Int],[[Maybe Int]])
str2msps rs [] = ([], replicate (R.numSymbols rs) [])
str2msps rs (p0:ps) = runST $ do
  mroot <- newSTRef []
  mv <- MV.replicate (R.numSymbols rs) []
  let go prev s = case rs R.!? s of
        Nothing -> MV.modify mv (Nothing:) prev
                   >> modifySTRef mroot (s:)
        Just (sA,_)
          | sA == prev -> MV.modify mv (Just s:) prev
          | sA == prevB -> MV.modify mv (Nothing:) prev
                           >> MV.modify mv (Just s:) prevB
          | otherwise -> error "unrecognized pattern"
          where
            (_,prevB) = rs R.! prev

  zipWithM_ go (p0:ps) ps
  rmsp <- reverse <$> readSTRef mroot
  msps <- fmap reverse . B.toList <$> B.unsafeFreeze mv
  return (rmsp, msps)

-- | Decode a list of predictions
decode :: Model -> BitVec -> Maybe ([Int], BitVec)
decode mdl bv = do
  (vals, bv') <- Var.decode (rbase:bases) bv
  let rmsp = Comb.unrankMultisetPermutation (snd rms) $
             head vals
      msps = zipWith Comb.unrankMultisetPermutation (snd <$> mss) $
             tail vals
  Just (msps2str rs rmsp msps, bv')

  where
    Model rs _ _ _ _ _ _ = mdl
    rbase = multinomial rms
    bases = multinomial <$> mss

    rms = rootDistr mdl
    mss = compositeDistrs mdl

-- | Walk the given transition tables back into a string of symbols
msps2str :: Rules -> [Int] -> [[Maybe Int]] -> [Int]
msps2str _ [] _ = []
msps2str rs (s0:rmsp) msps = runST $ do
  mroot <- newSTRef rmsp
  mv <- B.unsafeThaw $ V.fromList msps
  let go prev = do
        -- (prev) --------------------
        next <- lift $ MV.read mv prev
        case next of
          [] -> return ()
          (trans:rest) -> do
            lift $ MV.write mv prev rest
            case trans of
              Just s -> S.yield s >> go s
              Nothing -> do
                let (_,prevB) = rs R.! prev
        -- (snd prev) --------------------------
                next' <- lift $ MV.read mv prevB
                case next' of
                  [] -> return ()
                  (trans':rest') -> do
                    lift $ MV.write mv prevB rest'
                    case trans' of
                      Just s' -> S.yield s' >> go s'
                      Nothing -> do
        -- (root) --------------------------------------
                        next'' <- lift $ readSTRef mroot
                        case next'' of
                          [] -> return ()
                          (s'':rest'') -> do
                            lift $ writeSTRef mroot rest''
                            S.yield s'' >> go s''

  str <- S.toList_ $ go s0
  return $ s0:str
