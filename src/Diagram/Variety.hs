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

-- Here is how we represent a string of overlapping predictions as
-- combinatorial objects w.r.t. the counts of each prediction (and the
-- rule set ofc). Each symbol gets a transition vector that is an
-- instance of a multiset permutation of each symbol that can be
-- constructed from that symbol in the left/first position (as `Just
-- s01` where self is the`s0`), plus one type of element for head
-- termination (`Nothing`), plus we have a "root" transition vector
-- containing only atomic symbols for head starts that is an instance of
-- a multiset permutations of counts of symbols [0..255]. The first
-- prediction/symbol of the string of predictions is the first entry of
-- the root transition vector. To produce each following prediction, the
-- transition table of the context symbol (the previous symbol) is
-- checked; if `Just p` then `p` is produced; else if `Nothing` then the
-- transition table of the secondary context symbol is checked, if there
-- is one, else the root table is consulted, if the secondary context
-- symbol's table also has `Nothing` as the next transition, root table
-- is consulted.

-- | Count for each symbol.
type Counts = U.Vector Int

data Model = Model
  -- minimal parametrization --
  !Rules -- ^ rs :: construction rules
  !(U.Vector Int) -- ^ ks :: symbol construction counts

  -- combinatorial bookkeeping --
  !Int -- ^ n0 :: head count (total of the root coef)
  !(U.Vector Int) -- ^ ns :: ctx state count (total of the coef)
  !(U.Vector Int) -- ^ nc :: non-constructive ctxs (n - sum ks)
  !(B.Vector [Int]) -- ^ af :: "as-first" (ixs of the ks)

fromCounts :: Rules -> U.Vector Int -> Model
fromCounts rs ks = Model rs ks n0 ns nc af
  where
    len = R.numSymbols rs
    n0 = V.sum $ V.take 256 ks
    af = R.asFsts rs

    (ns,nc) = runST $ do
      mnsv <- V.thaw ks -- start with k states (primary ctx)
      mncv <- V.unsafeThaw $ V.replicate len 0

      -- iterate in reverse, adding nc's to snd's state count (n)
      forM_ [len-1,len-2..0] $ \s -> do
        n <- MV.read mnsv s -- sum of primary and secondary ctx
        let constrs = sum ((ks V.!) <$> (af V.! s)) -- sum ks
            nonconstrs = n - constrs
        MV.write mncv s nonconstrs -- write nc
        forM_ (rs R.!? s) $ \(_,sB) ->
          MV.modify mnsv (+nonconstrs) sB -- add secondaries to sB
      nsv <- V.unsafeFreeze mnsv
      ncv <- V.unsafeFreeze mncv
      return (nsv,ncv)

numSymbols :: Model -> Int
numSymbols (Model rs _ _ _ _ _) = R.numSymbols rs

rootDistr :: Model -> (Int, [(Int, Int)])
rootDistr (Model _ ks n0 _ _ _) = (n0, sks)
  where sks = filter ((>0) . snd) $
              zip [0..] $ V.toList $ V.take 256 ks

distr :: Model -> Int -> (Int, [(Maybe Int, Int)])
distr (Model _ ks _ ns nc af) s = (n, sks)
  where
    n = ns V.! s
    saf = af V.! s
    sks = filter ((>0) . snd) $
          (Nothing, nc V.! s) :
          zip (Just <$> saf) ((ks V.!) <$> saf)

compositeDistrs :: Model -> [(Int, [(Maybe Int,Int)])]
compositeDistrs mdl = distr mdl <$>
                      [256..numSymbols mdl - 1]

multinomial :: (Int,[(s,Int)]) -> Integer
multinomial (n,ks) = factorial n
                     `div` product (factorial . snd <$> ks)

variety :: Model -> Integer
variety mdl = product $ multinomial (rootDistr mdl) :
              (multinomial <$> compositeDistrs mdl)

-- | Return a map containing multiples of -n for predictions that are
-- supplanted by the introduction of the candidate and +n for the
-- candidate
deltaCounts :: Rules -> Candidate -> IntMap Int
deltaCounts rs c@(Candidate (_,s1) pp m) = case C.ppType rs c of
  Atomic -> L.foldl' (flip dockM) im0 $
            takeUntil (== pp) $ R.prefixes rs s1

  S1IsSnd -> dockM pp im0

  _else  -> dockM pp $
            L.foldl' (flip dockM) im0 $
            takeUntil (== snd (rs R.! pp)) $ R.prefixes rs s1
  where
    s01 = R.numSymbols rs
    im0 = IM.singleton s01 m -- n times s01 regardless of shape
    dockM s = IM.insertWith (+) s (-m)

insert :: Model -> Candidate -> (Int, Model)
insert (Model rs ks n0 ns nc af) c = ( s01
                                     , Model rs' ks' n0' ns' nc' af' )
  where
    Candidate (s0,s1) _ k = c
    (s01, rs') = R.push (s0,s1) rs
    af' = af V.// [(s0, s01:(af V.! s0))] -- cons s01 at s0

    deltas = IM.toAscList $ deltaCounts rs c
    (ks', n0', ns', nc') = runST $ do
      mksv <- V.unsafeThaw $ V.snoc ks k
      n0ref <- newSTRef n0
      mnsv <- V.unsafeThaw $ V.snoc ns k
      mncv <- V.unsafeThaw $ V.snoc nc 0 -- n - sum ks

      forM_ deltas $ \(s,delta) -> do
        MV.modify mksv (+delta) s

        -- FIXME --
        MV.modify mncv (+delta) s

        case rs R.!? s of
          Nothing -> modifySTRef n0ref (+delta)
          Just (sA,_) -> MV.modify mncv (+(-delta)) sA

      ksv <- V.unsafeFreeze mksv
      n0res <- readSTRef n0ref
      nsv <- V.unsafeFreeze mnsv
      ncv <- V.unsafeFreeze mncv
      return (ksv, n0res, nsv, ncv)


-- | Equivalent to deltaCodeLen in variety space, the factor to multiply
-- the old variety to get the new variety after adding this candidate
ratioVariety :: Model -> Candidate -> Ratio Integer
ratioVariety (Model rs ks n0 ns nc af) c =
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
    vals = snd . Comb.rankMultisetPermutation <$> msps

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
decode :: Model -> BitVec -> [Int]
decode mdl@(Model rs _ _ _ _ _) bv = msps2str rs rmsp msps
  where
    rbase = multinomial rms
    bases = multinomial <$> mss

    vals = Var.decode (rbase:bases) bv

    rms = rootDistr mdl
    mss = compositeDistrs mdl

    rmsp = Comb.unrankMultisetPermutation (snd rms) $ head vals
    msps = zipWith Comb.unrankMultisetPermutation (snd <$> mss) $ tail vals

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
