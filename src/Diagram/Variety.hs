module Diagram.Variety (module Diagram.Variety) where

import Control.Monad.ST
import Control.Monad

import Data.Maybe
import Data.STRef
import Data.Tuple.Extra
import qualified Data.Vector as B
import qualified Data.Vector.Generic as V
import qualified Data.Vector.Mutable as MV

import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Strict as M

import Streaming hiding (first)
import qualified Streaming.Prelude as S

import qualified Codec.Arithmetic.Combinatorics as Comb
import qualified Codec.Arithmetic.Variety as Var
import Codec.Arithmetic.Variety.BitVec (BitVec)
import qualified Codec.Arithmetic.Variety.BitVec as BV

import Diagram.Rules (Rules)
import qualified Diagram.Rules as R

type Categorical = IntMap Int

-- | The distribution of next states for a given state at inference
-- time.
data Distribution = Distribution {
  selfCount :: !Int,
  constrCounts :: !Categorical
}

-- | Compute the variety of a single distribution
variety1 :: Distribution -> Integer
variety1 (Distribution n ks) = Comb.multinomial $
                               kExit : IM.elems ks
  where kExit = n - sum ks

-- | Multiset represetntation of a Distribution, with the
-- transition/construction as a Maybe Int together with counts
toMultiset :: Distribution -> [(Maybe Int, Int)]
toMultiset (Distribution n ks) = (Nothing, kExit):
                                 (first Just <$> IM.toList ks)
  where kExit = n - sum ks

fromMultiset :: [(Maybe Int, Int)] -> Distribution
fromMultiset counts = Distribution n ks
  where
    m = M.fromList counts
    kExit = fromMaybe 0 $ M.lookup Nothing m
    ks = IM.fromAscList $
         first fromJust <$> M.toAscList (M.delete Nothing m)
    n = kExit + sum ks

-----------
-- MODEL --
-----------

data Distributions = Distributions {
  rootDistr :: !Categorical,
  byLastSym :: !(B.Vector Distribution)
}

variety :: Distributions -> Integer
variety (Distributions root v) = Comb.multinomial (IM.elems root)
                                 + sum (variety1 <$> v)

codeLen :: Distributions -> Int
codeLen = BV.bitLen . variety

-------------------
-- SERIALIZATION --
-------------------

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
  msps <- fmap reverse . V.toList <$> V.unsafeFreeze mv
  return (rmsp, msps)

-- | Encode a list of predictions
encode :: Rules -> [Int] -> BitVec
encode rs ps = Var.encode $ rval:vals
  where
    (rmsp,msps) = str2msps rs ps
    (_,rval) = Comb.rankMultisetPermutation rmsp
    vals = snd . Comb.rankMultisetPermutation <$> msps

-- | Walk the given transition tables back into a string of symbols
msps2str :: Rules -> [Int] -> [[Maybe Int]] -> [Int]
msps2str _ [] _ = []
msps2str rs (s0:rmsp) msps = runST $ do
  mroot <- newSTRef rmsp
  mv <- V.unsafeThaw $ V.fromList msps
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

-- | Decode a list of predictions
decode :: Rules -> Distributions -> BitVec -> [Int]
decode rs (Distributions root v) bv = msps2str rs rmsp msps
  where
    ds = V.toList v
    rbase = Comb.multinomial (IM.elems root)
    bases = variety1 <$> ds

    vals = Var.decode (rbase:bases) bv

    rms = IM.toList root
    mss = toMultiset <$> ds

    rmsp = Comb.unrankMultisetPermutation rms $ head vals
    msps = zipWith Comb.unrankMultisetPermutation mss $ tail vals
