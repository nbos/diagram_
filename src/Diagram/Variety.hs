module Diagram.Variety (module Diagram.Variety) where

import Control.Monad.ST
import Control.Monad

import Data.STRef
import qualified Data.Vector.Unboxed as U
import qualified Data.Vector.Generic as V
import qualified Data.Vector.Mutable as MV

import Streaming hiding (first)
import qualified Streaming.Prelude as S

import qualified Codec.Arithmetic.Combinatorics as Comb
import qualified Codec.Arithmetic.Variety as Var
import Codec.Arithmetic.Variety.BitVec (BitVec)

import Diagram.Rules (Rules,AsFsts)
import qualified Diagram.Rules as R
import Diagram.Util

-- | Count for each symbol.
type Counts = U.Vector Int

data Model = Model {
  symbolRules :: !Rules,
  symbolCounts :: !(U.Vector Int),
  symbolConstrs :: !AsFsts
}

numSymbols :: Model -> Int
numSymbols (Model rs _ _) = R.numSymbols rs

rootDistr :: Model -> [(Int,Int)]
rootDistr (Model _ ns _) = zip [0..] $ V.toList $ V.take 256 ns

distr :: Model -> Int -> [(Maybe Int,Int)]
distr (Model _ ns af) s = (Nothing, k'):
                          zip (Just <$> saf) ks
  where
    n = ns V.! s
    saf = af V.! s
    ks = (ns V.!) <$> saf
    k' = n - sum ks

compositeDistrs :: Model -> [[(Maybe Int,Int)]]
compositeDistrs mdl = distr mdl <$>
                      [256..numSymbols mdl - 1]

variety :: Model -> Integer
variety mdl = sum $ Comb.multinomial . filter (>0) <$> distrs
  where distrs = fmap snd (rootDistr mdl) :
                 ffmap snd (compositeDistrs mdl)

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
  msps <- fmap reverse . V.toList <$> V.unsafeFreeze mv
  return (rmsp, msps)

-- | Decode a list of predictions
decode :: Model -> BitVec -> [Int]
decode mdl@(Model rs _ _) bv = msps2str rs rmsp msps
  where
    rbase = Comb.multinomial $ snd <$> rms
    bases = Comb.multinomial . fmap snd <$> mss

    vals = Var.decode (rbase:bases) bv

    rms = filter ((>0) . snd) $ rootDistr mdl
    mss = filter ((>0) . snd) <$> compositeDistrs mdl

    rmsp = Comb.unrankMultisetPermutation rms $ head vals
    msps = zipWith Comb.unrankMultisetPermutation mss $ tail vals

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
