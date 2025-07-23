module Diagram.Variety (module Diagram.Variety) where

import Control.Monad.ST
import Control.Monad

import Data.STRef
import Data.Word
import Data.Bifunctor
import qualified Data.List as L
import qualified Data.IntMap.Strict as IM

import qualified Data.Vector.Unboxed as U
import qualified Data.Vector.Generic as V
import qualified Data.Vector.Generic.Mutable as MV

import qualified Codec.Elias as Elias
import qualified Codec.Arithmetic.Combinatorics as Comb
import qualified Codec.Arithmetic.Variety as Var
import Codec.Arithmetic.Variety.BitVec (BitVec)

import Diagram.Rules (Rules)
import qualified Diagram.Rules as R

data Model = Model {
  modelRules :: !Rules,
  modelTotalCount :: !Int,
  modelCounts :: !(U.Vector Int)
}

-- | Initial construction from string of atoms
fromAtoms :: [Word8] -> Model
fromAtoms as = runST $ do
  nref <- newSTRef 0
  mutns <- MV.replicate 256 0
  forM_ as $ \a -> do
    modifySTRef' nref (+1)
    MV.modify mutns (+1) $ fromIntegral a
  n <- readSTRef nref
  ks <- V.unsafeFreeze mutns
  return $ Model R.empty n ks

-- | Reconstruction from rule set and symbol string
fromSymbols :: Rules -> [Int] -> Model
fromSymbols rs ss = Model rs n ks
  where
    im = L.foldl' (\m k -> IM.insertWith (+) k 1 m) IM.empty ss
    n = sum im
    ks = V.replicate (R.numSymbols rs) 0
         V.// IM.toList im -- write

-- | Serialize a rule set and symbol string
encode :: Rules -> [Int] -> BitVec
encode rs ss = rsCode <> nCode <> ksCode <> ssCode
  where
    rsCode = R.encode rs
    (sks, (ssRank,ssBase)) = Comb.rankMultisetPermutation ss
    ((n,_),(ksRank,ksBase)) = Comb.rankDistribution (snd <$> sks)
    nCode = Elias.encodeDelta $ fromIntegral n
    ksCode = Var.encode1 ksRank ksBase
    ssCode = Var.encode1 ssRank ssBase

-- | Deserialize a model+symbol string
decode :: BitVec -> Maybe (Model, [Int], BitVec)
decode bv = do
  (rs, bv') <- R.decode bv
  (n , bv'') <- first fromInteger <$> Elias.decodeDelta bv'
  let numSymbols = R.numSymbols rs
  (ks, bv''') <- Comb.decodeDistribution (n,numSymbols) bv''
  let model = Model rs n (V.fromList ks)
  (ss, bv'''') <- Comb.decodeMultisetPermutation (zip [0..] ks) bv'''
  Just (model, ss, bv'''')
