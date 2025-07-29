module Diagram.Model (module Diagram.Model) where

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

import Numeric.SpecFunctions (logFactorial)

import qualified Codec.Elias as Elias
import qualified Codec.Arithmetic.Combinatorics as Comb
import qualified Codec.Arithmetic.Variety as Var
import Codec.Arithmetic.Variety.BitVec (BitVec)
import qualified Codec.Arithmetic.Variety.BitVec as BV

import Diagram.Rules (Rules)
import qualified Diagram.Rules as R

data Model = Model {
  modelRules :: !Rules,
  modelTotalCount :: !Int,
  modelCounts :: !(U.Vector Int)
} deriving Show

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

push :: Model -> (Int,Int) -> Int -> (Int, Model)
push (Model rs n ks) (s0,s1) n01 = (s01, Model rs' n' ks')
  where
    (s01,rs') = R.push (s0,s1) rs
    n' = n - n01
    ks' = runST $ do
      mutks <- V.unsafeThaw $ V.snoc ks n01
      forM_ [s0,s1] $ MV.modify mutks (+(-n01))
      V.unsafeFreeze mutks

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

-- | Code length in bits of the serialization of the model + a sampled
-- symbol string
codeLen :: Model -> Int
codeLen (Model rs n ks) = rsCodeLen + nCodeLen
                          + fromIntegral ksCodeLen
                          + fromIntegral ssCodeLen
  where
    rsCodeLen = R.codeLen rs
    nCodeLen = BV.length $ Elias.encodeDelta $ fromIntegral n
    ksCodeLen = Var.codeLen1 $ Comb.countDistributions n $ R.numSymbols rs
    ssCodeLen = Var.codeLen1 $ Comb.multinomial $ V.toList ks

-- | logBase 2 e, for [nats] * log2e = [bits]
log2e :: Double
log2e = 1.44269504088896340735992468100189214

eliasInfo :: Int -> Double
eliasInfo = fromIntegral
            . BV.length
            . Elias.encodeDelta
            . fromIntegral

-- | Compute the information, in bits, of a distribution of `n` elements
-- into `k` bins through the stars-and-bars angle
distrInfo :: Int -> Int -> Double
distrInfo _ 0 = 0.0
distrInfo n k = log2e * ( logFactorial (stars + bars)
                          - logFactorial stars
                          - logFactorial bars )
  where stars = n
        bars = k - 1

-- | Information in bits of the given model + a sampled symbol string
information :: Model -> Double
information (Model rs n ks) = rsInfo + nInfo + ksInfo + ssInfo
  where
    rsInfo = R.information rs
    nInfo = eliasInfo n
    ksInfo = distrInfo n (V.length ks)
    ssInfo = log2e * ( logFactorial n
                       - V.sum (logFactorial `V.map` ks))

-- | Compute the change in information of the model + sampled symbol
-- string given a new rule
infoDelta :: Model -> (Int,Int) -> Int -> Double
infoDelta (Model rs n ks) (s0,s1) n01 =
  -- traceShow (R.toString rs [s0,s1]) $
  -- traceShow [rsInfoDelta,nInfoDelta,ksInfoDelta,ssInfoDelta] $
  rsInfoDelta + nInfoDelta + ksInfoDelta + ssInfoDelta
  where
    -- rules info delta (constant)
    rsInfoDelta = R.fwdInfoDelta rs

    -- n elias encoding
    n' = n - n01
    nInfoDelta = eliasInfo n' - eliasInfo n

    -- ks a distribution of n elements
    ksInfoDelta = distrInfo n' (V.length ks + 1) -- new
                  - distrInfo n (V.length ks) -- old

    -- ss a multiset permutation of counts ks
    ssInfoDelta
      | s0 == s1 = log2e * ( logFactorial n' - logFactorial n
                             - logFactorial (n0 - 2*n01) + logFactorial n0
                             - logFactorial n01 )
      | otherwise = log2e * ( logFactorial n' - logFactorial n
                             - logFactorial (n0 - n01) + logFactorial n0
                             - logFactorial (n1 - n01) + logFactorial n1
                             - logFactorial n01 )
    n0 = ks V.! s0
    n1 = ks V.! s1
