module Diagram.Model (module Diagram.Model) where

import Control.Monad.ST
import Control.Monad

import Data.STRef
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

import Diagram.Rules (Rules)
import qualified Diagram.Rules as R
import Diagram.Information

-- | A model is a set of symbol defined through construction rules and
-- an integer-multinomial distribution (histogram) of the symbols that
-- can be resolved a given string identifying corresponding multiset
-- permutations
data Model = Model {
  modelRules :: !Rules,
  modelTotalCount :: !Int,
  modelCounts :: !(U.Vector Int)
} deriving Show

------------------
-- CONSTRUCTION --
------------------

empty :: Model
empty = Model R.empty 0 $ U.replicate 256 0

addCounts :: Model -> [Int] -> Model
addCounts (Model rs n ks) ss = runST $ do
  nref <- newSTRef n
  mutks <- V.thaw ks
  forM_ ss $ \s -> do
    modifySTRef' nref (+1)
    MV.modify mutks (+1) s
  n' <- readSTRef nref
  ks' <- V.unsafeFreeze mutks
  return $ Model rs n' ks'

-- | Reconstruction from rule set and symbol string
fromSymbols :: Rules -> [Int] -> Model
fromSymbols rs ss = Model rs n ks
  where
    im = L.foldl' (\m k -> IM.insertWith (+) k 1 m) IM.empty ss
    n = sum im
    ks = V.replicate (R.numSymbols rs) 0
         V.// IM.toList im -- write

pushRule :: Model -> (Int,Int) -> Int -> (Int, Model)
pushRule (Model rs n ks) (s0,s1) n01 = (s01, Model rs' n' ks')
  where
    (s01,rs') = R.pushRule (s0,s1) rs
    n' = n - n01
    ks' = runST $ do
      mutks <- V.unsafeThaw $ V.snoc ks n01
      forM_ [s0,s1] $ MV.modify mutks (+(-n01))
      V.unsafeFreeze mutks

-------------------
-- SERIALIZATION --
-------------------

-- | Serialize a symbol string given a rule set through the
-- serialization of the model of the string and a permutation
encode :: Rules -> [Int] -> BitVec
encode rs ss = rsCode <> nCode <> ksCode <> ssCode
  where
    rsCode = R.encode rs
    (sks, (ssRank,ssBase)) = Comb.rankMultisetPermutation ss
    ((n,_),(ksRank,ksBase)) = Comb.rankDistribution (snd <$> sks)
    nCode = Elias.encodeDelta $ fromIntegral n
    ksCode = Var.encode1 ksRank ksBase
    ssCode = Var.encode1 ssRank ssBase

-- | Deserialize a model+symbol string at the head of a given bit vector
-- that was serialized using @encode@
decode :: BitVec -> Maybe (Model, [Int], BitVec)
decode bv = do
  (rs, bv') <- R.decode bv
  (n , bv'') <- first fromInteger <$> Elias.decodeDelta bv'
  let numSymbols = R.numSymbols rs
  (ks, bv''') <- Comb.decodeDistribution (n,numSymbols) bv''
  let model = Model rs n (V.fromList ks)
  (ss, bv'''') <- Comb.decodeMultisetPermutation (zip [0..] ks) bv'''
  Just (model, ss, bv'''')

--------------------------
-- INFORMATION MEASURES --
--------------------------

-- | Compute the information, in bits, of a distribution of `n` elements
-- into `k` bins through the stars-and-bars angle
distrInfo :: Int -> Int -> Double
distrInfo _ 0 = 0.0
distrInfo n k = log2e * ( logFactorial (stars + bars)
                          - logFactorial stars
                          - logFactorial bars )
  where stars = n
        bars = k - 1

-- | Information in bits of the rank of a multiset permutation resolving
-- a string for the given model
stringInfo :: Model -> Double
stringInfo (Model _ n ks)
  | n <= 1 = 0
  | otherwise = log2e * (logFactorial n - V.sum (V.map logFactorial ks))

stringInfoDelta :: Int -> ((Int,Int),(Int,Int)) -> Int -> Double
stringInfoDelta n ((s0,k0),(s1,k1)) k01
  | s0 == s1 = log2e * ( logFactorial n' - logFactorial n
                         - logFactorial (k0 - 2*k01) + logFactorial k0
                         - logFactorial k01 )
  | otherwise = log2e * ( logFactorial n' - logFactorial n
                          - logFactorial (k0 - k01) + logFactorial k0
                          - logFactorial (k1 - k01) + logFactorial k1
                          - logFactorial k01 )
  where n' = n - k01
{-# INLINE stringInfoDelta #-}

-- | Information in bits of the given model + a sampled symbol string
information :: Model -> Double
information mdl@(Model rs n ks) = rsInfo + nInfo + ksInfo + ssInfo
  where
    rsInfo = R.information rs
    nInfo = eliasInfo n
    ksInfo = distrInfo n (V.length ks)
    ssInfo = stringInfo mdl

-- | Compute the change in code length (bits) of the model + symbol
-- string matching it given a new rule introduction
infoDelta :: Model -> (Int,Int) -> Int -> Double
infoDelta (Model rs n ks) (s0,s1) = infoDelta_ rs n ((s0,k0),(s1,k1))
  where
    k0 = ks V.! s0
    k1 = ks V.! s1

-- | `infoDelta` if the model's size `n` was scaled by `scale`
scaledInfoDelta :: Double -> Model -> (Int,Int) -> Int -> Double
scaledInfoDelta scale (Model rs n ks) (s0,s1) k01 =
  infoDelta_ rs sn ((s0,sk0),(s1,sk1)) sk01
  where -- FIXME : when s0 == s1, 2*sk0 is not necessarily <= sk01
    sc = scaleInt scale
    sn   = sc n
    sk01 = sc k01
    sk0  = sc $ ks V.! s0
    sk1  = sc $ ks V.! s1

infoDelta_ :: Rules -> Int -> ((Int,Int),(Int,Int)) -> Int -> Double
infoDelta_ rs n ((s0,k0),(s1,k1)) k01 =
  rsInfoDelta + nInfoDelta + ksInfoDelta + ssInfoDelta
  where
    numSymbols = R.numSymbols rs
    -- rules info delta (constant):
    rsInfoDelta = R.infoDelta rs
    -- n elias encoding:
    n' = n - k01
    nInfoDelta = eliasInfo n' - eliasInfo n
    -- ks a distribution of n elements:
    ksInfoDelta = distrInfo n' (numSymbols + 1) -- new
                  - distrInfo n numSymbols -- old
    -- ss a multiset permutation of counts ks:
    ssInfoDelta = stringInfoDelta n ((s0,k0),(s1,k1)) k01
{-# INLINE infoDelta_ #-}

-- -- | Code length in bits of the serialization of the model
-- modelCodeLen :: Model -> Int
-- modelCodeLen (Model rs n _) = rsCodeLen + nCodeLen
--                               + fromIntegral ksCodeLen
--   where
--     rsCodeLen = R.codeLen rs
--     nCodeLen = BV.length $ Elias.encodeDelta $ fromIntegral n
--     ksCodeLen = Var.codeLen1 $ Comb.countDistributions n $ R.numSymbols rs

-- -- | Code length in bits of the serialization of a symbol string sampled
-- -- from the given model
-- stringCodeLen :: Model -> Int
-- stringCodeLen (Model _ _ ks) = fromIntegral $ Var.codeLen1 $
--                                Comb.multinomial $ V.toList ks

-- -- | Code length in bits of the serialization of the model + a sampled
-- -- symbol string
-- codeLen :: Model -> Int
-- codeLen mdl = modelCodeLen mdl + stringCodeLen mdl

-- -- | `information` if the model's size `n` was scaled by `scale`,
-- -- e.g. the rule set takes the same size, but the symbol distribution
-- -- and permutation scale
-- scaledInformation :: Double -> Model -> Double
-- scaledInformation scale (Model rs n ks) = rsInfo + nInfo + ksInfo + ssInfo
--   where
--     rsInfo = R.information rs
--     sn = scaleInt scale n
--     nInfo = eliasInfo sn
--     ksInfo = distrInfo sn (V.length ks)
--     ssInfo = log2e * ( logFactorial sn
--                        - V.sum ((logFactorial . scaleInt scale) `V.map` ks))
