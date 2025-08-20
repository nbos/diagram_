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

import qualified Codec.Elias as Elias
import qualified Codec.Arithmetic.Combinatorics as Comb
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
    numSymbols = R.numSymbols rs
    (sks,ssCode) = Comb.encodeMultisetPermutation ss
    ks = V.toList $ runST $ do -- add bins with zero counts
      mutks <- U.unsafeThaw $ U.replicate numSymbols 0
      forM_ sks $ uncurry $ MV.write mutks
      U.unsafeFreeze mutks
    ((n,_),ksCode) = Comb.encodeDistribution ks
    nCode = Elias.encodeDelta $ fromIntegral n

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

-- MODEL * STRING --

-- | Information in bits of the given model + a sampled symbol string
information :: Model -> Double
information mdl@(Model rs n ks) = rsInfo + nInfo + ksInfo + ssInfo
  where
    rsInfo = R.information rs
    nInfo = eliasInfo n
    ksInfo = distrInfo n (V.length ks)
    ssInfo = stringInfo mdl

-- | Information in bits of the given model + a sampled symbol string if
-- the string the model was fit on `scale` times as big
scaledInformation :: Double -> Model -> Double
scaledInformation scale mdl@(Model rs n ks) =
  rsInfo + nInfo + ksInfo + ssInfo
  where
    sn     = scale * fromIntegral n
    rsInfo = R.information rs
    nInfo  = eliasInfo (round sn)
    ksInfo = fDistrInfo sn (fromIntegral $ V.length ks)
    ssInfo = scaledStringInfo scale mdl

-- Δ

-- | Compute the change in code length (bits) of the model + symbol
-- string matching it given a new rule introduction
infoDelta :: Model -> (Int,Int) -> Int -> Double
infoDelta (Model rs n ks) (s0,s1) k01 =
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

    k0 = ks V.! s0
    k1 = ks V.! s1

-- | Expected `infoDelta` when the model's size `n` is scaled by `scale`
scaledInfoDelta :: Double -> Model -> (Int,Int) -> Int -> Double
scaledInfoDelta scale (Model rs n ks) (s0,s1) k01 =
    rsInfoDelta + nInfoDelta + ksInfoDelta + ssInfoDelta
  where
    sn   = scale * fromIntegral n
    sk01 = scale * fromIntegral k01
    sk0  = scale * fromIntegral (ks V.! s0)
    sk1  = scale * fromIntegral (ks V.! s1)
    sn'  = sn - sk01

    numSymbols = R.numSymbols rs
    fNumSymbols = fromIntegral numSymbols
    -- rules info delta (constant):
    rsInfoDelta = R.infoDelta rs
    -- n elias encoding:
    nInfoDelta = eliasInfo (round sn') - eliasInfo (round sn)
    -- ks a distribution of n elements:
    ksInfoDelta = fDistrInfo sn' (fNumSymbols + 1) -- new
                  - fDistrInfo sn fNumSymbols -- old
    -- ss a multiset permutation of counts ks:
    ssInfoDelta = fStringInfoDelta sn ((s0,sk0),(s1,sk1)) sk01

-- DISTR's, i.e. ks --

-- | Compute the information, in bits, of a distribution of `n` elements
-- into `k` bins through "stars-and-bars"
distrInfoWith :: (Num a, Eq a) => (a -> Double) -> a -> a -> Double
distrInfoWith _ _ 0 = 0.0
distrInfoWith logFact n k = log2e * ( logFact (stars + bars)
                                      - logFact stars
                                      - logFact bars )
  where stars = n
        bars = k - 1
{-# INLINE distrInfoWith #-}

-- | Compute the information, in bits, of a distribution of `n` elements
-- into `k` bins through "stars-and-bars"
distrInfo :: Int -> Int -> Double
distrInfo = distrInfoWith iLogFactorial

-- | Compute the information, in bits, of a distribution of `n` elements
-- into `k` bins through "stars-and-bars"
fDistrInfo :: Double -> Double -> Double
fDistrInfo = distrInfoWith logFactorial

-- STRING's, i.e. ss, buf, src --

-- | Information in bits of the rank of a multiset permutation resolving
-- a string for the given model
stringInfo :: Model -> Double
stringInfo (Model _ n ks)
  | n <= 1 = 0
  | otherwise = log2e * (iLogFactorial n - V.sum (V.map iLogFactorial ks))

scaledStringInfo :: Double -> Model -> Double
scaledStringInfo scale (Model _ n ks)
  | n <= 1 = 0
  | otherwise = log2e * (scaleLogFact n - V.sum (V.map scaleLogFact ks))
  where scaleLogFact = logFactorial . (scale*) . fromIntegral

-- Δ

stringInfoDeltaWith :: Num a => (a -> Double) ->
                       a -> ((Int,a),(Int,a)) -> a -> Double
stringInfoDeltaWith logFact n ((s0,k0),(s1,k1)) k01
  | s0 == s1 = log2e * ( logFact n' - logFact n
                         - logFact (k0 - 2*k01) + logFact k0
                         - logFact k01 )
  | otherwise = log2e * ( logFact n' - logFact n
                          - logFact (k0 - k01) + logFact k0
                          - logFact (k1 - k01) + logFact k1
                          - logFact k01 )
  where n' = n - k01
{-# INLINE stringInfoDeltaWith #-}

stringInfoDelta :: Int -> ((Int,Int),(Int,Int)) -> Int -> Double
stringInfoDelta = stringInfoDeltaWith iLogFactorial
{-# INLINE stringInfoDelta #-}

fStringInfoDelta :: Double -> ((Int,Double),(Int,Double)) -> Double -> Double
fStringInfoDelta = stringInfoDeltaWith logFactorial
{-# INLINE fStringInfoDelta #-}

-- -- GRAVEYARD --
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
