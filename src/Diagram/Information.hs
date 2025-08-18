module Diagram.Information (module Diagram.Information) where

import qualified Numeric.SpecFunctions as Spec
import qualified Codec.Elias.Natural as Elias
import qualified Codec.Arithmetic.Variety.BitVec as BV

-- | logBase 2 e, for [nats] * log2e = [bits]
log2e :: Double
log2e = 1.44269504088896340735992468100189214

nats2bits :: Double -> Double
nats2bits = (*) log2e

eliasCodeLen :: Int -> Int
eliasCodeLen = BV.length
               . Elias.encodeDelta
               . fromIntegral

eliasInfo :: Int -> Double
eliasInfo = fromIntegral . eliasCodeLen

scaleInt :: Double -> Int -> Int
scaleInt scale = round . (scale*) . fromIntegral

logFactorial :: Double -> Double
logFactorial = Spec.logGamma . (+1)

iLogFactorial :: Int -> Double
iLogFactorial = Spec.logFactorial
