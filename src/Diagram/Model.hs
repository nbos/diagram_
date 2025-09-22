{-# LANGUAGE TupleSections #-}
module Diagram.Model (module Diagram.Model) where

import Control.Monad.ST
import Control.Monad
import Control.Monad.Primitive (PrimMonad(PrimState))

import Data.Bifunctor
import qualified Data.Vector.Unboxed as U
import qualified Data.Vector.Generic as V
import qualified Data.Vector.Generic.Mutable as MV

import Streaming
import qualified Streaming.Prelude as S

import qualified Codec.Elias as Elias
import qualified Codec.Arithmetic.Combinatorics as Comb
import Codec.Arithmetic.Variety.BitVec (BitVec)

import Diagram.Rules (Rules,Sym)
import qualified Diagram.Rules as R
import Diagram.Information

-- | A model is a set of symbol defined through construction rules and
-- an integer-multinomial distribution (histogram) of the symbols that
-- can be resolved a given string identifying corresponding multiset
-- permutations
data Model s = Model {
  modelRules :: !Rules,
  modelTotalCount :: !Int,
  modelCounts :: !(U.MVector s Int)
}

------------------
-- CONSTRUCTION --
------------------

empty :: PrimMonad m => m (Model (PrimState m))
empty = Model R.empty 0 <$> U.unsafeThaw (U.replicate 256 0)

incCounts :: PrimMonad m =>
             Model (PrimState m) -> [Sym] -> m (Model (PrimState m))
incCounts = foldM incCount

incCount :: PrimMonad m =>
            Model (PrimState m) -> Sym -> m (Model (PrimState m))
incCount (Model rs n ks) s = MV.modify ks (+1) s
                             >> return (Model rs (n+1) ks)

-- | Reconstruction from rule set and fully constructed symbol string
fromList :: PrimMonad m => Rules -> [Sym] -> m (Model (PrimState m))
fromList rs ss = do
  ks <- U.unsafeThaw $ U.replicate (R.numSymbols rs) 0
  forM_ ss $ MV.modify ks (+1)
  n <- MV.foldl' (+) 0 ks
  return $ Model rs n ks

-- | Reconstruction from rule set and fully constructed symbol stream
fromStream :: PrimMonad m => Rules -> Stream (Of Sym) m r ->
                             m (Model (PrimState m), r)
fromStream rs ss = do
  ks <- U.unsafeThaw $ U.replicate (R.numSymbols rs) 0
  r <- S.effects $ S.mapM (MV.modify ks (+1)) ss
  n <- MV.foldl' (+) 0 ks
  return (Model rs n ks, r)

clone :: PrimMonad m => Model (PrimState m) -> m (Model (PrimState m))
clone (Model rs n ks) = Model rs n <$> MV.clone ks

pushRule :: PrimMonad m => Model (PrimState m) -> (Sym,Sym) -> Int ->
                           m (Sym, Model (PrimState m))
pushRule (Model rs n ks) (s0,s1) n01 = do
  ks' <- MV.grow ks 1  -- O(n) snoc
  MV.write ks' s01 n01 --
  forM_ [s0,s1] $ MV.modify ks' (+(-n01))
  return (s01, Model rs' n' ks')
  where
    (s01,rs') = R.pushRule (s0,s1) rs
    n' = n - n01

-------------------
-- SERIALIZATION --
-------------------

-- | Serialize a symbol string given a rule set through the
-- serialization of the model of the string and a permutation
encode :: Rules -> [Sym] -> BitVec
encode rs ss = rsCode <> nCode <> ksCode <> ssCode
  where (rsCode, nCode, ksCode, ssCode) = encodeParts rs ss

-- | Serialize the four (4) components of a modeled string
-- serialization. In order: rules, total symbols count, individual
-- symbol counts, and the string as a permutation
encodeParts :: Rules -> [Sym] -> (BitVec, BitVec, BitVec, BitVec)
encodeParts rs ss = (rsCode, nCode, ksCode, ssCode)
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
decode :: PrimMonad m => BitVec -> m (Maybe (Model (PrimState m), [Sym], BitVec))
decode bv
  | Just (rs, bv') <- R.decode bv
  , Just (n , bv'') <- first fromInteger <$> Elias.decodeDelta bv'
  , Just (ks, bv''') <- Comb.decodeDistribution (n, R.numSymbols rs) bv''
  , Just (ss, bv'''') <- Comb.decodeMultisetPermutation (zip [0..] ks) bv''' = do
      mdl <- Model rs n <$> U.unsafeThaw (V.fromList ks)
      return $ Just (mdl, ss, bv'''')
  | otherwise = return Nothing

--------------------------
-- INFORMATION MEASURES --
--------------------------

-- I --

-- | Information in bits of the given model + a sampled symbol string
information :: PrimMonad m => Model (PrimState m) -> m Double
information mdl = do
  (rsInfo, nInfo, ksInfo, ssInfo) <- informationParts mdl
  return $ rsInfo + nInfo + ksInfo + ssInfo

informationParts :: PrimMonad m => Model (PrimState m) ->
                                   m (Double, Double, Double, Double)
informationParts mdl@(Model rs n ks) =
  (rsInfo, nInfo, ksInfo, ) <$> ssInfo
  where
    rsInfo = R.information rs
    nInfo = eliasInfo n
    ksInfo = distrInfo n (MV.length ks)
    ssInfo = stringInfo mdl

-- ΔI

-- For an alphabet of size `m`, a string of length `n`, a joint (s0,s1)
-- with count `k01` in the string, and counts `k0` of symbol `s0` and
-- `k1` of symbol `s1`, the difference in bits of the length of the
-- serialization using our encoding scheme (rules, string len,
-- histogram, permutation) can be computed efficiently as the sum of the
-- differences in code length of the four (4) different fields,
-- according to their serialization method.
--
-- The exapansion of the four terms is as follows:
--
-- [Rules]
-- len(Elias(m-256)) - len(Elias(m-255)) + 2 * log(m)
--
-- [String length]
-- len(Elias(n-k01)) - len(Elias(n))
--
-- [Histogram]
-- log((n-k01+m-1)!) - log((n-k01)!) - log((m-1)!)
-- - log((n+m-1)!) + log(n!) + log((m-1)!)
--
-- [Permutation]
-- log((n-k01)!) - log(n!) + log(k0!) - log(k01!)
-- if s0 == s1 then - log((k0-2*k01)!)
-- else - log((k0-k01)!) - log((k1-k01)!) + log(k1!)
--
-- A number of terms in the histogram's and permutation's cancel out
-- which makes them equal to:
--
-- [Histogram]
-- log((n-k01+m-1)!) - log((n+m-1)!)
--
-- [Permutation]
-- log(k0!) - log(k01!)
-- if s0 == s1 then - log((k0-2*k01)!)
-- else - log((k0-k01)!) - log((k1-k01)!) + log(k1!)

-- | Given the number of symbols `m` (length of the counts vector), the
-- length of the string `n` (sum of counts), the count of a symbol to be
-- introduced `k01` (a joint count) where the left and right parts are
-- two (2) different symbols (so s0 /= s1) and the count of the left
-- `k0` and right `k1` part of the introduced joint, return the
-- difference in code length, in bits, of the serialization.
infoLoss2 :: Int -> Int -> Int -> Int -> Int -> Double
infoLoss2 m n k01 k0 k1 = rLoss m
                          + fromIntegral (nLoss n k01)
                          + kLoss m n k01
                          + sLoss2 k01 k0 k1

-- | Given the number of symbols `m` (length of the counts vector), the
-- length of the string `n` (sum of counts), the count of a symbol to be
-- introduced `k00` (a joint count) where the left and right parts are
-- the same (1) symbol (so s0 == s1) and the count of the part symbol
-- `k0` before the introduction of the joint symbol, return the
-- difference in code length, in bits, of the serialization.
infoLoss1 :: Int -> Int -> Int -> Int -> Double
infoLoss1 m n k00 k0 = rLoss m
                       + fromIntegral (nLoss n k00)
                       + kLoss m n k00
                       + sLoss1 k00 k0

-- | Given the number of symbols `m` in a rule set, return the
-- difference in code length of its serialization.
rLoss :: Int -> Double
rLoss = R.infoDelta'

-- | Given the length of the string `n` and the count of an introduced
-- symbol, return the difference in length of the Elias encoding of the
-- length after the introduction of the symbol definition. Always
-- positive.
nLoss :: Int -> Int -> Int
nLoss n k01 = eliasCodeLen n' - eliasCodeLen n
  where n' = n - k01

-- | Given the number of symbols `m` (length of the counts vector), the
-- length of the string `n` (sum of counts), the count of a symbol to be
-- introduced `k` (a joint count), return the third term of the
-- difference in code length, in bits, of the serialization. Always
-- negative.
kLoss :: Int -> Int -> Int -> Double
kLoss m n = \k -> iLogFactorial (x - k) - iLogFactorial x
  where x = m - 1 + n

-- | Given a joint count where the left and right parts are two (2)
-- different symbols (so s0 /= s1) and the count of the left `k0` and
-- right `k1` part of the introduced joint, return the fourth term of
-- the difference in code length, in bits, of the serialization. Always
-- positive.
sLoss2 :: Int -> Int -> Int -> Double
sLoss2 k01 k0 k1 = iLogFactorial k0 + iLogFactorial k1
                   - iLogFactorial k0' - iLogFactorial k1'
                   - iLogFactorial k01
  where k0' = k0 - k01
        k1' = k1 - k01

-- | Given a joint count where the left and right parts are the same
-- symbol (s0 == s1) and the count of the part `k0`, return the fourth
-- term of the difference in code length, in bits, of the
-- serialization. Always positive.
sLoss1 :: Int -> Int -> Double
sLoss1 k00 k0 = iLogFactorial k0 - iLogFactorial k0' - iLogFactorial k00
  where k0' = k0 - 2*k00

-- | Given two symbols, compute the difference in code length of the
-- serialization were a rule introduced for their joint symbol.
infoDelta :: PrimMonad m => Model (PrimState m) -> (Sym,Sym) -> Int -> m Double
infoDelta (Model rs n ks) (s0,s1) k01
  | s0 == s1 = infoLoss1 m n k01 <$> mk0
  | otherwise = liftA2 (infoLoss2 m n k01) mk0 mk1
  where
    m = R.numSymbols rs
    mk0 = MV.read ks s0
    mk1 = MV.read ks s1

-- | Compute the change in code length (bits) of the model + symbol
-- string matching it given a new rule introduction. Not optimized: use
-- infoDelta instead for an exact value or infoLoss1-2.
naiveInfoDelta :: PrimMonad m => Model (PrimState m) -> (Sym,Sym) -> Int -> m Double
naiveInfoDelta (Model rs n ks) (s0,s1) k01 = do
  k0 <- MV.read ks s0
  k1 <- MV.read ks s1
  -- ss a multiset permutation of counts ks:
  let ssInfoDelta = stringInfoDelta n ((s0,k0),(s1,k1)) k01
  return $ rsInfoDelta + nInfoDelta + ksInfoDelta + ssInfoDelta
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

-- I(ks) --

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

-- I(ss) --

-- | Information in bits of the rank of a multiset permutation resolving
-- a string for the given model
stringInfo :: PrimMonad m => Model (PrimState m) -> m Double
stringInfo (Model _ n ks)
  | n <= 1 = return 0
  | otherwise = do
      ldenom <- MV.foldl' (flip ((+) . iLogFactorial)) 0.0 ks
      return $ log2e * (iLogFactorial n - ldenom)

-- ΔI(ss)

stringInfoDeltaWith :: Num a => (a -> Double) ->
                       a -> ((Sym,a),(Sym,a)) -> a -> Double
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

stringInfoDelta :: Int -> ((Sym,Int),(Sym,Int)) -> Int -> Double
stringInfoDelta = stringInfoDeltaWith iLogFactorial
{-# INLINE stringInfoDelta #-}

fStringInfoDelta :: Double -> ((Sym,Double),(Sym,Double)) -> Double -> Double
fStringInfoDelta = stringInfoDeltaWith logFactorial
{-# INLINE fStringInfoDelta #-}

-- -- GRAVEYARD --
-- -- | Information in bits of the given model + a sampled symbol string if
-- -- the string the model was fit on `scale` times as big
-- scaledInformation :: PrimMonad m => Double -> Model (PrimState m) -> m Double
-- scaledInformation scale mdl = do
--   (rsInfo, nInfo, ksInfo, ssInfo) <- scaledInformationParts scale mdl
--   return $ rsInfo + nInfo + ksInfo + ssInfo

-- scaledInformationParts :: PrimMonad m => Double -> Model (PrimState m) ->
--                                          m (Double, Double, Double, Double)
-- scaledInformationParts scale mdl@(Model rs n ks) =
--   (rsInfo, nInfo, ksInfo,) <$> ssInfo
--   where
--     sn     = scale * fromIntegral n
--     rsInfo = R.information rs
--     nInfo  = eliasInfo (round sn)
--     ksInfo = fDistrInfo sn (fromIntegral $ MV.length ks)
--     ssInfo = scaledStringInfo scale mdl

-- -- | Expected `infoDelta` when the model's size `n` is scaled by `scale`
-- scaledInfoDelta :: PrimMonad m => Double -> Model (PrimState m) ->
--                                   (Int,Int) -> Int -> m Double
-- scaledInfoDelta scale (Model rs n ks) (s0,s1) k01 = do
--   k0 <- MV.read ks s0
--   k1 <- MV.read ks s1
--   let sk0 = scale * fromIntegral k0
--       sk1 = scale * fromIntegral k1
--       -- ss a multiset permutation of counts ks:
--       ssInfoDelta = fStringInfoDelta sn ((s0,sk0),(s1,sk1)) sk01
--   return $ rsInfoDelta + nInfoDelta + ksInfoDelta + ssInfoDelta
--   where
--     sn   = scale * fromIntegral n
--     sk01 = scale * fromIntegral k01
--     sn'  = sn - sk01

--     numSymbols = R.numSymbols rs
--     fNumSymbols = fromIntegral numSymbols
--     -- rules info delta (constant):
--     rsInfoDelta = R.infoDelta rs
--     -- n elias encoding:
--     nInfoDelta = eliasInfo (round sn') - eliasInfo (round sn)
--     -- ks a distribution of n elements:
--     ksInfoDelta = fDistrInfo sn' (fNumSymbols + 1) -- new
--                   - fDistrInfo sn fNumSymbols -- old

-- scaledStringInfo :: PrimMonad m => Double -> Model (PrimState m) -> m Double
-- scaledStringInfo scale (Model _ n ks)
--   | n <= 1 = return 0
--   | otherwise = do
--       ldenom <- MV.foldl' (\acc k -> acc + scaleLogFact k) 0.0 ks
--       return $ log2e * (scaleLogFact n - ldenom)
--   where scaleLogFact = logFactorial . (scale*) . fromIntegral

-- -- | Report to stdout the accuracy of the approximated (based on the
-- -- `n`th first constructed symbols) code-lengths of the different parts
-- -- of the serialization of the given string of atoms.
-- printApproxReport :: Rules -> Int -> [Int] -> IO ()
-- printApproxReport rs n src = do
--   let numSymbols = R.numSymbols rs
--       symbolLengths = R.symbolLengths rs
--       ssReal = R.subst rs src -- construct
--       (ss, ssRest) = splitAt n ssReal -- crop

--   mdl <- fromList rs ss
--   (Model _ nReal ksRealMut) <- flip incCounts ssRest =<< clone mdl
--   ksReal <- U.toList <$> U.freeze ksRealMut

--   let extLen = sum $ (symbolLengths U.!) <$> ss
--       extLenReal = sum $ (symbolLengths U.!) <$> ssReal
--       scale = fromIntegral extLenReal / fromIntegral extLen

--   (rsInfo, nInfo, ksInfo, ssInfo) <- scaledInformationParts scale mdl
--   let (rsCode, nCode, ksCode, ssCode) = encodeParts rs ssReal

--   -- TODO: print report like a table with \t's and PASS/FAIL on roundtrip

--   -- rs valid.
--   let rsCodeLen = BV.length rsCode
--       rsError = 100 * (rsInfo - fromIntegral rsCodeLen)
--                 / fromIntegral rsCodeLen :: Double
--       rsDecoded = fst <$> R.decode rsCode
--   putStrLn $ printf "   rs: est. %.1f real %d (%+.2f%% err.) (roundtrip: %s)"
--     rsInfo rsCodeLen rsError
--     (show $ Just rs == rsDecoded)

--   -- n valid.
--   let nCodeLen = BV.length nCode
--       nError = 100 * (nInfo - fromIntegral nCodeLen)
--                / fromIntegral nCodeLen :: Double
--       nDecoded = fst <$> Elias.decodeDelta nCode
--   putStrLn $ printf "   n:  est. %.1f real %d (%+.2f%% err.) (roundtrip: %s)"
--     nInfo nCodeLen nError
--     (show $ Just (fromIntegral nReal) == nDecoded)

--   -- ks valid.
--   let ksCodeLen = BV.length ksCode
--       ksError = 100 * (ksInfo - fromIntegral ksCodeLen)
--                 / fromIntegral ksCodeLen :: Double
--       ksDecoded = fst <$> Comb.decodeDistribution (nReal,numSymbols) ksCode
--   putStrLn $ printf "   ks: est. %.1f real %d (%+.2f%% err.) (roundtrip: %s)"
--     ksInfo ksCodeLen ksError
--     (show $ Just ksReal == ksDecoded)
--   when (Just ksReal /= ksDecoded) $ do
--     print nReal
--     print numSymbols
--     putStr "ksReal: " >> print ksReal
--     putStr "ksDecoded: " >> print ksDecoded
--     exitFailure

--   -- ss valid.
--   let ssCodeLen = BV.length ssCode
--       ssError = 100 * (ssInfo - fromIntegral ssCodeLen)
--                 / fromIntegral ssCodeLen :: Double
--       ssDecoded = fst <$> Comb.decodeMultisetPermutation (zip [0..] ksReal) ssCode
--   putStrLn $ printf "   ss: est. %.1f real %d (%+.2f%% err.) (roundtrip: %s)"
--     ssInfo ssCodeLen ssError
--     (show $ Just ssReal == ssDecoded)
--   when (Just ssReal /= ssDecoded) $ do
--     putStr "ssReal: " >> print ssReal
--     putStr "ssDecoded: " >> print ssDecoded
--     exitFailure

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
