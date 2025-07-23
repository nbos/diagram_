{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- | Construction rules
module Diagram.Rules (module Diagram.Rules) where

import Prelude

import Control.Exception (assert)
import Control.Monad

import Data.Word (Word8)
import Data.Tuple.Extra
import qualified Data.ByteString as BS
import qualified Data.ByteString.UTF8 as UTF8

import qualified Data.Vector as B
import qualified Data.Vector.Unboxed as U
import qualified Data.Vector.Generic as V
import qualified Data.Vector.Generic.Mutable as MV

import Numeric.SpecFunctions (logFactorial)

import qualified Codec.Elias.Natural as Elias
import qualified Codec.Arithmetic.Variety as Var
import Codec.Arithmetic.Variety.BitVec (BitVec)
import qualified Codec.Arithmetic.Variety.BitVec as BV

import Diagram.Util

-- | Self-referrential vector of recipes for the construction of all
-- symbols above 256 indexed at s-256
type Rules = U.Vector (Int,Int)

-- | New empty rule set
empty :: Rules
empty = V.empty

-- | Number of rules
size :: Rules -> Int
size = V.length

-- | Number of defined symbols
numSymbols :: Rules -> Int
numSymbols = (256 +) . size

-- | Compute the length of a symbol
symbolLength :: Rules -> Int -> Int
symbolLength rs = go
  where
    go s | s < 256   = 1
         | otherwise = let (s0,s1) = rs V.! (s - 256)
                       in go s0 + go s1

fromList :: [(Int, Int)] -> Rules
fromList = V.fromList

-- | Add a new symbol with a construction rule. Returns updated rules
-- and index of new symbol. O(n)
push :: (Int, Int) -> Rules -> (Int, Rules)
push s0s1 rs =
  assert (uncurry (&&) $ both (< s01) s0s1)
  (s01, irs')
  where
    s01 = numSymbols rs
    irs' = V.snoc rs s0s1

-- | Lookup the rule for constructing a given symbol
(!) :: Rules -> Int -> (Int,Int)
(!) rs s = rs V.! (s - 256)
infixl 9 !

-- | Lookup the rule for constructing a given symbol. Nothing returned
-- if the given symbol is atomic (<256) or not yet defined
(!?) :: Rules -> Int -> Maybe (Int,Int)
(!?) = invLookup
infixl 9 !?

-- | Lookup the rule for constructing a given symbol. Nothing returned
-- if the given symbol is atomic (<256) or not yet defined
invLookup :: Rules -> Int -> Maybe (Int,Int)
invLookup rs s | s < 256   = Nothing
               | otherwise = Just $ rs ! s

-- | Deconstruct a symbol back into a list of bytes
extension :: Rules -> Int -> [Word8]
extension rs = go
  where
    go s | s < 256 = [fromIntegral s]
         | otherwise = let (s0,s1) = rs V.! (s - 256)
                       in go s0 ++ go s1

-- | List the symbols that are constructive prefixes of the given
-- symbol, from large to small, starting with the symbol itself and
-- ending with the first atomic symbol of its extension
prefixes :: Rules -> Int -> [Int]
prefixes rs = go
  where
    go s | s < 256 = [s]
         | otherwise = let (s0,_) = rs V.! (s - 256)
                       in s : go s0

-- | List the symbols that are constructive suffixes of the given
-- symbol, from large to small, starting with the symbol itself and
-- ending with the last atomic symbol of its extension
suffixes :: Rules -> Int -> [Int]
suffixes rs = go
  where
    go s | s < 256 = [s]
         | otherwise = let (_,s1) = rs V.! (s - 256)
                       in s : go s1

-- | Resolve the symbol back into a string of chars
toString :: Rules -> [Int] -> String
toString = UTF8.toString
           . BS.pack
           . fmap fromIntegral
           .: concatMap
           . extension

--------------
-- INDEXING --
--------------

-- | Generic for `asFsts` and `asSnds`
asGen :: ((Int,Int) -> Int) -> Rules -> B.Vector [Int]
asGen f rs = V.create $ do
  mv <- MV.replicate (numSymbols rs) []
  forM_ [256..numSymbols rs - 1] $ \s ->
    MV.modify mv (s:) $ f (rs ! s)
  return mv
{-# INLINE asGen #-}

-- | For every symbol, the list of composite symbols that have that
-- symbol as first/left part.
asFsts :: Rules -> B.Vector [Int]
asFsts = asGen fst

-- | For every symbol, the list of composite symbols that have that
-- symbol as second/right part.
asSnds :: Rules -> B.Vector [Int]
asSnds = asGen snd

-------------------
-- SERIALIZATION --
-------------------

encode :: Rules -> BitVec
encode rs = lenCode <> rulesCode -- cat of rulesLen + rules
  where
    lenCode = Elias.encodeDelta $ fromIntegral $ V.length rs
    rulesCode = Var.encode $
                foldr (\(a,b) acc -> a : b : acc) [] $
                zipWith (\(s0,s1) base -> ( (fromIntegral s0, base)
                                          , (fromIntegral s1, base) ))
                (V.toList rs)
                [256::Integer ..]

decode :: BitVec -> Maybe (Rules, BitVec)
decode bv = do
  (len,bv') <- Elias.decodeDelta bv
  let bases = foldr (\a acc -> a:a:acc) [] $ -- dupe each
              take (fromIntegral len) [256..]
  (vals,bv'') <- Var.decode bases bv'
  Just ( V.fromList $ go $ fromIntegral <$> vals
       , bv'' )
  where
    go [] = []
    go (a:b:rest) = (a,b):go rest
    go (_:_) = error "impossible"

-- | The exact length of the code (in bits) of the serialization of the
-- rule set (not very efficient)
codeLen :: Rules -> Int
codeLen rs = lenCodeLen + rulesCodeLen
  where
    len = V.length rs
    lenCode = Elias.encodeDelta $ fromIntegral len
    lenCodeLen = BV.length lenCode
    rulesCodeLen = Var.codeLen1 $ product $
                   (\a -> a*a) <$> take len [256..]

-- | The amount of information (in bits) in the rule set (more
-- efficient)
information :: Rules -> Double
information rs = lenCodeInfo + rulesCodeInfo
  where
    len = V.length rs
    lenCode = Elias.encodeDelta $ fromIntegral len
    lenCodeInfo = fromIntegral $ BV.length lenCode
    rulesCodeInfo = log2e * 2 * ( logFactorial (256 + len)
                                  - logFactorial (256 :: Int) )

-- | logBase 2 e, for [nats] * log2e = [bits]
log2e :: Double
log2e = 1.44269504088896340735992468100189214

eliasInfo :: Int -> Double
eliasInfo = fromIntegral
            . BV.length
            . Elias.encodeDelta
            . fromIntegral

-- | The forward difference between the information of the rule set
-- after adding a new rule relative to the information of the rule set
-- now. @fwdDeltaInfo rs@ approximately computes @information (snd $
-- push (s0,s1) rs) - information rs@
fwdInfoDelta :: Rules -> Double
fwdInfoDelta rs = lenDeltaInfo + rulesDeltaInfo
  where
    len = V.length rs
    lenDeltaInfo = eliasInfo (len + 1) - eliasInfo len
    rulesDeltaInfo = log2e * 2 * log (fromIntegral (256 + len + 1))
