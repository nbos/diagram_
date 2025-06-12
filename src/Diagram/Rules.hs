{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- | Construction rules
module Diagram.Rules (module Diagram.Rules) where

import Prelude hiding (length)

import Control.Monad (forM_)
import Control.Monad.ST (runST)
import Control.Exception (assert)

import Data.Word (Word8)
import qualified Data.ByteString as BS
import qualified Data.ByteString.UTF8 as UTF8
import qualified Data.Vector as B
import qualified Data.Vector.Unboxed as U
import qualified Data.Vector.Generic as V
import qualified Data.Vector.Generic.Mutable as MV
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IM

import Diagram.Util

-- TODO: rm bySnd map (not used)

data Rules = Rules {
  -- | Self-referrential vector of recipes for the construction of all
  -- symbols above 256 indexed at s-256
  invRules :: !(U.Vector (Int,Int)),    -- s01 -> (s0,s1)
  byFst    :: !(B.Vector (IntMap Int)), -- s0 -> s1 -> s01
  bySnd    :: !(B.Vector (IntMap Int))  -- s1 -> s0 -> s01
} deriving (Show)

-- | New empty rule set
empty :: Rules
empty = Rules V.empty emptySets emptySets
  where emptySets = V.replicate 256 IM.empty

-- | Number of rules
size :: Rules -> Int
size = V.length . invRules

-- | Number of defined symbols
numSymbols :: Rules -> Int
numSymbols = (256 +) . size

-- | Compute the length of a symbol
symbolLength :: Rules -> Int -> Int
symbolLength (Rules irs _ _) = go
  where
    go s | s < 256   = 1
         | otherwise = let (s0,s1) = irs V.! (s - 256)
                       in go s0 + go s1

fromList :: [(Int, Int)] -> Rules
fromList l = Rules irs bfs bss
  where
    irs = V.fromList l
    sz = V.length irs
    (bfs, bss) = runST $ do
      mbfs <- MV.replicate (256 + sz) IM.empty
      mbss <- MV.replicate (256 + sz) IM.empty
      forM_ (zip l [256..]) $ \((s0,s1),s01) ->
        assert (s0 < s01 && s1 < s01)
        MV.modify mbfs (IM.insert s1 s01) s0 -- s0 -> s1 -> s01
        >> MV.modify mbss (IM.insert s0 s01) s1 -- s1 -> s0 -> s01
      fbfs <- V.freeze mbfs
      fbss <- V.freeze mbss
      return (fbfs, fbss)

-- | Add a new symbol with a construction rule. Returns updated rules
-- and index of new symbol. O(n)
push :: (Int, Int) -> Rules -> (Int, Rules)
push s0s1@(s0,s1) rs@(Rules irs pcs scs) = assert (both (< s01) s0s1)
                                           (s01, Rules irs' pcs' scs')
  where
    s01 = numSymbols rs
    irs' = V.snoc irs s0s1
    pcs' = V.modify (flip2 MV.modify (IM.insert s1 s01) s0) pcs
    scs' = V.modify (flip2 MV.modify (IM.insert s0 s01) s1) scs

-- | Lookup the rule for constructing a given symbol
(!) :: Rules -> Int -> (Int,Int)
(!) (Rules irs _ _) s = irs V.! (s - 256)
infixl 9 !

-- | Lookup the rule for constructing a given symbol. Nothing returned
-- if the given symbol is atomic (<256) or not yet defined
invLookup :: Rules -> Int -> Maybe (Int,Int)
invLookup rs s | s < 256   = Nothing
               | otherwise = Just $ rs ! s

-- | Return all symbols that have the given symbols as a right symbol
-- (s1) in an unspecified order (in order of the left symbols index)
withAsSnd :: Rules -> Int -> [Int]
withAsSnd (Rules _ _ bss) s1 = IM.elems $ bss V.! s1

constr :: Rules -> Int -> Int -> Int
constr (Rules _ bfs _) s0 s1 = (bfs V.! s0) IM.! s1

-- | Construct the greater symbol if the prediction is from a non-null
-- context, else return the target symbol.
pConstr :: Rules -> (Maybe Int, Int) -> Int
pConstr _ (Nothing, tgt) = tgt
pConstr rs (Just s0, s1) = constr rs s0 s1

-- | Deconstruct a symbol back into a list of bytes
extension :: Rules -> Int -> [Word8]
extension (Rules irs _ _) = go
  where
    go s | s < 256 = [fromIntegral s]
         | otherwise = let (s0,s1) = irs V.! (s - 256)
                       in go s0 ++ go s1

-- | List the symbols that are constructive prefixes of the given
-- symbol, from large to small, starting with the symbol itself and
-- ending with the first atomic symbol of its extension
prefixes :: Rules -> Int -> [Int]
prefixes (Rules irs _ _) = go
  where
    go s | s < 256 = [s]
         | otherwise = let (s0,_) = irs V.! (s - 256)
                       in s : go s0

-- | List the symbols that are constructive suffixes of the given
-- symbol, from large to small, starting with the symbol itself and
-- ending with the last atomic symbol of its extension
suffixes :: Rules -> Int -> [Int]
suffixes (Rules irs _ _) = go
  where
    go s | s < 256 = [s]
         | otherwise = let (_,s1) = irs V.! (s - 256)
                       in s : go s1

-- | Resolve the symbol back into a string of chars
toString :: Rules -> Int -> String
toString = UTF8.toString
           . BS.pack
           . fmap fromIntegral
           .: extension

-- | Given a list of predictions in reverse direction (last,
-- second-to-last, etc.), return the 0-2 possible context symbols: the
-- last target (if it exists) and the last prediction (if it exists) in
-- that order.
resolveBwd :: Rules -> [(Maybe Int, Int)] -> [Int]
resolveBwd _ [] = []
resolveBwd _ ((Nothing,s):_) = [s]
resolveBwd rs ((Just sA, sB):_) = [sB, constr rs sA sB]

-- | Return all symbols that can be constructed from the head symbols,
-- starting with the head symbol (small to large), i.e. recursively
-- construct as long as possible
resolveFwd :: Rules -> [(Maybe Int, Int)] -> [Int]
resolveFwd _ [] = []
resolveFwd rs ((_,sym):predictions) = go sym predictions
  where go s pdns | ((Just s0, s1):rest) <- pdns
                  , s == s0 = s0 : go (constr rs s0 s1) rest
                  | otherwise = [s]
