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

import Diagram.Util

data Rules = Rules {
  -- | Self-referrential vector of recipes for the construction of all
  -- symbols above 256 indexed at s-256
  invRules :: !(U.Vector (Int,Int)), -- s01 -> (s0,s1)
  sufChildren :: !(B.Vector [Int]) -- s1 -> [s01]
}

-- | New empty rule set
empty :: Rules
empty = Rules V.empty $ V.replicate 256 []

-- | Number of rules
size :: Rules -> Int
size = V.length . invRules

-- | Number of defined symbols
numSymbols :: Rules -> Int
numSymbols = (256 +) . size

-- | Compute the length of a symbol
symbolLength :: Rules -> Int -> Int
symbolLength (Rules irs _) = go
  where
    go s | s < 256   = 1
         | otherwise = let (s0,s1) = irs V.! (s - 256)
                       in go s0 + go s1

fromList :: [(Int, Int)] -> Rules
fromList l = Rules irs scs
  where
    irs = V.fromList l
    sz = V.length irs
    scs = runST $ do
      mscs <- MV.replicate (256 + sz) []
      forM_ (zip l [256..]) $ \((s0,s1),s01) ->
        assert (s0 < s01 && s1 < s01)
        MV.modify mscs (s01:) s1
      V.freeze mscs

-- | Add a new symbol with a construction rule. Returns updated rules
-- and index of new symbol. O(n)
push :: (Int, Int) -> Rules -> (Int, Rules)
push s0s1@(_,s1) rs@(Rules irs scs) = assert (both (< s01) s0s1)
                                      (s01, Rules irs' scs')
  where
    s01 = numSymbols rs
    irs' = V.snoc irs s0s1
    scs' = V.modify (flip2 MV.modify (s01:) s1) scs

-- | Lookup the rule for constructing a given symbol
(!) :: Rules -> Int -> (Int,Int)
(!) (Rules irs _) s = irs V.! (s - 256)
infixl 9 !

-- | Lookup the rule for constructing a given symbol. Nothing returned
-- if the given symbol is atomic (<256) or not yet defined
invLookup :: Int -> Rules -> Maybe (Int,Int)
invLookup s rs | s < 256   = Nothing
               | otherwise = Just $ rs ! s

-- | Return all symbols that have the given symbols as a right symbol
-- (s1) in an unspecified order (reverse symbol index as value for now)
sChildren :: Int -> Rules -> [Int]
sChildren s (Rules _ scs)= scs V.! s

-- | Deconstruct a symbol back into a list of bytes
extension :: Rules -> Int -> [Word8]
extension (Rules irs _) = go
  where
    go s | s < 256 = [toEnum s]
         | otherwise = let (s0,s1) = irs V.! (s - 256)
                       in go s0 ++ go s1

-- | List the symbols that are constructive prefixes of the given
-- symbol, from large to small, starting with the symbol itself and
-- ending with the first atomic symbol of its extension
cPrefixes :: Rules -> Int -> [Int]
cPrefixes (Rules irs _) = go
  where
    go s | s < 256 = [s]
         | otherwise = let (s0,_) = irs V.! (s - 256)
                       in s : go s0

-- | List the symbols that are constructive suffixes of the given
-- symbol, from large to small, starting with the symbol itself and
-- ending with the last atomic symbol of its extension
cSuffixes :: Rules -> Int -> [Int]
cSuffixes (Rules irs _) = go
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

-- resolveGeneric :: forall m. PrimMonad m =>
--                   (forall a b. (a -> a -> b) -> a -> a -> b) ->
--                   (Rules -> Int -> (IntMap Int)) ->
--                   Rules -> [Int] -> [Int]
-- resolveGeneric _ _ _ [] = return []
-- resolveGeneric comb withAsFstFn rs (a0:atoms) = go a0 atoms
--   where
--     go s0 as = do
--       -- see what s0 is fst as:
--       m0 <- rs `withAsFstFn` s0
--       -- match their extensions against atoms:
--       mres0s <- mapM (`againstAtoms` as) $ IM.toList m0
--       -- if match, recurse, looking up further constructions:
--       recs <- mapM (uncurry go) $ catMaybes mres0s
--       return $ s0 : concat recs

--     -- | check a symbol's extension against the atom string, returning
--     -- remaining atoms if they match
--     againstAtoms :: (Int, res) -> [Int] -> (Maybe (res, [Int]))
--     againstAtoms (s1,res) as = (res,)
--       <<$>> goMatch (extensionGeneric comb rs s1) as

--     -- | onlyIfMatch's rec helper
--     goMatch :: Stream (Of Int) m r -> [Int] -> (Maybe [Int])
--     goMatch str as = S.uncons str >>=
--       \case Nothing -> return $ Just as -- end of extension
--             Just (s,str') -> case as of
--               [] -> return Nothing
--               a:rest | s == a -> goMatch str' rest
--                      | otherwise -> return Nothing
-- {-# INLINE resolveGeneric #-}

-- -- | Construct all possible symbols at the head of the given string of
-- -- symbols
-- resolvePrefixes :: Rules -> [Int] -> [Int]
-- resolvePrefixes = resolveGeneric id withAsFst

-- -- | Construct all possible symbols at the head of a reversed list of
-- -- symbols (i.e. all symbols that end at the tail of the reverse of the
-- -- input list)
-- resolveSuffixes :: Rules -> [Int] -> [Int]
-- resolveSuffixes = resolveGeneric flip withAsSnd
