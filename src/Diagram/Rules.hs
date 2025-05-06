{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- | Construction rules
module Diagram.Rules (module Diagram.Rules) where

import Prelude hiding (length)
import Control.Monad (foldM)
import Control.Monad.Primitive (PrimMonad)
import Control.Exception (assert)

import Streaming
import qualified Streaming.Prelude as S

import Data.Word (Word8)
-- import Data.Maybe (catMaybes)
-- import Data.IntMap.Strict (IntMap)
-- import qualified Data.IntMap.Strict as IM
import qualified Data.ByteString as BS
import qualified Data.ByteString.UTF8 as UTF8

import Diagram.Dynamic (UnboxedVec, PrimitiveVec)
import qualified Diagram.Dynamic as DMV
import Diagram.Util

-- | Construction rules with O(1) push and lookup inside a PrimMonad `m`
data Rules m = Rules {
  -- -- | Construction rules indexed by the first symbol
  -- rulesByFst :: !(BoxedVec m (IntMap Int)), -- s0 -> s1 -> s01
  -- -- | Construction rules indexed by the second symbol
  -- rulesBySnd :: !(BoxedVec m (IntMap Int)), -- s1 -> s0 -> s01
  -- | Self-referrential vector of recipes for the construction of all
  -- symbols above 256 indexed at s-256
  invRules   :: !(UnboxedVec m (Int,Int)), -- s01 -> (s0,s1)
  -- | Memoized vector of lengths, otherwise, it's O(len)
  symbolLengths :: !(PrimitiveVec m Int)
}

-- | New empty rule set
new :: PrimMonad m => m (Rules m)
new = do
  -- byFst <- DMV.replicate 256 IM.empty
  -- bySnd <- DMV.replicate 256 IM.empty
  inv <- DMV.new
  Rules inv <$> DMV.new

-- | Number of rules
size :: Rules m -> Int
size = DMV.dynLength . invRules

-- | Number of defined symbols
numSymbols :: Rules m -> Int
numSymbols = (256 +) . size

-- | Compute the length of a symbol
symbolLength :: PrimMonad m => Rules m -> Int -> m Int
symbolLength rs s
  | s < 256   = return 1
  | otherwise = DMV.read (symbolLengths rs) (s - 256) -- go
  -- where go s = invLookup s rs >>= \case
  --         Nothing -> assert (s < 256) $ return 1
  --         Just (s0,s1) -> do
  --           pre <- go s0
  --           suf <- go s1
  --           return $ pre + suf

fromList :: PrimMonad m => [(Int,Int)] -> m (Rules m)
fromList l = do
  rs <- new
  foldM (fmap snd .: flip push) rs l

-- -- | Deconstruct a symbol back into a list of atoms/byte string
-- extension :: PrimMonad m => Rules m -> Int -> m [Int]
-- extension rs = go
--   where go s = invLookup s rs >>= \case
--           Nothing -> assert (s < 256) $ return [s]
--           Just (s0,s1) -> do
--             pre <- go s0
--             suf <- go s1
--             return $ pre ++ suf

-- | List the symbols that are prefixes of the given symbol, from large
-- to small, starting with the symbol itself and ending with the first
-- atomic symbol of its extension
prefixes :: PrimMonad m => Rules m -> Int -> m [Int]
prefixes rs = go
  where go s = invLookup s rs >>= \case
          Nothing -> assert (s < 256) $ return [s]
          Just (s0,_) -> (s:) <$> go s0

-- | List the symbols that are suffixes of the given symbol, from large
-- to small, starting with the symbol itself and ending with the last
-- atomic symbol of its extension
suffixes :: PrimMonad m => Rules m -> Int -> m [Int]
suffixes rs = go
  where go s = invLookup s rs >>= \case
          Nothing -> assert (s < 256) $ return [s]
          Just (_,s1) -> (s:) <$> go s1

-- | Resolve the symbol back into a string of chars
toString :: PrimMonad m => Rules m -> Int -> m String
toString = fmap (UTF8.toString
                 . BS.pack
                 . fmap fromIntegral)
           . S.toList_
           .: extension

-- | Add a new symbol with a construction rule. Returns updated rules
-- and index of new symbol.
push :: PrimMonad m => (Int,Int) -> Rules m -> m (Int, Rules m)
push s0s1@(s0,_) rs@(Rules inv lengths) =
  assert (both (< numSymbols rs) s0s1) $ do
  -- s0's and s1's
  let s01 = numSymbols rs
  -- DMV.modify byFst (IM.insert s1 s01) s0 -- s0 -> s1 -> s01
  -- DMV.modify bySnd (IM.insert s0 s01) s1 -- s1 -> s0 -> s01

  -- initialize s01's values
  -- byFst' <- DMV.push byFst IM.empty -- (s01,{}) -> {}
  -- bySnd' <- DMV.push bySnd IM.empty -- ({},s01) -> {}
  inv' <- DMV.push inv s0s1     -- (s0, s1) -> s01

  l0 <- symbolLength rs s0
  l1 <- symbolLength rs s0
  lengths' <- DMV.push lengths (l0 + l1)

  return (s01, Rules inv' lengths')

-- -- | Lookup construction rules where the given symbol is the first part
-- -- (prefix)
-- withAsFst :: PrimMonad m => Rules m -> Int -> m (IntMap Int)
-- withAsFst = DMV.read . rulesByFst
  
-- -- | Lookup construction rules where the given symbol is the second part
-- -- (suffix)
-- withAsSnd :: PrimMonad m => Rules m -> Int -> m (IntMap Int)
-- withAsSnd = DMV.read . rulesBySnd

-- | Lookup the rule for constructing a given symbol
(<!) :: PrimMonad m => Rules m -> Int -> m (Int,Int)
(<!) rs = DMV.read (invRules rs) . (+) (-256)
infixl 9 <!

-- | Lookup the rule for constructing a given symbol. Nothing returned
-- if the given symbol is atomic (<256) or not yet defined
(<!?) :: PrimMonad m => Rules m -> Int -> m (Maybe (Int,Int))
(<!?) rs = DMV.readMaybe (invRules rs) . (+) (-256)
infixl 9 <!?

-- | Lookup the rule for constructing a given symbol. Nothing returned
-- if the given symbol is atomic (<256) or not yet defined
invLookup :: PrimMonad m => Int -> Rules m -> m (Maybe (Int,Int))
invLookup = flip (<!?)

extensionGeneric :: PrimMonad m => (forall a b. (a -> a -> b) -> a -> a -> b) ->
                    Rules m -> Int -> Stream (Of Word8) m ()
extensionGeneric comb rs = go
  where
    go s = lift (invLookup s rs) >>=
      \case Nothing -> assert (s >= 0 && s < 256)
                       S.yield $ toEnum s
            Just (s0,s1) -> comb (>>) (go s0) (go s1)
{-# INLINE extensionGeneric #-}

extension :: PrimMonad m => Rules m -> Int -> Stream (Of Word8) m ()
extension = extensionGeneric id

revExtension :: PrimMonad m => Rules m -> Int -> Stream (Of Word8) m ()
revExtension = extensionGeneric flip

-- resolveGeneric :: forall m. PrimMonad m =>
--                   (forall a b. (a -> a -> b) -> a -> a -> b) ->
--                   (Rules m -> Int -> m (IntMap Int)) ->
--                   Rules m -> [Int] -> m [Int]
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
--     againstAtoms :: (Int, res) -> [Int] -> m (Maybe (res, [Int]))
--     againstAtoms (s1,res) as = (res,)
--       <<$>> goMatch (extensionGeneric comb rs s1) as

--     -- | onlyIfMatch's rec helper
--     goMatch :: Stream (Of Int) m r -> [Int] -> m (Maybe [Int])
--     goMatch str as = S.uncons str >>=
--       \case Nothing -> return $ Just as -- end of extension
--             Just (s,str') -> case as of
--               [] -> return Nothing
--               a:rest | s == a -> goMatch str' rest
--                      | otherwise -> return Nothing
-- {-# INLINE resolveGeneric #-}

-- -- | Construct all possible symbols at the head of the given string of
-- -- symbols
-- resolvePrefixes :: PrimMonad m => Rules m -> [Int] -> m [Int]
-- resolvePrefixes = resolveGeneric id withAsFst

-- -- | Construct all possible symbols at the head of a reversed list of
-- -- symbols (i.e. all symbols that end at the tail of the reverse of the
-- -- input list)
-- resolveSuffixes :: PrimMonad m => Rules m -> [Int] -> m [Int]
-- resolveSuffixes = resolveGeneric flip withAsSnd
