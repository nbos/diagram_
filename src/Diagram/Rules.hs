{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- | Construction rules
module Diagram.Rules (module Diagram.Rules) where

import Prelude

import Control.Exception (assert)

import Data.Word (Word8)
import Data.Tuple.Extra
import qualified Data.ByteString as BS
import qualified Data.ByteString.UTF8 as UTF8
import qualified Data.Vector.Unboxed as U
import qualified Data.Vector.Generic as V

import Diagram.Head (Head)
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
toString :: Rules -> Int -> String
toString = UTF8.toString
           . BS.pack
           . fmap fromIntegral
           .: extension

resolveBwd' :: Rules -> [Int] -> [Int]
resolveBwd' _ [] = []
resolveBwd' rs (s:_) = case invLookup rs s of
  Nothing -> [s]
  Just (_, sB) -> [sB, s]

resolveFwd' :: Rules -> [Int] -> [Int]
resolveFwd' rs ss = case fst $ splitHeadFwd rs ss of
  [] -> []
  (pp:rest) -> maybe pp snd (invLookup rs pp) : rest

-- | Take symbols from a list as long as they construct with the
-- accumulated head, starting with the target of the first symbol
splitHeadFwd :: Rules -> [Int] -> ([Int],[Int])
splitHeadFwd _ [] = ([],[])
splitHeadFwd rs (pp:ss0) = let (hd0,tl0) = go s0 ss0
                           in (pp:hd0,tl0)
  where
    s0 = maybe pp snd $ invLookup rs pp
    go _ [] = ([],[])
    go sA (s:ss) | Just (sA',_) <- invLookup rs s
                 , sA == sA' = let (hd,tl) = go s ss
                               in (s:hd, tl)
                 | otherwise = ([], s:ss)

-- | Take the first symbol and all its following prefixes (large to
-- small) from a reversed list of predictions, down to the pp
splitHeadBwd :: Rules -> [Int] -> ([Int],[Int])
splitHeadBwd _ [] = ([],[])
splitHeadBwd rs (s0:ss0) = let (hd0,tl0) = go s0 ss0
                           in (s0:hd0, tl0)
  where go _ [] = ([],[])
        go s (sA':ss) = case invLookup rs s of
          Nothing -> ([], sA':ss) -- atomic, s is pp
          Just (sA,_)
            | sA' == sA -> let (hd,tl) = go sA ss
                           in (s:hd, tl)
            | otherwise ->
                assert ((snd <$> invLookup rs sA') == Just s)
                ([sA'], ss) -- sA' is pp

-- | Return the constructive interval between two symbols, assuming the
-- first is a prefix of the second. The result is guaranteed to start
-- with lo and end with hi, like a range.
consInterval :: Rules -> Int -> Int -> [Int]
consInterval rs lo hi = go hi [hi]
  where
    go s acc | s == lo = acc
             | otherwise = case invLookup rs s of
                 Nothing -> error $ "not an interval: " ++ show (lo,hi)
                 Just (sA,_) -> go sA $ sA:acc

-- | Given a symbol and its predecessor prediction (pp), return the
-- chunked extension of the symbol in a string with the given rule
-- set. This is equivalent to the constructive interval from the target
-- part of the pp and the symbol (inclusive), with pp in the head
-- instead.
consExtension :: Rules -> Int -> Int -> [Int]
consExtension rs s pp = pp : tail consIl
  where
    ppTgt = maybe pp snd $ invLookup rs pp
    consIl = consInterval rs ppTgt s

extLen :: Rules -> Int -> Int -> Int
extLen = length .:. consExtension

-- | Unpack an interval representation of a head into the list of
-- constructions, in reverse (from large to small), including both
-- bounds
unpack :: Rules -> Head -> [Int]
unpack rs (sMin,sMax) = takeUntil (== sMin) $
                        prefixes rs sMax

-- | Given a ruleset and a new rule, rewrite a string represented as a
-- list of heads into a list of equal size with Nothing's in the place
-- of deleted heads.
apply :: Rules -> (Int,Int) -> Int -> Int -> [Head] -> [Maybe Head]
apply rs (s0,s1) s01 pp = case invLookup rs pp of
  -- Case: pp is atomic and necessarily begins h1. No overlap between h0
  -- and h1.
  Nothing -> go2 f
    where f h0 h1 = (snd h0 == s0
                     || (snd <$> (rs !? snd h0)) == Just s0)
                    && fst h1 == pp
                    && s1 `elem` prefixes rs (snd h1)

  -- Case: pp ends h0, right after s0. Symbol `snd pp` begins h1.
  Just (ppA,_) | ppA == s0 -> go2 f
    where f h0 h1 = snd h0 == pp
                    && fst h0 /= pp
                    && s1 `elem` prefixes rs (snd h1)

  -- Case: pp begins h1 where s1 is not exercised but only produced by
  -- pp, i.e. the presence of pp implies the presence of s1.
  Just (_,ppB) | ppB == s1 -> go2 f
    where f h0 h1 = snd h0 == s0
                    && fst h1 == pp

  -- Case: pp is in a singleton head overlapping both h0 and h1.
  Just _ -> go3 f
    where f h0 ih h1 = snd h0 == s0
                       && ih == (pp,pp)
                       && s1 `elem` prefixes rs (snd h1)
  where
    go2 f = go
      where
        go [] = []
        go [h] = [Just h]
        go (h0:h1:hs)
          | f h0 h1 = Just h0' : (if null rh1B then Nothing : go hs
                                  else go (h1':hs))
          | otherwise = Just h0 : go (h1:hs)
            where
              (rh1B,_) = span (/= s1) $ unpack rs h1 -- large to small
              h0' = s01 <$ h0 -- push s01
              h1' = (last rh1B, head rh1B) -- pack

    go3 f = go
      where
        go [] = []
        go [h] = [Just h]
        go [h0,h1] = Just <$> [h0,h1]
        go (h0:ih:h1:hs)
          | f h0 ih h1 = Just h0' : Nothing :
                         (if null rh1B then Nothing : go hs
                          else go (h1':hs))
          | otherwise = Just h0 : go (ih:h1:hs)
            where
              (rh1B,_) = span (/= s1) $ unpack rs h1 -- large to small
              h0' = s01 <$ h0 -- push s01
              h1' = (last rh1B, head rh1B) -- pack
