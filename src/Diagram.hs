{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}

module Diagram (module Diagram) where

import Control.Exception (assert)
import Control.Monad.ST

import Data.STRef
import Data.Maybe
import Data.Tuple.Extra
import qualified Data.List as L

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

import Diagram.Rules (Rules)
import qualified Diagram.Rules as R

import Diagram.Util

err :: [Char] -> a
err = error . ("Diagram: " ++)

type Symbol = Int
-- | A pair of symbols appearing immediately after one another
type Joint = (Symbol,Symbol)
-- | Isomorphic to a list of successive predictions where each
-- subsequent prediction is predicated on the last:
-- (((((x,x),x),x),x),x), etc.
type Head = (Symbol,Symbol)

fromAtoms :: [Int] -> [Head]
fromAtoms = fmap dupe

-- | Return @True@ iff the constructive interval begins and ends on the
-- same symbol
single :: Head -> Bool
single = uncurry (==)

-- | Project into the symbol if there is only one
getSingle :: Head -> Maybe Int
getSingle (sMin,sMax) | sMin == sMax = Just sMin
                      | otherwise = Nothing

-- | Unpack an interval representation of a head into the list of
-- constructions, in reverse (from large to small), including both
-- bounds
unpack :: Rules -> Head -> [Symbol]
unpack rs (sMin,sMax) = takeUntil (== sMin) $
                        R.prefixes rs sMax

listCandidates :: Rules -> [Head] -> [Joint]
listCandidates _ [] = []
listCandidates _ [_] = []
listCandidates rs (h0:h1:heads)
  | uncurry (/=) h0 = let ctx = snd h0
                          (octx,_) = rs R.! ctx
                      in go octx ctx (h1:heads)

  | uncurry (/=) h1 = let ctx = snd h1
                          (octx,_) = rs R.! ctx
                          ps1 = unpack rs h1
                      in ((s0,) <$> ps1) ++ go octx ctx (h1:heads)

  | otherwise = (s0,s1) : go s0 s1 heads
  where
    s0 = assert (uncurry (==) h0) $ fst h0 -- h0 singleton
    s1 = assert (uncurry (==) h1) $ fst h1 -- h1 singleton

    go :: Int -> Int -> [(Int,Int)] -> [(Int, Int)]
    go _ _ [] = []
    go octx ctx (h:hs) = ((left,) <$> right) ++ go octx' (snd h) hs
      where
        octx' = if uncurry (==) h then ctx else fst (rs R.! snd h)
        ps = unpack rs h
        (left, right) = case R.invLookup rs (fst h) of
          Nothing -> (ctx, ps) -- no overlap
          Just (sA,_) -> (octx, sA:ps) -- overlap

countCandidates :: Rules -> [Head] -> Map (Int,Int) Int
countCandidates = L.foldl' f M.empty .: listCandidates
  where f m k = M.insertWith (+) k 1 m

substituteWith :: Rules -> (Int,Int) -> Int -> Int -> [Head] -> [Head]
substituteWith rs (s0,s1) s01 pp = case R.invLookup rs pp of
      -- Case: pp is atomic and necessarily begins s1's head
      Nothing -> go2 (\h0 h1 -> snd h0 == s0 && fst h1 == pp)
      -- Case: pp is composite
      Just (ppA,_)
        -- Case: pp follows s0 in its head (pp ends s0's head)
        | ppA == s0 -> go2 (\h0 _ -> snd h0 == pp && fst h0 /= pp)
        -- Case: pp is in a different (third) head than s0 and s1,
        -- between s0's and s1's head
        | otherwise -> go3
  where
    go3 :: [Head] -> [Head]
    go3 [] = []
    go3 [h] = [h]
    go3 [h0,h1] = [h0,h1]
    go3 (h0:ih:h1:hs) | snd h0 == s0
                      , ih == (pp,pp)
                      , s1 `elem` R.prefixes rs (snd h1) =
                          if null rh1B then h0':go3 hs
                          else h0':go3 (h1':hs)
                      | otherwise = h0 : go3 (ih:h1:hs)
          where
            (rh1B,_) = span (/= s1) $ unpack rs h1 -- large to small
            h0' = s01 <$ h0
            h1' = (last rh1B, head rh1B)

    go2 :: (Head -> Head -> Bool) -> [Head] -> [Head]
    go2 cond = go
      where
        go [] = []
        go [h] = [h]
        go (h0:h1:hs) | cond h0 h1
                      , s1 `elem` R.prefixes rs (snd h1) =
                          if null rh1B then h0':go hs
                          else h0':go (h1':hs)
                      | otherwise = h0:go (h1:hs)
          where
            (rh1B,_) = span (/= s1) $ unpack rs h1 -- large to small
            -- h1A = reverse rh1A -- small to large: [pp..s1]
            -- h1B = reverse rh1B -- small to large: s1[..]
            h0' = s01 <$ h0
            h1' = (last rh1B, head rh1B)
