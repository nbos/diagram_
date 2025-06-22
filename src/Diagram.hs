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
import Diagram.Model (Model)
import qualified Diagram.Model as Mdl

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

listCandidates :: Rules -> [Head] -> [Joint]
listCandidates _ [] = []
listCandidates _ [_] = []
listCandidates rs (h0:h1:heads)
  | uncurry (/=) h0 = let ctx = snd h0
                          (octx,_) = rs R.! ctx
                      in go octx ctx (h1:heads)

  | uncurry (/=) h1 = let ctx = snd h1
                          (octx,_) = rs R.! ctx
                          ps1 = takeUntil (== fst h1) (R.prefixes rs ctx)
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
        ps = takeWhile (/= fst h) $ R.prefixes rs $ snd h
        (left, right) = case R.invLookup rs (fst h) of
          Nothing -> (ctx, ps) -- no overlap
          Just (sA,_) -> (octx, sA:ps) -- overlap

countCandidates :: Rules -> [Head] -> Map (Int,Int) Int
countCandidates = L.foldl' f M.empty .: listCandidates
  where f m k = M.insertWith (+) k 1 m

substituteWith :: Rules -> (Int,Int) -> Int -> Int -> [[Int]] -> [[Int]]
substituteWith _ _ _ _ [] = []
substituteWith rs (s0,s1) s01 pp (h0:hs0) = case R.invLookup rs pp of
  Nothing -> goA
  Just (ppA,ppB) -> goC
  where
    -- pp atomic, last head0 * elem head1 => head0'
    goA = undefined
    -- pp composite
    goC = undefined
