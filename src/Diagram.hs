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

fromAtoms :: [Int] -> [[Int]]
fromAtoms = fmap (:[])

listCandidates :: Rules -> [[Int]] -> [(Int,Int)]
listCandidates _ [] = []
listCandidates rs (h0:hs0)
  | length h0 > 1 = go ctx0A ctx0 hs0
  | otherwise = case hs0 of
      [] -> []
      h1:hs1 | length h1 > 1 -> ((s0,) <$> h1) ++ go ctx1A ctx1 hs1
             | otherwise -> (s0,s1) : go s0 s1 hs1
        where
          s0 = head h0 -- h0 singleton
          s1 = head h1 -- h1 singleton
          ctx1 = last h1
          (ctx1A,_) = rs R.! ctx1
  where
    ctx0 = last h0
    (ctx0A,_) = rs R.! ctx0

    go _ _ [] = []
    go octx ctx (h:hs) = ((left,) <$> right) ++ go octx' pn hs
      where
        p0 = head h
        pn = last h
        octx' = if p0 == pn then ctx else fst (rs R.! pn)
        ps = takeWhile (/= p0) $ R.prefixes rs pn
        (left, right) = case R.invLookup rs p0 of
          Nothing -> (ctx, ps) -- no overlap
          Just (s0,_) -> (octx, s0:ps) -- overlap

countCandidates :: Rules -> [[Int]] -> Map (Int,Int) Int
countCandidates = L.foldl' f M.empty .: listCandidates
  where f m k = M.insertWith (+) k 1 m

substituteWith :: Rules -> (Int,Int) -> Int -> Int -> [[Int]] -> [[Int]]
substituteWith _ _ _ _ [] = []
substituteWith rs (s0,s1) s01 pp (h0:hs0) = undefined
