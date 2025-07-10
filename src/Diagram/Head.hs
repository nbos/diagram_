{-# LANGUAGE TupleSections #-}
module Diagram.Head (module Diagram.Head) where

import Data.Tuple.Extra (dupe)
import qualified Data.List as L
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

import Diagram.Rules (Rules)
import qualified Diagram.Rules as R
import Diagram.Util

type Symbol = Int
-- | A pair of symbols appearing immediately after one another
type Joint = (Symbol,Symbol)

-- | Isomorphic to a list of successive predictions where each
-- subsequent prediction is predicated on the last:
-- (((((x,x),x),x),x),x), etc.
type Head = (Int,Int)

fromAtoms :: [Int] -> [Head]
fromAtoms = fmap dupe

-- | Return @True@ iff the constructive interval begins and ends on the
-- same symbol
isSingleton :: Head -> Bool
isSingleton = uncurry (==)

-- | Project into the symbol if there is only one
getSingle :: Head -> Maybe Int
getSingle (pMin,pMax) | pMin == pMax = Just pMin
                      | otherwise = Nothing

-- | Unpack an interval representation of a head into the list of
-- constructions, in reverse (from large to small), including both
-- bounds
unpack :: Rules -> Head -> [Int]
unpack rs (sMin,sMax) = takeUntil (== sMin) $
                        R.prefixes rs sMax

enumerateJoints :: Rules -> [Head] -> [Joint]
enumerateJoints _ [] = []
enumerateJoints _ [_] = []
enumerateJoints rs (h0:h1:heads) = case getSingle h0 of
  Nothing -> let ctx = snd h0
                 (octx,_) = rs R.! ctx
             in go octx ctx (h1:heads)
  Just s0 -> case getSingle h1 of
    Nothing -> let ctx = snd h1
                   (octx,_) = rs R.! ctx
                   ps1 = unpack rs h1
               in ((s0,) <$> ps1) ++ go octx ctx (h1:heads)
    Just s1 -> (s0,s1) : go s0 s1 heads
  where
    go :: Int -> Int -> [(Int,Int)] -> [(Int, Int)]
    go _ _ [] = []
    go octx ctx (h:hs) = [ (a,b) | a <- left, b <- right ]
                         ++ go octx' (snd h) hs
      where
        octx' | isSingleton h = ctx
              | otherwise = fst $ rs R.! snd h
        ps = unpack rs h
        (left, right)
          | Just (sA,_) <- rs R.!? fst h = ([octx], sA:ps)
          | Just (_,ctxB) <- rs R.!? ctx = ([ctx,ctxB], ps)
          | otherwise = ([ctx], ps)

countJoints :: Rules -> [Head] -> Map (Int,Int) Int
countJoints = L.foldl' f M.empty .: enumerateJoints
  where f m k = M.insertWith (+) k 1 m
