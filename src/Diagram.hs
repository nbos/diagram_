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
import Streaming
import qualified Streaming.Prelude as S

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
    go octx ctx (h:hs) = [ (a,b) | a <- left, b <- right ]
                         ++ go octx' (snd h) hs
      where
        octx' = if uncurry (==) h then ctx else fst (rs R.! snd h)
        ps = unpack rs h
        (left, right) = case R.invLookup rs (fst h) of
          Nothing -> -- no overlap
            case R.invLookup rs ctx of
              Nothing -> ([ctx], ps)
              Just (_,ctxB) -> ([ctx,ctxB], ps)
          Just (sA,_) -> ([octx], sA:ps) -- overlap

countCandidates :: Rules -> [Head] -> Map (Int,Int) Int
countCandidates = L.foldl' f M.empty .: listCandidates
  where f m k = M.insertWith (+) k 1 m

substituteWith :: Rules -> (Int,Int) -> Int -> Int -> [Head] -> [Head]
substituteWith rs (s0,s1) s01 pp = case R.invLookup rs pp of
  -- Case: pp is atomic and necessarily begins h1. No overlap between h0
  -- and h1.
  Nothing -> go
    where go [] = []
          go [h] = [h]
          go (h0:h1:hs) | snd h0 == s0
                        , fst h1 == pp
                        , s1 `elem` R.prefixes rs (snd h1) = h0':go hs'
                        | otherwise = h0:go (h1:hs)
            where
              (rh1B,_) = span (/= s1) $ unpack rs h1 -- large to small
              h0' = s01 <$ h0 -- push s01
              h1' = (last rh1B, head rh1B)
              hs' = if null rh1B then hs else h1':hs

  -- Case: pp ends h0, right after s0. Symbol `snd pp` begins h1.
  Just (ppA,_) | ppA == s0 -> go
    where go [] = []
          go [h] = [h]
          go (h0:h1:hs) | snd h0 == pp
                        , fst h0 /= pp
                        , s1 `elem` R.prefixes rs (snd h1) = h0':go hs'
                        | otherwise = h0:go (h1:hs)
            where
              (rh1B,_) = span (/= s1) $ unpack rs h1 -- large to small
              h0' = s01 <$ h0 -- push s01
              h1' = (last rh1B, head rh1B)
              hs' = if null rh1B then hs else h1':hs

  -- Case: pp begins h1 where s1 is not exercised but only produced by
  -- pp, i.e. the presence of pp implies the presence of s1.
  Just (_,ppB) | ppB == s1 -> go
    where go [] = []
          go [h] = [h]
          go (h0:h1:hs) | snd h0 == s0
                        , fst h1 == pp = h0':go hs'
                        | otherwise = h0:go (h1:hs)
            where
              rh1B = init $ unpack rs h1 -- large to small
              h0' = s01 <$ h0 -- push s01
              h1' = (last rh1B, head rh1B)
              hs' = if null rh1B then hs else h1':hs

  -- Case: pp is in a singleton head overlapping both h0 and h1.
  Just _ -> go
    where go [] = []
          go [h] = [h]
          go [h0,h1] = [h0,h1]
          go (h0:ih:h1:hs) | snd h0 == s0
                           , ih == (pp,pp) -- singleton
                           , s1 `elem` R.prefixes rs (snd h1) = h0':go hs'
                           | otherwise = h0:go (ih:h1:hs)
            where
              (rh1B,_) = span (/= s1) $ unpack rs h1 -- large to small
              h0' = s01 <$ h0 -- push s01
              h1' = (last rh1B, head rh1B)
              hs' = if null rh1B then hs else h1':hs

------------------------------------------------------------------------

update :: Rules -> (Int,Int) -> Int -> Int -> Int -> [Head] ->
          (Map (Symbol,Symbol) Int, [Head])
update rs (s0,s1) s01 pp n = swap . S.lazily . runIdentity . S.toList .
  case R.invLookup rs pp of
    -- Case: pp is atomic and necessarily begins h1. No overlap between
    -- h0 and h1.
    Nothing -> go [] m0
      where
        ms0B = maybe [] ((:[]) . snd) $ rs R.!? s0
        m0 = M.fromList [ ((a,b),-n) | a <- s0:ms0B
                                     , b <- unpack rs (pp,s1) ]
        go _ m [] = return m
        go _ m [h] = S.yield h >> return m
        go bwd m (h0:h1:hs) | snd h0 == s0
                            , fst h1 == pp
                            , s1 `elem` R.prefixes rs (snd h1) =
                                S.yield h0' >>
                                go (h0':bwd) m hs'
                            | otherwise =
                                S.yield h0 >>
                                go (h0:bwd) m (h1:hs)
          where
            (rh1B,_) = span (/= s1) $ unpack rs h1 -- large to small
            h0' = s01 <$ h0 -- push s01
            h1' = (last rh1B, head rh1B)
            hs' = if null rh1B then hs else h1':hs


    -- Case: pp ends h0, right after s0. Symbol `snd pp` begins h1.
    Just (ppA,_) | ppA == s0 -> go [] m0
      where
        (_, ppB) = rs R.! pp
        les1 = unpack rs (ppB, s1)
        (_,h11B) = rs R.! (les1 !! 1)
        m0 = M.fromList $ (,-n) <$> (pp, h11B) : ((s0,) <$> les1)

        go _ m [] = return m
        go _ m [h] = S.yield h >> return m
        go bwd m (h0:h1:hs) | snd h0 == pp
                            , fst h0 /= pp
                            , s1 `elem` R.prefixes rs (snd h1) =
                                S.yield h0' >>
                                go (h0':bwd) m hs'
                            | otherwise =
                                S.yield h0 >>
                                go (h0:bwd) m (h1:hs)
          where
            (rh1B,_) = span (/= s1) $ unpack rs h1 -- large to small
            h0' = s01 <$ h0 -- push s01
            h1' = (last rh1B, head rh1B)
            hs' = if null rh1B then hs else h1':hs

    -- Case: pp begins h1 where s1 is not exercised but only produced by
    -- pp, i.e. the presence of pp implies the presence of s1.
    Just (_,ppB) | ppB == s1 -> go [] m0
      where
        (s0A, s0B) = rs R.! s0
        m0 = M.fromList $ (,-n) <$> [(s0A,pp),(s0,s1),(s0B,s1)]

        go _ m [] = return m
        go _ m [h] = S.yield h >> return m
        go bwd m (h0:h1:hs) | snd h0 == s0
                            , fst h1 == pp =
                                S.yield h0' >>
                                go (h0':bwd) m hs'
                            | otherwise =
                                S.yield h0 >>
                                go (h0:bwd) m (h1:hs)
          where
            rh1B = init $ unpack rs h1 -- large to small
            h0' = s01 <$ h0 -- push s01
            h1' = (last rh1B, head rh1B)
            hs' = if null rh1B then hs else h1':hs

    -- Case: pp is in a singleton head overlapping both h0 and h1.
    Just _ -> go [] m0
      where
        (s0A,s0B) = rs R.! s0
        (_,ppB) = rs R.! pp
        les1 = unpack rs (ppB, s1)
        (_,h11B) = rs R.! (les1 !! 1)
        m0 = M.fromList $ (,-n) <$> (s0A,pp):(pp,h11B):
             [ (a,b) | a <- [s0,s0B], b <- les1 ]

        go _ m [] = return m
        go _ m [h] = S.yield h >> return m
        go _ m [h0,h1] = S.yield h0 >> S.yield h1 >> return m
        go bwd m (h0:ih:h1:hs) | snd h0 == s0
                               , ih == (pp,pp) -- singleton
                               , s1 `elem` R.prefixes rs (snd h1) =
                                   S.yield h0' >>
                                   go (h0':bwd) m hs'
                               | otherwise =
                                   S.yield h0 >>
                                   go (h0:bwd) m (ih:h1:hs)
          where
            (rh1B,_) = span (/= s1) $ unpack rs h1 -- large to small
            h0' = s01 <$ h0 -- push s01
            h1' = (last rh1B, head rh1B)
            hs' = if null rh1B then hs else h1':hs
