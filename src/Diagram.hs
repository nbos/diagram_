{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}

module Diagram (module Diagram) where

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
isSingleton :: Head -> Bool
isSingleton = uncurry (==)

-- | Project into the symbol if there is only one
getSingle :: Head -> Maybe Int
getSingle (pMin,pMax) | pMin == pMax = Just pMin
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
listCandidates rs (h0:h1:heads) = case getSingle h0 of
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

countCandidates :: Rules -> [Head] -> Map (Int,Int) Int
countCandidates = L.foldl' f M.empty .: listCandidates
  where f m k = M.insertWith (+) k 1 m

-- | Given a ruleset and a new rule, rewrite a string represented as a
-- list of heads and count the delta in candidates, returned in a map of
-- delta counts (positive or negative, non-zero)
update :: Rules -> (Int,Int) -> Int -> Int -> [Head] ->
          (Map (Int,Int) Int, [Head])
update rs s0s1 s01 pp hs = ( M.filter (/= 0) $ M.unionsWith (+) ms
                           , catMaybes mhs)
  where
    mhs = applyConstr rs s0s1 s01 pp hs
    chunks = deltaChunks [] $ zip hs mhs
    ms = (<$> chunks) $ \c ->
      let (shs,shs') = second catMaybes $ unzip c
          cs = countCandidates rs shs
          cs' = countCandidates rs shs'
      in M.filter (/= 0) $ M.unionWith (+) ((0-) <$> cs) cs'

    deltaChunks _ [] = []
    deltaChunks bwd (a:rest)
      | Just (fst a) == snd a = deltaChunks (a:bwd) rest
      | otherwise = let (as,bs) = first (a:) $ splitAfter2Eq rest
                    in as : deltaChunks (reverse as ++ bwd) bs

    splitAfter2Eq [] = ([],[])
    splitAfter2Eq [a] = ([a],[])
    splitAfter2Eq (a0:a1:rest)
      | Just (fst a0) == snd a0
      , Just (fst a1) == snd a1 = ([a0,a1], rest)
      | otherwise = let (as,bs) = splitAfter2Eq (a1:rest)
                    in (a0:as, bs)

-- | Given a ruleset and a new rule, rewrite a string represented as a
-- list of heads into a list of equal size with Nothing's in the place
-- of deleted heads.
applyConstr :: Rules -> (Int,Int) -> Int -> Int -> [Head] -> [Maybe Head]
applyConstr rs (s0,s1) s01 pp = case R.invLookup rs pp of
  -- Case: pp is atomic and necessarily begins h1. No overlap between h0
  -- and h1.
  Nothing -> go2 f
    where f h0 h1 = (snd h0 == s0
                     || (snd <$> (rs R.!? snd h0)) == Just s0)
                    && fst h1 == pp
                    && s1 `elem` R.prefixes rs (snd h1)

  -- Case: pp ends h0, right after s0. Symbol `snd pp` begins h1.
  Just (ppA,_) | ppA == s0 -> go2 f
    where f h0 h1 = snd h0 == pp
                    && fst h0 /= pp
                    && s1 `elem` R.prefixes rs (snd h1)

  -- Case: pp begins h1 where s1 is not exercised but only produced by
  -- pp, i.e. the presence of pp implies the presence of s1.
  Just (_,ppB) | ppB == s1 -> go2 f
    where f h0 h1 = snd h0 == s0
                    && fst h1 == pp

  -- Case: pp is in a singleton head overlapping both h0 and h1.
  Just _ -> go3 f
    where f h0 ih h1 = snd h0 == s0
                       && ih == (pp,pp)
                       && s1 `elem` R.prefixes rs (snd h1)
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
