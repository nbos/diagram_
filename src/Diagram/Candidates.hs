{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
module Diagram.Candidates (module Diagram.Candidates) where

import Data.Maybe
import Data.Tuple.Extra
import qualified Data.List as L
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

import Diagram.Head (Head)
import qualified Diagram.Head as H
import Diagram.Rules (Rules)
import qualified Diagram.Rules as R
import Diagram.Util

err :: [Char] -> a
err = error . ("Diagram: " ++)

type Symbol = Int
-- | A pair of symbols appearing immediately after one another
type Joint = (Symbol,Symbol)

enumerate :: Rules -> [Head] -> [Joint]
enumerate _ [] = []
enumerate _ [_] = []
enumerate rs (h0:h1:heads) = case H.getSingle h0 of
  Nothing -> let ctx = snd h0
                 (octx,_) = rs R.! ctx
             in go octx ctx (h1:heads)
  Just s0 -> case H.getSingle h1 of
    Nothing -> let ctx = snd h1
                   (octx,_) = rs R.! ctx
                   ps1 = R.unpack rs h1
               in ((s0,) <$> ps1) ++ go octx ctx (h1:heads)
    Just s1 -> (s0,s1) : go s0 s1 heads
  where
    go :: Int -> Int -> [(Int,Int)] -> [(Int, Int)]
    go _ _ [] = []
    go octx ctx (h:hs) = [ (a,b) | a <- left, b <- right ]
                         ++ go octx' (snd h) hs
      where
        octx' | H.isSingleton h = ctx
              | otherwise = fst $ rs R.! snd h
        ps = R.unpack rs h
        (left, right)
          | Just (sA,_) <- rs R.!? fst h = ([octx], sA:ps)
          | Just (_,ctxB) <- rs R.!? ctx = ([ctx,ctxB], ps)
          | otherwise = ([ctx], ps)

count :: Rules -> [Head] -> Map (Int,Int) Int
count = L.foldl' f M.empty .: enumerate
  where f m k = M.insertWith (+) k 1 m

-- | Given a ruleset and a new rule, rewrite a string represented as a
-- list of heads and count the delta in candidates, returned in a map of
-- delta counts (positive or negative, non-zero)
applyRule :: Rules -> (Int,Int) -> Int -> Int -> [Head] -> ( Map (Int,Int) Int
                                                           , [Head] )
applyRule rs s0s1 s01 pp hs = ( M.filter (/= 0) $ M.unionsWith (+) ms
                              , catMaybes mhs )
  where
    mhs = R.apply rs s0s1 s01 pp hs
    chunks = deltaChunks [] $ zip hs mhs
    ms = (<$> chunks) $ \c ->
      let (shs,shs') = second catMaybes $ unzip c
          cs = count rs shs
          cs' = count rs shs'
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
