{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}

module Diagram (module Diagram) where

import Control.Exception (assert)
import Control.Lens hiding (parts)
import Control.Monad.ST

import Data.STRef
import Data.Maybe
import qualified Data.List as L

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import qualified Data.IntMap.Strict as IM

import Diagram.Rules (Rules)
import qualified Diagram.Rules as R
import Diagram.Model (Model)
import qualified Diagram.Model as Mdl

import Diagram.Util

err :: [Char] -> a
err = error . ("Diagram: " ++)

data Search = Search {
  _sModel :: !Model,
  _sTargets :: ![Int],
  _sCandidates :: !(Map (Int,Int) -- (s0,s1) ->
                    ((Maybe Int, Int), Int)) -- ((suf0, pref1), n)
}
makeLenses ''Search

-- | Construction
fromString :: [Int] -> Search
fromString ss =
  let mdl = Mdl.singleton counts
  -- ctxs <- forM ss $ DMV.read $ mdl^.modelKeys
  -- let events = (BS.empty, hd) : zip ctxs tl
  in Search mdl ss candidates
  where
    counts = L.foldl' (\m s -> IM.insertWith (+) s 1 m) IM.empty ss
    candidates = M.mapWithKey (\(_,s1) n -> ((Nothing,s1),n)) $
                 countJoints ss

-- | Linear space traversal of the list with all previous (in reverse)
-- and all following elements
contextual :: [a] -> [([a],a,[a])]
contextual as = zip3 prevs as nexts
  where prevs = revInits as -- [[], [a0], [a1,a0], [a2,a1,a0], ...]
        nexts = tail $ L.tails as

-- | Count the number of times pairs of symbols appear together
countJoints :: [Int] -> Map (Int,Int) Int
countJoints [] = M.empty
countJoints ss@(_:tl) = L.foldl' f M.empty $ zip ss tl
  where f m s0s1 = M.insertWith (+) s0s1 1 m

-- | Given a rule set, a predicate of what is constructable, a reversed
-- list of past predictions, a symbol and a list of future predictions,
-- return a list of predictions that would subsume the one given.
candidatesAt :: Rules -> ((Int,Int) -> Bool) ->
                [Int] -> Int -> [Int] -> [(Int,Int)]
candidatesAt rs f bwd p fwd = [ (c,t) | c <- ctxsGE -- GE ctx
                                      , t <- tgts -- GE tgt
                                      , Just (c,t) /= parts -- not EQ
                                      , f (c,t) ] -- constructable
  where
    tgts = R.resolveFwd' rs fwd
    ctxs = R.resolveBwd' rs bwd
    parts = R.invLookup rs p
    ctxsGE = case parts of
      Nothing -> ctxs
      Just (ctx,_) -> filter (>=ctx) ctxs
    -- neq | Just (c,t) <- parts = (/= (c,t))
    --     | otherwise = const True

type Symbol = Int
type PP = Symbol
type Joint = (Symbol,Symbol)
type Count = Int
type Length = Int
type Candidates = Map Joint (PP, Length, Count)

updateCandidates :: Rules -> Int -> Candidates -> [Int] -> (Candidates, [Int])
updateCandidates rs s01 cs = flip (go 0 []) m0
  where
    -- TODO: do we remove s0s1 before or after?
    m0 = (minBound :: Int, ) <$> cs

    s0s1@(s0,s1) = rs R.! s01
    (pp, len, n) = cs M.! s0s1
    s1Ext = R.consExtension rs pp s1
    s1Len = length s1Ext

    ppParts = R.invLookup rs pp
    filterCtx = maybe id (filter . (<=) . snd) ppParts
    go :: Int -> [Int] -> [Int] -> Map Joint (Int, (PP, Length, Count)) ->
          (Map Joint (PP, Length, Count), [Int])
    go _ bwd [] m = (snd <$> m, reverse bwd)
    go i bwd pfwd@(p:fwd) m
      | s1Fwd == s1Ext -- s1 prefix of head
      , Just i0 <- L.elemIndex s0 ctxs = -- s0 in ctx ({0,1})
          let tgts01 = R.resolveFwd' rs fwd'
              ctxs01 = R.resolveBwd' rs $ drop (i0+1) bwd

              m' = L.foldl' (flip id) m []

          in go (i+s1Len) (s01:bwd) fwd' m'

      | otherwise =
          go (i+1) (p:bwd) fwd m

      where
        constructable :: (Symbol, Symbol) -> Bool
        constructable p = let (lastCons,(_,consLen,_)) = m M.! p
                          in lastCons + consLen <= i

        (s1Fwd,fwd') = splitAt s1Len pfwd
        (s0Bwd,bwd') = R.splitHeadBwd rs bwd

        tgts = R.resolveFwd' rs pfwd
        ctxs = R.resolveBwd' rs bwd
        ctxsGE = filterCtx ctxs

-- dec :: Rules -> [Int] -> Joint -> Candidates -> Candidates
-- dec rs bwd s0s1 =
--   flip M.adjust s0s1 $ \e@(pp,n) ->
--   let -- [s1..](snd pp) (null iff s1 == snd pp)
--       inter1 = takeWhile (/= snd pp) $ R.prefixes rs $ snd s0s1
--       width = length $ takeWhile (/= pp) $ R.prefixes rs $ snd s0s1
--       constructable = i - length inter1 > lastChunked
--   in if constructable then (pp,n-1) else e

type Candidates' = Map (Int,Int) ((Maybe Int, Int), Int)

-- | Augment a predecessor prediction map into a full "Candidates" map
-- by counting all possible constructions from the list of
-- predictions. This is not part of the search algorithm but defines the
-- invariant preserved when counts are updated by a pass over the string
-- after a rule introduction
fromPredictions :: Map (Int,Int) (Maybe Int, Int) -> Rules ->
                   [(Maybe Int, Int)] -> Candidates'
fromPredictions pps _ [] = (,0) <$> pps
fromPredictions _ _ ((Just _,_):_) = err "impossible"
fromPredictions pps rs ((Nothing,ctx0):pdns) = snd <$> go 0 ctx0 pdns m0
  where
    m0 = (minBound :: Int,) . (,0) <$> pps

    -- | increment by 1 each from the cartesian product of symbols to
    -- the left greater or equal to the current context and symbols to
    -- the right greater or equal to the current target except the
    -- current pairing (minCtx,tgt)
    go :: Int -> Int -> [(Maybe Int, Int)] ->
          Map (Int, Int) (Int, ((Maybe Int, Int), Int)) ->
          Map (Int, Int) (Int, ((Maybe Int, Int), Int))
    go _ _ [] m = m
    go i maxCtx ((minCtx,tgt):rest) m = go i' maxHead pdns' m'
        where
          -- filter (ctx <=) (maxCtxB:[maxCtx])
          ctxGE = maybe id (filter . (<=)) minCtx $
                  maybe id ((:) . snd) (R.invLookup rs maxCtx) -- FIXME !!!
                  [maxCtx]

          maxHead = undefined -- R.maxHead rs tgt rest -- FIXME
          tgtGE = takeUntil (== tgt) $
                  R.prefixes rs maxHead

          -- inc anything greater than current
          m' = L.foldl' (flip id) m
               [ inc' rs i s0 s1 | s0 <- ctxGE
                                , s1 <- tgtGE
                                , (Just s0, s1) /= (minCtx,tgt) ]

          headLen = length tgtGE
          i' = i + headLen
          pdns' = drop (headLen - 1) rest

-- | increment (s0,s1) candidate by 1, if constructable
inc' :: Rules -> Int -> Int -> Int ->
        Map (Int,Int) (Int, ((Maybe Int,Int), Int)) ->
        Map (Int,Int) (Int, ((Maybe Int,Int), Int))
inc' rs i s0 s1 =
  flip M.adjust (s0,s1) $ \e@(lastChunked,(pp,n)) ->
  let -- [s1..](snd pp) (null iff s1 == snd pp)
      inter1 = takeWhile (/= snd pp) $ R.prefixes rs s1
      constructable = i - length inter1 > lastChunked
  in if constructable then (i,(pp,n+1)) else e

-- | increment (s0,s1) candidate by 1, if constructable
dec' :: Rules -> Int -> Int -> Int ->
        Map (Int,Int) (Int, ((Maybe Int,Int), Int)) ->
        Map (Int,Int) (Int, ((Maybe Int,Int), Int))
dec' rs i s0 s1 =
  flip M.adjust (s0,s1) $ \e@(lastChunked,(pp,n)) ->
  let -- [s1..](snd pp) (null iff s1 == snd pp)
      inter1 = takeWhile (/= snd pp) $ R.prefixes rs s1
      constructable = i - length inter1 > lastChunked
  in if constructable then (i,(pp,n-1)) else e

updateCandidates' :: Rules -> (Int, Int) -> (Maybe Int, Int) ->
                    Candidates' -> [(Maybe Int, Int)] ->
                    (Candidates', [(Maybe Int, Int)])
updateCandidates' rs (s0,s1) pp = flip (go 0 [])
                                 . fmap (minBound,)
  where
    go _ bwd [] m = (snd <$> m, reverse bwd) -- end
    go i bwd (p:fwd) m
      | p == pp
      , Just is0 <- L.elemIndex s0 ctxs
      , Just is1 <- L.elemIndex s1 tgts =
          let ctxs01 = R.resolveBwd rs $ drop (is0+1) bwd
              tgts01 = R.resolveFwd rs $ drop (is1+1) fwd
              ctxsGE = maybe id (filter . (<=)) (fst pp) ctxs

              m' = L.foldl' (flip id) m $
                   dec' rs i s0 s1 :
                   -- rm candidates GT pp && LE (s0,s1)
                   [ dec' rs i c t | c <- ctxsGE -- ctx GE pp's
                                  , t <- tgts -- tgt GE pp's
                                  , (Just c, t) /= pp -- not EQ
                                  , c < s0 || t < s1 ] -- LT (s0,s1)
                   ++ -- add candidates with s01 as CTX or TGT
                   [ id ] -- FIXME

          in go (i+1) ((Just s0,s1):bwd) fwd m'

      | otherwise =
          go (i+1) (p:bwd) fwd m
      where
        ctxs = R.resolveBwd rs bwd
        tgts = R.resolveFwd rs (pp:fwd)
