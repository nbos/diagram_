{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}

module Diagram (module Diagram) where

import Control.Lens hiding (pre)
import Control.Monad.ST

import Data.STRef
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

type Candidates = Map (Int,Int) ((Maybe Int, Int), Int)

-- | Augment a predecessor prediction map into a full "Candidates" map
-- by counting all possible constructions from the list of
-- predictions. This is not part of the search algorithm but defines the
-- invariant preserved when counts are updated by a pass over the string
-- after a rule introduction
fromPredictions :: Map (Int,Int) (Maybe Int, Int) -> Rules ->
                   [(Maybe Int, Int)] -> Candidates
fromPredictions pps _ [] = (,0) <$> pps
fromPredictions _ _ ((Just _,_):_) = err "impossible"
fromPredictions pps rs ((Nothing,ctx0):pdns) = runST $ do
  m <- newSTRef $ (minBound :: Int,) . (,0) <$> pps
  go m 0 ctx0 pdns
  snd <<$>> readSTRef m -- discard idxs
  where
    -- | increment by 1 each from the cartesian product of symbols to
    -- the left greater or equal to the current context and symbols to
    -- the right greater or equal to the current target except the
    -- current pairing (minCtx,tgt)
    go :: STRef s (Map (Int,Int) (Int, ((Maybe Int,Int), Int))) ->
          Int -> Int -> [(Maybe Int,Int)] -> ST s ()
    go _ _ _ [] = return () -- end
    go m i maxCtx ((minCtx,tgt):rest) = do
      sequence_ [ inc m i s0 s1 | s0 <- left
                                , s1 <- right
                                , Just s0 /= minCtx || s1 /= tgt ]

      go m i' maxHead pdns' -- continue

        where
          -- filter (minCtx <=) (maxCtxB:[maxCtx])
          left = maybe id (filter . (<=)) minCtx $
                 maybe id ((:) . snd) (R.invLookup rs maxCtx)
                 [maxCtx]
            -- case R.invLookup rs maxCtx of
            -- Nothing -> [maxCtx]
            -- Just (_, maxCtxB) -> case minCtx of
            --   Nothing -> [maxCtxB, maxCtx]
            --   Just minCtxS | minCtxS == maxCtxB -> [maxCtxB, maxCtx]
            --                | minCtxS == maxCtx -> [maxCtx]
            --                | otherwise -> err "impossible"

          maxHead = R.maxHead rs tgt rest
          right = takeUntil (== tgt) $
                  R.prefixes rs maxHead

          headLen = length right
          i' = i + headLen
          pdns' = drop (headLen - 1) rest

    -- | increment (s0,s1) candidate by 1, if constructable
    inc :: STRef s (Map (Int,Int) (Int, ((Maybe Int,Int), Int))) ->
           Int -> Int -> Int -> ST s ()
    inc m i s0 s1 =
      modifySTRef m $
      flip M.adjust (s0,s1) $ \e@(lastChunked,(pp@(_,pre1),n)) ->
      let -- [s1..]pre1 (null iff s1 == pre1)
          inter1 = takeWhile (/= pre1) $ R.prefixes rs s1
          constructable = i - length inter1 > lastChunked
      in if constructable then (i,(pp,n+1)) else e


updateCandidates :: Rules -> Int -> (Int, Int) -> (Maybe Int, Int) ->
                    Candidates -> [(Maybe Int, Int)] ->
                    (Candidates, [(Maybe Int, Int)])
updateCandidates rs s01 (s0,s1) (preCtx,ppp1) cdts pdns = runST $ do
  m <- newSTRef cdts
  pdns' <- go m [] pdns
  cdts' <- readSTRef m
  return (cdts', pdns')
  
  where
    go :: STRef s Candidates -> [(Maybe Int, Int)] ->
          [(Maybe Int, Int)] -> ST s [(Maybe Int, Int)]
    go _ bwd [] = return $ reverse bwd -- end
    go m [] (pdn0:fwd) = go m [pdn0] fwd
    go m bwd@(maxCtx@(ctxA,ctxB):bwdRest) fwd@(next@(minCtx,tgt):fwdRest)
      | match0 && match1 = undefined

      | otherwise = undefined
      where
        -- only two cases match s0: s0 is the previous target or s0 is
        -- the previous prediction (s0B target in the s0A context)
        match0 = ctxB == s0 || case R.invLookup rs s0 of
          Nothing -> False
          Just (s0A,s0B) -> ctxA == Just s0A && ctxB == s0B

        match1 = -- we could compare full (Maybe Int, Int) but targets +
                 -- pp fully determine contexts so it's unnecessary
          (snd <$> fwd1) == pattern1
        
        maxHead = R.maxHead rs tgt fwd --------- might go beyond s1
        
        fwd1 = take len1 fwd
        rightSymbols = R.resolveFwd rs fwdRest

    -- [pre1..s1] (not null)
    pattern1 = assertId (not . null) $
               reverse $
               takeUntil (== ppp1) $
               R.prefixes rs s1

    len1 = length pattern1

