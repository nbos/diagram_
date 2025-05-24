{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}

module Diagram (module Diagram) where

import Control.Exception (assert)
import Control.Lens hiding (pre)
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

      -- inc anything greater than current
      sequence_ [ inc m i s0 s1 | s0 <- ctxGE
                                , s1 <- tgtGE
                                , (Just s0, s1) /= (minCtx,tgt) ]

      go m i' maxHead pdns' -- continue

        where
          -- filter (ctx <=) (maxCtxB:[maxCtx])
          ctxGE = maybe id (filter . (<=)) minCtx $
                  maybe id ((:) . snd) (R.invLookup rs maxCtx) -- FIXME /!\
                  [maxCtx]
            -- case R.invLookup rs maxCtx of
            -- Nothing -> [maxCtx]
            -- Just (_, maxCtxB) -> case ctx of
            --   Nothing -> [maxCtxB, maxCtx]
            --   Just ctxS | ctxS == maxCtxB -> [maxCtxB, maxCtx]
            --                | ctxS == maxCtx -> [maxCtx]
            --                | otherwise -> err "impossible"

          maxHead = R.maxHead rs tgt rest
          tgtGE = takeUntil (== tgt) $
                  R.prefixes rs maxHead

          headLen = length tgtGE
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
updateCandidates rs n (s0,s1) pp = flip go []
  where
    dec :: STRef s Candidates -> Int -> Int -> ST s ()
    dec ref s0 s1 = undefined

    -- 2) add candidates GT (s0,s1)
    go m bwd fwd = case break (== pp) fwd of
      (gap, []) -> (m, reverse bwd ++ gap) -- end
      (gap, _pp:fwd') -> assert (_pp == pp) $ case (bwd', geS1) of
        (prev:_, _s1:gtS1) -> assert (_s1 == s1) $ case prev of
          (Nothing, s) | s == s0 -> matched
                       | otherwise -> noMatch

          (Just sA, sB) | sB == s0 -> matched
                        | s <- R.constr rs prev
                        , s == s0 -> matched
                        | otherwise -> noMatch
          where
            (headRest,fwd'') = splitAt (length gtS1) fwd'
            bwd'' = revAppend headRest $
                    (Just s0, s1):bwd'

            maxCtx = R.constr rs prev

            matched = flip2 go bwd'' fwd'' $ runST $ do
              ref <- newSTRef m

              -- update map...

              readSTRef ref

            -- filter (fst pp <=) (snd prev:[maxCtx])
            ctxGE = maybe id (filter . (<=)) (fst pp) $
                    ---------- FIXME ----------
                    (if isJust (fst prev) then (snd prev:) else id)
                    [maxCtx]

        _noPrevOrNoS1 -> noMatch

        where
          noMatch = go m (pp:bwd') fwd' -- move by whole head?

          bwd' = revAppend gap bwd
          maxHead = R.maxHead rs (snd pp) fwd'

          -- [ppTgt, ..., s1?, ..., maxHead]
          constrs = dropWhile (/= snd pp) $
                    reverse $ -- small to large
                    R.prefixes rs maxHead

          -- [ppTgt, ...][s1, ..., maxHead]
          (ltS1,geS1) = break (== s1) constrs
