{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Diagram (module Diagram) where

-- import Control.Exception (assert)

-- import Control.Monad
import Control.Lens
import Control.Monad.State.Strict
import Control.Monad.Primitive (PrimMonad)

-- import Data.Bifunctor

-- import Data.Word
import qualified Data.List as L
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IM
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
-- import Data.ByteString (ByteString)
-- import qualified Data.ByteString as BS

-- import Streaming
import qualified Streaming.Prelude as S
-- import qualified Diagram.Streaming as S

import qualified Diagram.Rules as R
import Diagram.Model (Model(..))
import qualified Diagram.Model as Mdl
-- import qualified Diagram.Trie as Trie
import Diagram.Util

err :: [Char] -> a
err = error . ("Diagram: " ++)

type Search m = StateT (SearchState m) m
data SearchState m = Search {
  _sModel :: !(Model m),
  _sTargets :: ![Int],

  -- | We can keep track of all the edges that would be eliminated from a
  -- new rule (s0,s1) by counting the number of times each construction
  -- prefix (c-prefix) of s1 (from itself down to the first atom of its
  -- extension) is introduced how many times by an extension suffix
  -- (e-suffix) of s0.
  _sCandidates :: !(Map (Int,Int) (IntMap Int)) -- (s0,s1) -> pre1 -> n
}
makeLenses ''SearchState

-- | Construction
fromString :: PrimMonad m => [Int] -> m (SearchState m)
fromString ss = do
  mdl <- Mdl.singleton counts
  -- ctxs <- forM ss $ DMV.read $ mdl^.modelKeys
  -- let events = (BS.empty, hd) : zip ctxs tl
  return $ Search mdl ss candidates
  where
    counts = L.foldl' (\m s -> IM.insertWith (+) s 1 m) IM.empty ss
    candidates = M.mapWithKey (\(_,s1) n -> IM.singleton s1 n) $
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

type Prediction = (Maybe Int, Int)
type Candidates = Map (Int,Int) (IntMap Int)

updateCandidates :: forall m. PrimMonad m => Int -> (Int, Int) ->
                    Model m -> [Prediction] -> Candidates ->
                    m ([Prediction], Candidates)
updateCandidates s01 (s0,s1) mdl@(Model rs _ _ctxTrie) = go []
  where
    eMatch = Mdl.eMatchRev mdl
    cMatch = Mdl.cMatchRev mdl

    go :: [Prediction] -> [Prediction] ->
          Candidates -> m ([Prediction], Candidates)
    go bwd [] = return . (reverse bwd, )
    go bwd (pr@(_ctx,_s):fwd) = \m -> cMatch s1 (snd <$> bwd') >>= \case

      Nothing -> eMatch s01 (snd <$> bwd') >>= \case
        Nothing -> doesntMatch m
        Just _ -> matchesAsCtx m

      Just (cPref1, bwdRest) -> eMatch s0 bwdRest >>= \case
        Nothing -> doesntMatch m

        -- s0 ext, s1 cons. match: ensure no claim supersedes s0's
        Just _bwdAtoms -> do
          let _lenPref1s = length cPref1

          -- bs0 <- Mdl.ctxKey mdl s0
          -- let len0 = BS.length bs0
          -- (hd, msts, tl) <- Trie.resolveGeneric bs0 ctxTrie bwdAtoms
          -- let revRest' = S.each (L.drop len0 $ BS.unpack hd) >> tl
          -- case L.find (flip Mdl.claims s1 . snd) $ reverse msts of
          --   Nothing -> findErr msts
          --   Just (Just s', _) | s' > s0 -> matchesAsCtx m
          --   Just (claimant, _) -> do
          
          undefined -- TODO

      where
        doesntMatch = go bwd' fwd
        matchesAsCtx _m = undefined -- TODO
        
        bwd' = pr:bwd 

        _fwdAtoms = S.mapM_ (R.extension rs) undefined -- $ S.each fwd

        _findErr lin = err $ "updateCandidates: Can't find symbol "
          ++ show s1 ++ " in context lineage: " ++ show lin

