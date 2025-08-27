{-# LANGUAGE TupleSections, BangPatterns #-}
module Diagram.Mesh (module Diagram.Mesh) where

import Control.Monad.Primitive (PrimMonad(PrimState))

import Data.Maybe
import Data.Bifunctor
import qualified Data.List as L
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Data.Trie (Trie)
import qualified Data.Trie as Trie
import qualified Data.ByteString as BS

import Data.Vector.Unboxed.Mutable (MVector)

import qualified Streaming.Prelude as S

import Diagram.Doubly (Index)
import qualified Diagram.Doubly as D
import Diagram.Rules (Rules)
import qualified Diagram.Rules as R
import Diagram.Model (Model(..))
import qualified Diagram.Model as Mdl
import Diagram.Util

type Sym = Int -- symbol
type Doubly s = D.Doubly MVector s Sym

----------
-- MESH --
----------

data Mesh s = Mesh
  !Model               -- ^ String's model :: (rs,n,ks)
  !(Doubly s)          -- ^ Fixed size underlying string :: [Int]
  !(Doubly s)          -- ^ Right buffer of partial constructions :: [Int]
  !(Map (Sym,Sym) Sym) -- ^ Forward rules :: (s0,s1) -> s01
  !(Trie ())           -- ^ Extensions of all symbols :: Set ByteString
  !(Map (Sym,Sym) Int) -- ^ Joint counts (candidates) :: (s0,s1) -> n01

-- | Construction
fromList :: PrimMonad m => Rules -> [Sym] -> m (Mesh (PrimState m))
fromList rs l = do
  ss <- D.fromList l
  buf <- D.new 10 -- could be bigger
  return $ Mesh mdl ss buf rsm trie cdts
  where
    numSymbols = R.numSymbols rs
    mdl = Mdl.fromSymbols rs l
    rsm = R.toMap rs
    trie = Trie.fromList $
           (,()) . BS.pack . R.extension rs <$> [0..numSymbols-1]
    cdts = countJoints l

-- | Compute the loss for each candidate joint and return joints ordered
-- by loss, lowest first, with count.
-- TODO: bookkeep
sortCandidates :: Mesh s -> Double -> [(Double,((Sym,Sym),Int))]
sortCandidates (Mesh mdl _ _ _ _ cdts) scale =
  L.sort $ withLoss <$> M.toList cdts
  where
    withLoss = toFst $ uncurry $ Mdl.scaledInfoDelta scale mdl

-- | Add a rule, rewrite
pushRule :: PrimMonad m => Mesh (PrimState m) -> (Sym,Sym) ->
                           m (Mesh (PrimState m))
pushRule (Mesh mdl ss buf rsm trie cdts) (s0,s1) = do
  ss' <- S.foldM_ (subst1 s01) (return ss) return $
         D.jointIndices ss (s0,s1)
  buf' <- S.foldM_ (subst1 s01) (return buf) return $
          D.jointIndices buf (s0,s1)
  return $ Mesh mdl' ss' buf' rsm' trie' cdts'
  where
    err = error $ "not a candidate: " ++ show (s0,s1)
    (n01,cdts') = first (fromMaybe err) $
                  M.updateLookupWithKey (\_ _ -> Nothing) (s0,s1) cdts
    (s01, mdl'@(Model rs' _ _)) = Mdl.pushRule mdl (s0,s1) n01
    bs01 = R.bytestring rs' s01
    trie' = Trie.insert bs01 () trie
    rsm' = M.insert (s0,s1) s01 rsm

-------------
-- HELPERS --
-------------

-- | Substitute the symbol at the given index and the next with the
-- given symbol
subst1 :: PrimMonad m => Sym -> Doubly (PrimState m) -> Index ->
                         m (Doubly (PrimState m))
subst1 s01 l i = D.modify l (const s01) i >>
                 D.next l i >>= D.delete l

countJoints :: [Int] -> Map (Sym,Sym) Int
countJoints [] = M.empty
countJoints (s0:ss) = countJoints_ M.empty s0 ss

-- | Count the joints in a list given the map of counts and the previous
-- symbol
countJoints_ :: Map (Sym,Sym) Int -> Sym -> [Sym] -> Map (Sym,Sym) Int
countJoints_ !m _ [] = m
countJoints_ !m s0 [s1] = M.insertWith (+) (s0,s1) 1 m
countJoints_ !m s0 (s1:s2:ss)
  | s0 == s1 && s1 == s2 = countJoints_ m' s2 ss
  | otherwise = countJoints_ m' s1 (s2:ss)
  where m' = M.insertWith (+) (s0,s1) 1 m
