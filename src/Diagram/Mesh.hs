{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections, BangPatterns, LambdaCase #-}
module Diagram.Mesh (module Diagram.Mesh) where

import Control.Monad
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

full :: Mesh s -> Bool
full (Mesh _ ss _ _ _ _) = D.full ss

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

-- | While there is free space in the symbol string and the buffer is
-- not the prefix of any potential symbol, append the fully constructed
-- symbols at the head of the buffer to the end of the symbol string
flush :: PrimMonad m => Mesh (PrimState m) -> m (Mesh (PrimState m))
flush msh@(Mesh mdl@(Model rs _ _) ss0 buf0 rsm trie cdts)
  | D.full ss0 = return msh
  | otherwise = go ss0 buf0
                . BS.pack
                . concatMap (R.extension rs)
                =<< D.toList buf0
  where
    go ss buf bs
      | D.full ss || prefixing = -- D.null buf ==> prefixing
          return $ Mesh mdl ss buf rsm trie cdts -- end
      | otherwise = do
          let i = fromJust $ D.head buf
          s <- D.read buf i
          ss' <- fromJust <$> D.trySnoc ss s
          buf' <- D.delete buf i
          let len = R.symbolLength rs s
              bs' = BS.drop len bs
          go ss' buf' bs'
      where
        exts = Trie.keys $ Trie.submap bs trie
        prefixing = not (null exts || exts == [bs])

snoc :: forall m. PrimMonad m =>
        Mesh (PrimState m) -> Sym -> m (Mesh (PrimState m))
snoc (Mesh mdl@(Model rs _ _) ss buf0 rsm trie cdts) s = do
  buf <- go buf0 s
  flush $ Mesh mdl ss buf rsm trie cdts
  where
    go :: Doubly (PrimState m) -> Int -> m (Doubly (PrimState m))
    go buf s1 = (D.last buf >>=) $ \case
      Just s0 | not (null constrs) -> foldM go buf recip01
                                      >>= flip go s01
        where
          s01 = minimum constrs
          recip01 = R.lRecip rs s0 (fst $ rs R.! s01)
          constrs = catMaybes $
                    -- check for a construction between s0 and s1, and
                    (M.lookup (s0,s1) rsm :) $
                    -- check for a construction overriding one in s0...
                    fmap (\suf0 -> let (_,r0) = rs R.! suf0
                                   in M.lookup (r0,s1) rsm
                                      >>= nothingIf (>= suf0)) $
                    -- ...over composite suffixes of s0
                    init $ R.suffixes rs s0

      _else -> D.snoc buf s1

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
