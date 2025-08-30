{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections, BangPatterns, LambdaCase #-}
module Diagram.Mesh (module Diagram.Mesh) where

import Control.Monad
import Control.Monad.Primitive

import Data.Maybe
import Data.Bifunctor
import qualified Data.List as L
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Data.Trie (Trie)
import qualified Data.Trie as Trie
import qualified Data.ByteString as BS
import Data.Vector.Unboxed.Mutable (MVector)

import Streaming
import qualified Streaming.Prelude as S
import Diagram.Streaming ()

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

data Mesh s = Mesh {
  model :: !Model, -- ^ String's model :: (rs,n,ks)
  string :: !(Doubly s), -- ^ Fixed size underlying string
  parity :: !Bool,  -- ^ Number of times last symbol is repeated
  buffer :: !(Doubly s), -- ^ Right buffer of partial constructions
  fwdRules :: !(Map (Sym,Sym) Sym), -- ^ Forward rules
  extTrie :: !(Trie ()), -- ^ Extensions of all symbols
  candidates :: !(Map (Sym,Sym) Int) -- ^ Joint counts (candidates)
}

full :: Mesh s -> Bool
full (Mesh _ ss _ _ _ _ _) = D.full ss

checkParity :: PrimMonad m => Doubly (PrimState m) -> m Bool
checkParity ss = (S.next (D.toRevStream ss) >>=) $ \case
  Left () -> return False
  Right (sn, revRest) -> even <$> S.length_ (S.takeWhile (== sn) revRest)

-- | Construction
fromList :: PrimMonad m => Rules -> [Sym] -> m (Mesh (PrimState m))
fromList rs l = do
  ss <- D.fromList l

  -- check parity of end of `ss`
  par <- (S.next (D.toRevStream ss) >>=) $ \case
    Left () -> return False
    Right (sn, revRest) ->
      even <$> S.length_ (S.takeWhile (== sn) revRest)

  buf <- D.new 10 -- could be bigger
  return $ Mesh mdl ss par buf rsm trie cdts
  where
    numSymbols = R.numSymbols rs
    mdl = Mdl.fromList rs l
    rsm = R.toMap rs
    trie = Trie.fromList $
           (,()) . BS.pack . R.extension rs <$> [0..numSymbols-1]
    cdts = countJoints l

-- | Construction from a stream of size at most `n`
fromStream :: PrimMonad m => Rules -> Int -> Stream (Of Sym) m r ->
                             m (Mesh (PrimState m), r)
fromStream rs n str = do
  (ss,(mdl,(cdts,r))) <- D.fromStream n $
                         Mdl.fromStream rs $ S.copy $
                         countJointsM $ S.copy str

  -- check parity of end of `ss`
  par <- (S.next (D.toRevStream ss) >>=) $ \case
    Left () -> return False
    Right (sn, revRest) ->
      even <$> S.length_ (S.takeWhile (== sn) revRest)

  buf <- D.new 10 -- could be bigger
  return (Mesh mdl ss par buf rsm trie cdts, r)

  where
    numSymbols = R.numSymbols rs
    rsm = R.toMap rs
    trie = Trie.fromList $
           (,()) . BS.pack . R.extension rs <$> [0..numSymbols-1]

-- | Compute the loss for each candidate joint and return joints ordered
-- by loss, lowest first, with count.
-- TODO: bookkeep
sortCandidates :: Mesh s -> Double -> [(Double,((Sym,Sym),Int))]
sortCandidates (Mesh mdl _ _ _ _ _ cdts) scale =
  L.sort $ withLoss <$> M.toList cdts
  where
    withLoss = toFst $ uncurry $ Mdl.scaledInfoDelta scale mdl

-- | Add a rule, rewrite
pushRule :: PrimMonad m => Mesh (PrimState m) -> (Sym,Sym) ->
                           m (Int, Mesh (PrimState m))
pushRule (Mesh mdl ss _ buf rsm trie cdts) (s0,s1) = do
  ss' <- S.foldM_ (subst1 s01) (return ss) return $
         D.jointIndices ss (s0,s1)
  par' <- checkParity ss'
  buf' <- S.foldM_ (subst1 s01) (return buf) return $
          D.jointIndices buf (s0,s1)
  return (s01, Mesh mdl' ss' par' buf' rsm' trie' cdts')
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
flush msh@(Mesh mdl@(Model rs _ _) ss0 par0 buf0 rsm trie cdts0)
  | D.full ss0 = return msh
  | otherwise = do
      sn0 <- fromMaybe minBound <$> D.last ss0 -- minBound hacky but w/e
      go ss0 par0 buf0 cdts0 sn0
        . BS.pack
        . concatMap (R.extension rs)
        =<< D.toList buf0
  where
    go !ss !par !buf !cdts !sn !bs
      | D.full ss || prefixing = -- D.null buf ==> prefixing
          return $ Mesh mdl ss par buf rsm trie cdts -- end
      | otherwise = do
          let i = fromJust $ D.head buf
          s <- D.read buf i
          ss' <- fromJust <$> D.trySnoc ss s
          buf' <- D.delete buf i
          let len = R.symbolLength rs s
              bs' = BS.drop len bs
              par' = s /= sn || not par -- if s == sn then not par else True
              cdts' | s == sn && not par = cdts
                    | otherwise = M.insertWith (+) (sn,s) 1 cdts
          go ss' par' buf' cdts' s bs'
      where
        exts = Trie.keys $ Trie.submap bs trie
        prefixing = not (null exts || exts == [bs])

snoc :: forall m. PrimMonad m =>
        Mesh (PrimState m) -> Sym -> m (Mesh (PrimState m))
snoc msh@(Mesh (Model rs _ _) _ _ buf0 rsm _ _) s = do
  buf <- go buf0 s
  flush $ msh{ buffer = buf }
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

countJointsM :: Monad m => Stream (Of Int) m r -> m (Map (Int,Int) Int, r)
countJointsM = countJointsM_ M.empty

countJointsM_ :: Monad m => Map (Int,Int) Int -> Stream (Of Int) m r ->
                            m (Map (Int,Int) Int, r)
countJointsM_ m0 ss0 = (S.next ss0 >>=) $ \case
  Left r -> return (m0, r)
  Right (s0,ss0') -> go m0 s0 ss0'
  where
    go !m s0 ss = (S.next ss >>=) $ \case
      Left r -> return (m,r) -- end
      Right (s1,ss') -> (S.next ss' >>=) $ \case
        Left r -> return (m', r) -- last joint
        Right (s2,_) | s0 == s1 && s1 == s2 -> countJointsM_ m' ss' -- even
                     | otherwise -> go m' s1 ss' -- odd
        where m' = M.insertWith (+) (s0,s1) 1 m
