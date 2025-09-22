{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections, BangPatterns, LambdaCase #-}
module Diagram.Mesh (module Diagram.Mesh) where

import Prelude hiding (read)

import Control.Monad hiding (join)
import Control.Monad.Primitive (PrimMonad(PrimState))

import Data.Word (Word8)
import Data.Maybe
import Data.Tuple.Extra
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import qualified Data.IntSet as IS
import Data.Trie (Trie)
import qualified Data.Trie as Trie
import qualified Data.ByteString as BS

import Streaming hiding (second,join)
import qualified Streaming.Prelude as S
import Diagram.Streaming () -- PrimMonad instance

import Diagram.Rules (Sym)
import qualified Diagram.Rules as R
import Diagram.Doubly (Index)
import qualified Diagram.Doubly as D
import Diagram.Model (Model(..))
import qualified Diagram.Model as Model
import Diagram.Joints (ByJoint,Doubly)
import qualified Diagram.Joints as Joints
import Diagram.Progress
import Diagram.Util

----------
-- MESH --
----------

-- | Symbol string with all the bookkeeping
data Mesh s = Mesh {
  model :: !(Model s), -- ^ String's model :: (rs,n,ks)
  string :: !(Doubly s), -- ^ Fixed size underlying string
  parity :: !Bool,  -- ^ Number of times last symbol is repeated
  buffer :: !(Doubly s), -- ^ Right buffer of partial constructions
  fwdRules :: !(Map (Sym,Sym) Sym), -- ^ Forward rules
  extTrie :: !(Trie ()), -- ^ Extensions of all symbols
  candidates :: !ByJoint -- ^ Joint counts + locations
}

full :: Mesh s -> Bool
full (Mesh _ ss _ _ _ _ _) = D.full ss

checkParity :: PrimMonad m => Doubly (PrimState m) -> m Bool
checkParity ss = (S.next (D.revStream ss) >>=) $ \case
  Left () -> return False
  Right (sn, revRest) -> even <$> S.length_ (S.takeWhile (== sn) revRest)

-- | Construction from a stream of atoms size at most `n`
fromStream :: PrimMonad m => Int -> Stream (Of Word8) m r ->
                             m (Mesh (PrimState m), r)
fromStream n str = do
  (ss,(mdl,(cdts,r))) <- D.fromStream n $
                         Model.fromStream R.empty $ S.copy $
                         Joints.fromList_ M.empty $
                         S.zip (S.enumFrom 0) $ S.copy $
                         S.map fromEnum str

  -- check parity of end of `ss`
  par <- (S.next (D.revStream ss) >>=) $ \case
    Left () -> return False
    Right (sn, revRest) ->
      even <$> S.length_ (S.takeWhile (== sn) revRest)

  buf <- D.new 10 -- could be bigger
  return (Mesh mdl ss par buf rsm trie cdts, r)

  where
    rsm = M.empty
    trie = Trie.fromList $ (,()) . BS.pack . (:[]) <$> [0..255]

-- | Add a rule, rewrite, with progress bars
pushRule :: (PrimMonad m, MonadIO m) =>
            Mesh (PrimState m) -> (Sym,Sym) -> m (Sym, Mesh (PrimState m))
pushRule (Mesh mdl@(Model rs _ _) ss _ buf rsm trie cdts) (s0,s1) = do
  (s01, mdl') <- Model.pushRule mdl (s0,s1) n01
  let here = (++) (" [" ++ show s01 ++ "]: ")
      rsm' = M.insert (s0,s1) s01 rsm

  ((am,rm),_) <- Joints.delta (s0,s1) s01 ss $
                 withPB n01 (here "Computing change on candidates") $
                 S.each i01s
  let cdts' = (cdts `Joints.difference` rm) `Joints.union` am

  ss' <- S.foldM_ (subst1 s01) (return ss) return $
         withPB n01 (here "Modifying string in place") $
         S.each i01s

  par' <- checkParity ss'
  buf' <- S.foldM_ (subst1 s01) (return buf) return $
          D.jointIndices buf (s0,s1)

  return (s01, Mesh mdl' ss' par' buf' rsm' trie' cdts')

  where
    err = error $ "not a candidate: " ++ show (s0,s1)
    (n01, i01s) = second IS.toList . fromMaybe err $ M.lookup (s0,s1) cdts
    bs01 = R.bytestring rs s0 <> R.bytestring rs s1
    trie' = Trie.insert bs01 () trie

-- | Substitute the symbol at the given index and the next with the
-- given symbol
subst1 :: PrimMonad m => Sym -> Doubly (PrimState m) -> Index ->
                         m (Doubly (PrimState m))
subst1 s01 l i = D.modify l (const s01) i >>
                 D.next l i >>= D.delete l

-- | While there is free space in the symbol string and the buffer is
-- not the prefix of any potential symbol, append the fully constructed
-- symbols at the head of the buffer to the end of the symbol string
flush :: PrimMonad m => Mesh (PrimState m) -> m (Mesh (PrimState m))
flush msh@(Mesh mdl0@(Model rs _ _) ss0 par0 buf0 rsm trie cdts0)
  | D.full ss0 = return msh
  | otherwise = do
      in0 <- fromMaybe err <$> D.last ss0
      sn0 <- D.read ss0 in0
      go mdl0 ss0 par0 buf0 cdts0 in0 sn0
        . BS.pack
        . concatMap (R.extension rs)
        =<< D.toList buf0
  where
    err = error "Mesh.flush: empty mesh case not implemented"
    go !mdl !ss !par !buf !cdts !i_n !sn !bs
      | D.full ss || prefixing = -- D.null buf ==> prefixing
          return $ Mesh mdl ss par buf rsm trie cdts -- end
      | otherwise = do -- assert $ not (D.null buf || D.null ss)
          let i0buf = fromJust $ D.head buf
          s <- D.read buf i0buf
          mdl' <- Model.incCount mdl s
          (i_n', ss') <- fromJust <$> D.trySnoc ss s
          buf' <- D.delete buf i0buf
          let len = R.symbolLength rs s
              bs' = BS.drop len bs
              par' = s /= sn || not par -- if s == sn then not par else True
              cdts' | s == sn && not par = cdts
                    | otherwise = Joints.insert cdts (sn,s) i_n
          go mdl' ss' par' buf' cdts' i_n' s bs'
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

      _else -> snd <$> D.snoc buf s1
