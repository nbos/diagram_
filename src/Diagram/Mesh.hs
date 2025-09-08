{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections, BangPatterns, LambdaCase, TypeApplications #-}
module Diagram.Mesh (module Diagram.Mesh) where

import Control.Monad
import Control.Monad.Primitive

import Data.Maybe
import qualified Data.List as L
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Data.Trie (Trie)
import qualified Data.Trie as Trie
import qualified Data.ByteString as BS

import qualified Data.Vector.Strict as B
import qualified Data.Vector.Unboxed as U
import Data.Vector.Unboxed.Mutable (MVector)
import qualified Data.Vector.Generic.Mutable as MV

import Streaming as S
import qualified Streaming.Prelude as S
import Diagram.Streaming () -- PrimMonad Stream instance

import Diagram.Doubly (Index)
import qualified Diagram.Doubly as D
import Diagram.Rules (Rules)
import qualified Diagram.Rules as R
import Diagram.Model (Model(..))
import qualified Diagram.Model as Mdl
import Diagram.Progress
import Diagram.Util

type Sym = Int -- symbol
type Doubly s = D.Doubly MVector s Sym

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
  extLens :: !(U.Vector Int), -- ^ Length of extension of all symbols
  candidates :: !(Map (Sym,Sym) Int) -- ^ Joint counts (candidates)
}

full :: Mesh s -> Bool
full (Mesh _ ss _ _ _ _ _ _) = D.full ss

-- | O(numSymbols). The length of the string's extension. Could be
-- bookkept if we get to that point.
extLen :: PrimMonad m => Mesh (PrimState m) -> m Int
extLen (Mesh (Model _ _ ks) _ _ _ _ _ sls _) =
  MV.ifoldl' (\acc i k -> acc + k * (sls U.! i)) 0 ks

checkParity :: PrimMonad m => Doubly (PrimState m) -> m Bool
checkParity ss = (S.next (D.toRevStream ss) >>=) $ \case
  Left () -> return False
  Right (sn, revRest) -> even <$> S.length_ (S.takeWhile (== sn) revRest)

-- | Construction
fromList :: PrimMonad m => Rules -> [Sym] -> m (Mesh (PrimState m))
fromList rs l = do
  mdl <- Mdl.fromList rs l
  ss <- D.fromList l

  -- check parity of end of `ss`
  par <- (S.next (D.toRevStream ss) >>=) $ \case
    Left () -> return False
    Right (sn, revRest) ->
      even <$> S.length_ (S.takeWhile (== sn) revRest)

  buf <- D.new 10 -- could be bigger
  return $ Mesh mdl ss par buf rsm trie sls cdts
  where
    numSymbols = R.numSymbols rs
    rsm = R.toMap rs
    trie = Trie.fromList $
           (,()) . BS.pack . R.extension rs <$> [0..numSymbols-1]
    sls = R.symbolLengths rs
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
  return (Mesh mdl ss par buf rsm trie sls cdts, r)

  where
    numSymbols = R.numSymbols rs
    rsm = R.toMap rs
    trie = Trie.fromList $
           (,()) . BS.pack . R.extension rs <$> [0..numSymbols-1]
    sls = U.generate numSymbols $ R.symbolLength rs

-- | Compute the loss for each candidate joint and return joints ordered
-- by loss, lowest first, with count.
-- TODO: bookkeep
sortCandidates :: PrimMonad m => Mesh (PrimState m) -> Double ->
                                 m [(Double,((Sym,Sym),Int))]
sortCandidates (Mesh mdl _ _ _ _ _ _ cdts) scale =
  L.sort <$> mapM withLoss (M.toList cdts)
  where
    withLoss cdt = (,cdt) <$> uncurry (Mdl.scaledInfoDelta scale mdl) cdt

-- | Add a rule, rewrite, with progress bars
pushRule :: (PrimMonad m, MonadIO m) =>
            Mesh (PrimState m) -> (Sym,Sym) -> m (Int, Mesh (PrimState m))
pushRule (Mesh mdl@(Model rs _ _) ss _ buf rsm trie sls cdts) (s0,s1) = do
  (s01, mdl') <- Mdl.pushRule mdl (s0,s1) n01
  let here = (++) (" [" ++ show s01 ++ "]: ")
      rsm' = M.insert (s0,s1) s01 rsm

  -- Can't stream these three together bc of the way recountM has to
  -- look behind and ahead on string
  i01s <- S.toList_ $
          withPB n01 (here "Finding construction sites") $
          D.jointIndices ss (s0,s1)
  ss' <- S.foldM_ (subst1 s01) (return ss) return $
         withPB n01 (here "Modifying string in place") $
         S.each i01s
  (m,_) <- recountM ss' (s0,s1) s01 $
           withPB n01 (here "Computing change on candidates") $
           S.each i01s
  --

  par' <- checkParity ss'
  buf' <- S.foldM_ (subst1 s01) (return buf) return $
          D.jointIndices buf (s0,s1)

  let cdts' = M.mergeWithKey (const $ nothingIf (== 0) .: (+)) id id cdts m
  (s01,) <$> flush (Mesh mdl' ss' par' buf' rsm' trie' sls' cdts')

  where
    err = error $ "not a candidate: " ++ show (s0,s1)
    n01 = fromMaybe err $ M.lookup (s0,s1) cdts
    bs01 = R.bytestring rs s0 <> R.bytestring rs s1
    trie' = Trie.insert bs01 () trie
    sls' = U.snoc sls $ sum $ R.symbolLength rs <$> [s0,s1]

-- | While there is free space in the symbol string and the buffer is
-- not the prefix of any potential symbol, append the fully constructed
-- symbols at the head of the buffer to the end of the symbol string
flush :: PrimMonad m => Mesh (PrimState m) -> m (Mesh (PrimState m))
flush msh@(Mesh mdl0@(Model rs _ _) ss0 par0 buf0 rsm trie sls cdts0)
  | D.full ss0 = return msh
  | otherwise = do
      sn0 <- D.read ss0 . fromMaybe err =<< D.last ss0
      go mdl0 ss0 par0 buf0 cdts0 sn0
        . BS.pack
        . concatMap (R.extension rs)
        =<< D.toList buf0
  where
    err = error "Mesh.flush: empty mesh case not implemented"
    go !mdl !ss !par !buf !cdts !sn !bs
      | D.full ss || prefixing = -- D.null buf ==> prefixing
          return $ Mesh mdl ss par buf rsm trie sls cdts -- end
      | otherwise = do
          let i = fromJust $ D.head buf
          s <- D.read buf i
          mdl' <- Mdl.incCount mdl s
          ss' <- fromJust <$> D.trySnoc ss s
          buf' <- D.delete buf i
          let len = R.symbolLength rs s
              bs' = BS.drop len bs
              par' = s /= sn || not par -- if s == sn then not par else True
              cdts' | s == sn && not par = cdts
                    | otherwise = M.insertWith (+) (sn,s) 1 cdts
          go mdl' ss' par' buf' cdts' s bs'
      where
        exts = Trie.keys $ Trie.submap bs trie
        prefixing = not (null exts || exts == [bs])

snoc :: forall m. PrimMonad m =>
        Mesh (PrimState m) -> Sym -> m (Mesh (PrimState m))
snoc msh@(Mesh (Model rs _ _) _ _ buf0 rsm _ _ _) s = do
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

recountM :: forall m r. PrimMonad m => Doubly (PrimState m) -> (Int,Int) -> Int ->
            Stream (Of Int) m r -> m (Map (Int, Int) Int, r)
recountM (D.Doubly Nothing _ _ _ _) _ _ is0 = (M.empty, ) <$> S.effects is0
recountM ss@(D.Doubly (Just i0) _ _ _ _) (s0,s1) s01 is0 = do
  s0s1ref <- newPrimRef @U.MVector (0 :: Int) -- (s0,s1) (-) (redundant)
  s1s0ref <- newPrimRef @U.MVector (0 :: Int) -- (s1,s0) (-)
  prevvec <- MV.replicate @m @U.MVector s01 (0 :: Int) -- (i,s01) (-/+)
  nextvec <- MV.replicate @m @U.MVector s01 (0 :: Int) -- (s01,i) (-/+)
  s0s0ref <- newPrimRef @U.MVector (0 :: Int) -- (s0,s0) (+) (prev correction)
  s1s1ref <- newPrimRef @U.MVector (0 :: Int) -- (s1,s1) (+) (next correction)
  autoref <- newPrimRef @U.MVector (0 :: Int) -- (s01,s01) (+)

  -- <loop>
  r <- case () of
    _ -> go is0 where
      go :: Stream (Of Index) m r -> m r
      go is = (S.next is >>=) $ \case
        Left r -> return r -- end
        Right (i,is') -> do
          -- prev
          when (i /= i0) $ do
            iprev <- D.prev ss i
            prev <- D.read ss iprev
            MV.modify prevvec (+1) prev
            when (prev == s0) $ do -- s0 /= s1
              n0 <- (+1) <$> S.length_ ( S.break (/= s0) $
                                         D.toRevStreamFrom ss iprev )
              when (odd n0) $ modifyPrimRef s0s0ref (+1) -- correct

          -- s0s1's
          n <- S.length_ $ S.break (/= s01) $ D.toStreamFrom ss i
          modifyPrimRef s0s1ref (+n)
          when (s0 /= s1) $ modifyPrimRef s1s0ref (+(n-1))
          modifyPrimRef autoref (+(n `div` 2))

          -- next
          (S.next (S.drop (n-1) $ S.yield i >> is') >>=) $ \case
            Left r -> return r -- nothing after, end
            Right (i',is'') -> do
              inext <- D.next ss i'
              when (inext /= i0) $ do
                next <- D.read ss inext
                MV.modify nextvec (+1) next
                when (next == s1) $ do
                  if s0 == s1 then modifyPrimRef s1s1ref (+1) -- even nnext
                    else do
                    nnext <- (+1) <$> S.length_ ( S.break (/= next) $
                                                  D.toStreamFrom ss inext)
                    when (odd nnext) $ modifyPrimRef s1s1ref (+1)
              go is'' -- continue
  -- </loop>

  resref <- newPrimRef @B.MVector M.empty
  let insert k n = when (n /= 0) $ modifyPrimRef resref $ M.insertWith (+) k n

  -- read --
  insert (s0,s1) . (0-) =<< readPrimRef s0s1ref -- (-)
  insert (s1,s0) . (0-) =<< readPrimRef s1s0ref -- (-)
  MV.iforM_ prevvec $ \prev n -> insert (prev,s0) (-n)  -- (-)
                                 >> insert (prev,s01) n -- (+)
  MV.iforM_ nextvec $ \next n -> insert (s1,next) (-n)  -- (-)
                                 >> insert (s01,next) n -- (+)
  insert (s0,s0) =<< readPrimRef s0s0ref   -- (+)
  insert (s1,s1) =<< readPrimRef s1s1ref   -- (+)
  insert (s01,s01) =<< readPrimRef autoref -- (+)

  -- end --
  (,r) <$> readPrimRef resref

  where
    newPrimRef :: MV.MVector v a => a -> m (v (PrimState m) a)
    newPrimRef = MV.replicate 1
    modifyPrimRef :: MV.MVector v a => v (PrimState m) a -> (a -> a) -> m ()
    modifyPrimRef v f = MV.modify v f 0 -- TODO: unsafe
    readPrimRef :: MV.MVector v a => v (PrimState m) a -> m a
    readPrimRef = flip MV.read 0 -- TODO: unsafe
