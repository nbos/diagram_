{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections, LambdaCase #-}
module Diagram.Mesh (module Diagram.Mesh) where

import Control.Monad
import Control.Monad.Primitive (PrimMonad(PrimState))

import Data.Word (Word8)
import Data.Maybe
import Data.Bifunctor
import qualified Data.Map.Strict as M
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.IntSet as IS

import Streaming hiding (first,second,join)
import qualified Streaming as S
import qualified Streaming.Prelude as S

import qualified Data.Vector.Strict as B
import qualified Data.Vector.Generic.Mutable as MV

import Diagram.Rules (Sym)
import qualified Diagram.Rules as R
import qualified Diagram.Doubly as D
import Diagram.Model (Model(..))
import qualified Diagram.Model as Mdl
import Diagram.Joints (Doubly,Joints,ByLoss)
import qualified Diagram.Joints as Joints
import Diagram.Source (Source)
import qualified Diagram.Source as Source
import Diagram.Progress
import Diagram.Util

----------
-- MESH --
----------

-- | Symbol string with all the bookkeeping
data Mesh m r = Mesh {
  model :: !(Model (PrimState m)),   -- ^ String's model :: (rs,n,ks)
  string :: !(Doubly (PrimState m)), -- ^ Fixed size underlying string
  parity :: !Bool,                   -- ^ Number of times last symbol is repeated
  candidates :: !Joints,             -- ^ Joint counts + locations
  byPart :: !(B.MVector (PrimState m)
               (Set (Sym,Sym))),     -- ^ Joints each symbol is part of
  losses :: !ByLoss,                 -- ^ Joints by their count/loss
  source :: !(Source m r)            -- ^ Source of raw bytes
}

full :: Mesh m r -> Bool
full (Mesh _ str _ _ _ _ _) = D.full str

checkParity :: PrimMonad m => Doubly (PrimState m) -> m Bool
checkParity str = (S.next (D.revStream str) >>=) $ \case
  Left () -> return False
  Right (sn, revRest) -> even <$> S.length_ (S.takeWhile (== sn) revRest)

-- | Construction with size `n` from a stream of atoms
fromStream :: (PrimMonad m, MonadIO m) =>
              Int -> Stream (Of Word8) m r -> m (Mesh m r)
fromStream n as = do
  let rs = R.empty
  (mdl,(str,(jts,rest))) <- Mdl.fromStream rs $
                            D.fromStream n $ S.copy $
                            Joints.fromStream $
                            S.zip (S.enumFrom 0) $ S.copy $
                            S.map fromEnum $
                            withPB n "Initializing mesh" $
                            S.splitAt n as

  -- check parity of end of `str`
  par <- (S.next (D.revStream str) >>=) $ \case
    Left () -> return False
    Right (sn, revRest) ->
      even <$> S.length_ (S.takeWhile (== sn) revRest)

  bp <- MV.replicate (R.numSymbols rs) Set.empty
  forM_ (M.keys jts) $ \(s0,s1) -> do
    MV.modify bp (Set.insert (s0,s1)) s0
    MV.modify bp (Set.insert (s0,s1)) s1

  let Model _ _ mks = mdl
  ls <- Joints.byLoss mks jts

  Mesh mdl str par jts bp ls <$> Source.new rs rest

minLoss :: Mesh m r -> (Double, [(Sym,Sym)])
minLoss (Mesh (Model rs n _) _ _ _ _ ls _) = Joints.findMin numSymbols n ls
  where numSymbols = R.numSymbols rs

-- | Add a rule, rewrite, refill, with progress bars
pushRule :: (PrimMonad m, MonadIO m) =>
            Mesh m r -> (Sym,Sym) -> m (Sym, Mesh m r)
pushRule (Mesh mdl@(Model _ _ ks) str _ jts bp ls src) (s0,s1) = do
  let (n01, i01s) = second IS.toList $
                    fromMaybe (error $ "not a candidate: " ++ show (s0,s1)) $
                    M.lookup (s0,s1) jts
  (s01, mdl'@(Model rs' _ _)) <- Mdl.pushRule mdl (s0,s1) n01
  let here = (++) (" [" ++ show s01 ++ "]: ")

  str' <- S.foldM_ (D.subst2 s01) (return str) return $
          withPB n01 (here "Modifying string in place") $
          S.each i01s
  par' <- checkParity str'
  src' <- Source.pushRule (s0,s1) s01 src

  -- :: update joints books :: --
  ((am,rm),_) <- Joints.delta (s0,s1) s01 str $
                 withPB n01 (here "Computing change on candidates") $
                 S.each i01s
  let jts' = (jts `Joints.difference` rm) `Joints.union` am

  bp' <- MV.grow bp 1 -- (cloned)
  MV.write bp' s01 Set.empty
  -- add newly introduced joints at their parts (bp)
  forM_ (M.keys $ am `M.difference` jts) $ \jt -> do
    MV.modify bp' (Set.insert jt) $ fst jt
    MV.modify bp' (Set.insert jt) $ snd jt
  -- remove now eliminated joints at their parts (bp)
  forM_ (M.keys $ rm `M.difference` jts') $ \jt -> do
    MV.modify bp' (Set.delete jt) $ fst jt
    MV.modify bp' (Set.delete jt) $ snd jt

  -- :: fill mesh with new symbols :: --
  (observed, am', Mesh mdl'' str'' par'' jts'' bp'' ls' src'') <-
    (S.next (Source.splitAt rs' n01 src') >>=) $ \case
    Left src'' -> return ( IS.empty, M.empty
                         , Mesh mdl' str' par' jts' bp' ls src'')
    Right (s_0,ss) -> do
      i_n' <- fromMaybe (error "empty Mesh") <$> D.last str'
      ns' <- D.read str' i_n'

      -- in one pass
      (observed :> (mdl'' :> (am', str'' :> src''))) <-
        S.fold (flip IS.insert) IS.empty id $ -- record inc'd symbols
        S.foldM Mdl.incCount (return mdl') return $ S.copy $ -- inc Model counts
        S.map snd $ -- now, only for the Sym, dropping Index
        ( if par' then Joints.fromStreamOdd_ (i_n',ns') -- odd
          else Joints.fromStream_ ) M.empty $ S.copy $  -- even
        S.map fst $ -- drop every intermediate (Doubly m), keep (Index,Sym)
        fmap (S.first $ snd -- we only need the last (Doubly m), drop (Index,Sym)
               . fromJust) $ -- assume there is a last element
        S.last $ S.copy $ -- get last ((Index,Sym), Doubly m)
        S.scanM (\(_,l) s -> first (,s) . fromJust <$> D.trySnoc l s) -- snoc
                (return (error "_|_", str)) return $
        withPB n01 "Filling mesh back to capacity" $
        S.yield s_0 >> ss
      --

      par'' <- checkParity str''
      forM_ (M.keys $ am' `M.difference` jts') $ \jt -> do
        MV.modify bp' (Set.insert jt) $ fst jt
        MV.modify bp' (Set.insert jt) $ snd jt

      let jts'' = jts' `Joints.union` am'
      return (observed, am', Mesh mdl'' str'' par'' jts'' bp' ls src'')

  -- :: delete and re-insert in loss map :: --
  let affectedSymbols = IS.insert s0 $ IS.insert s1 observed
  affectedJoints <- -- (this could be improved but it's the simplest)
    fmap (Set.unions . (M.keysSet (M.unions [am,rm,am']):))$
    mapM (MV.read bp) $ IS.toList affectedSymbols

  let lossesToDelete = M.restrictKeys jts   affectedJoints
      lossesToInsert = M.restrictKeys jts'' affectedJoints

      deleteLoss im (jt,(k01,_)) = do
        k0 <- MV.read ks $ fst jt
        k1 <- MV.read ks $ snd jt
        let key = (k01,(k0,k1))
        return $ Joints.deleteLoss key jt im

      Model _ _ ks'' = mdl''
      insertLoss im (jt,(k01,_)) = do
        k0 <- MV.read ks'' $ fst jt
        k1 <- MV.read ks'' $ snd jt
        let key' = (k01,(k0,k1))
        return $ Joints.insertLoss key' jt im

  ls'' <- flip2 (S.foldM_ insertLoss) return
          ( withPB (M.size lossesToInsert) "Inserting losses" $
            S.each $ M.toList lossesToInsert ) $
          S.foldM_ deleteLoss (return ls') return $
          withPB (M.size lossesToDelete) "Deleting losses" $
          S.each $ M.toList lossesToDelete

  return (s01, Mesh mdl'' str'' par'' jts'' bp'' ls'' src'')
