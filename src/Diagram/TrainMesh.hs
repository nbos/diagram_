{-# LANGUAGE ScopedTypeVariables #-}
module Diagram.TrainMesh (module Diagram.TrainMesh) where

import Control.Monad
import Control.Monad.Primitive (PrimMonad(PrimState))

import Data.Word (Word8)
import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Strict as M
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.IntSet as IS

import Streaming hiding (first,second,join)
import qualified Streaming.Prelude as S

import qualified Data.Vector.Strict as B
import qualified Data.Vector.Generic.Mutable as MV

import Diagram.Rules (Sym)
import qualified Diagram.Rules as R
import Diagram.Model (Model(..))
import Diagram.Joints (LossFn,ByLoss(..))
import qualified Diagram.Joints as Joints
import Diagram.Mesh (Mesh(Mesh))
import qualified Diagram.Mesh as Mesh
import Diagram.Source (Source)
import qualified Diagram.Source as Source
import Diagram.Progress
import Diagram.Util

----------
-- MESH --
----------

-- | Mesh with joints sorted by loss
data TrainMesh m r = TrainMesh {
  mesh :: !(Mesh m),            -- ^ String, model & joints
  byPart :: !(B.MVector (PrimState m)
              (Set (Sym,Sym))), -- ^ Joints each symbol is part of
  losses :: !ByLoss,            -- ^ Joints by their count/loss
  source :: !(Source m r)       -- ^ Source of raw bytes
}

-- | Construction with size `n` from a stream of atoms
fromStream :: (PrimMonad m, MonadIO m) =>
              LossFn -> Int -> Stream (Of Word8) m r -> m (TrainMesh m r)
fromStream fn n as = do
  let rs = R.empty
  (msh@(Mesh mdl _ jts), rest) <- Mesh.fromStream n as

  bp <- MV.replicate (R.numSymbols rs) Set.empty
  forM_ (M.keys jts) $ \(s0,s1) -> do
    MV.modify bp (Set.insert (s0,s1)) s0
    MV.modify bp (Set.insert (s0,s1)) s1

  let Model _ _ mks = mdl
  ls <- Joints.byLoss fn mks jts

  TrainMesh msh bp ls <$> Source.new rs rest

minLoss :: TrainMesh m r -> (Double, [(Sym,Sym)])
minLoss (TrainMesh (Mesh (Model rs n _) _ _) _ ls _) =
  Joints.findMin (R.numSymbols rs) n ls

-- | Add a rule, rewrite, refill, with progress bars
pushRule :: (PrimMonad m, MonadIO m) => Bool -> Bool ->
            TrainMesh m r -> (Sym,Sym) -> m (Sym, TrainMesh m r)
pushRule verifyString verifyMeta tm (s0,s1) = do
  let TrainMesh msh@(Mesh (Model _ n ks) _ jts) bp ls src = tm

  (s01, (am, rm), msh'@(Mesh (Model rs' n' _) _ jts')) <-
    Mesh.pushRule verifyMeta msh (s0,s1)

  let n01 = n - n'
      here = (++) (" [" ++ show s01 ++ "]: ")

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

  src' <- Source.pushRule (s0,s1) s01 src
  -- :: fill mesh with new symbols :: --
  (msh''@(Mesh mdl'' str'' jts''), am', observed, src'') <-
    Mesh.append msh' (Source.splitAt rs' n01 src')

  forM_ (M.keys $ am' `M.difference` jts') $ \jt -> do
    MV.modify bp' (Set.insert jt) $ fst jt
    MV.modify bp' (Set.insert jt) $ snd jt

  when verifyString $ Mesh.validateString msh' ()

  -- :: delete and re-insert in loss map :: --
  let affectedSymbols = IS.insert s0 $
                        IS.insert s1 $
                        IS.delete s01 observed -- delete bc using old `bp`
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

  ls' <- flip2 (S.foldM_ insertLoss) return
         ( withPB (M.size lossesToInsert) (here "Inserting losses") $
           S.each $ M.toList lossesToInsert ) $
         S.foldM_ deleteLoss (return ls) return $
         withPB (M.size lossesToDelete) (here "Deleting losses") $
         S.each $ M.toList lossesToDelete

  -- <verification>
  when verifyMeta $ do
    let ByLoss fn im' = ls'
    -- TODO: progress bar
    (ByLoss _ imVerif) <- Joints.byLoss fn ks'' =<< Joints.fromDoubly str''
    unless (im' == imVerif) $
      let common = IM.keysSet $
                   IM.mapMaybe id $
                   IM.intersectionWith (\v0 v1 -> if v0 == v1 then Just v0 else Nothing)
                   im' imVerif
      in error $ "Error in the maintenance of loss map. Contains:\n"
         ++ show (im' `IM.withoutKeys` common)
         ++ "\nShould contain:\n" ++ show (imVerif `IM.withoutKeys` common)
  -- </verification>

  return (s01, TrainMesh msh'' bp' ls' src'')
