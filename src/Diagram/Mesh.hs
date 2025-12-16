{-# LANGUAGE ScopedTypeVariables #-}
module Diagram.Mesh (module Diagram.Mesh) where

import Control.Monad
import Control.Monad.Primitive (PrimMonad(PrimState))

import Data.Word (Word8)
import Data.Maybe
import Data.Bifunctor
import qualified Data.List as L
import qualified Data.Map.Strict as M
import qualified Data.IntSet as IS

import Streaming hiding (first,second,join)
import qualified Streaming.Prelude as S

import qualified Data.Vector.Unboxed as U

import Diagram.Rules (Sym)
import qualified Diagram.Rules as R
import qualified Diagram.Doubly as D
import Diagram.Model (Model(..))
import qualified Diagram.Model as Mdl
import Diagram.Joints (Doubly,Joints)
import qualified Diagram.Joints as Joints
import Diagram.Streaming ()
import Diagram.Progress (withPB)

----------
-- MESH --
----------

-- | Symbol string with rules, counts and joint counts
data Mesh m = Mesh {
  model :: !(Model (PrimState m)),   -- ^ String's model :: (rs,n,ks)
  string :: !(Doubly (PrimState m)), -- ^ Fixed size underlying string
  candidates :: !Joints              -- ^ Joint counts + locations
}

full :: Mesh m -> Bool
full (Mesh _ str _) = D.full str

-- | Construction from the first `n` atoms of a stream
fromStream :: (PrimMonad m, MonadIO m) =>
              Int -> Stream (Of Word8) m r -> m ( Mesh m
                                                , Stream (Of Word8) m r )
fromStream n as = do
  let rs = R.empty
  (mdl,(str,(jts,rest))) <- Mdl.fromStream rs $
                            D.fromStream n $ S.copy $
                            Joints.fromStream $
                            S.zip (S.enumFrom 0) $ S.copy $
                            S.map fromEnum $
                            S.splitAt n as
  return (Mesh mdl str jts, rest)

validateString :: PrimMonad m => Mesh m -> a -> m a
validateString (Mesh (Model rs _ _) str _) a = do
  ss <- D.toList str
  let as = fmap fromEnum $ R.extension rs `concatMap` ss
      ss' = R.subst rs as -- revReduce
      ss'' = L.foldl' (flip id) as $
             zipWith R.subst1 (R.toList rs) [256..]

  when (ss'' /= ss') $
    error $ "Discrepancy between revReduce algorithm and 1-by-1 substitution:\n"
    ++ "revReduce:\n" ++ show ss'
    ++ "\nsubst1:\n" ++ show ss''

  when (ss' /= ss) $
    error $ "Error in construction order:\n"
    ++ "String is:\n" ++ show ss
    ++ "\nShould be:\n" ++ show ss'

  return a

-- | Add a rule, rewrite, refill, with progress bars
pushRule :: (PrimMonad m, MonadIO m) => Bool -> Bool ->
            Mesh m -> (Sym,Sym) -> m (Sym, (Joints, Joints), Mesh m)
pushRule verifyString verifyModel (Mesh mdl str jts) (s0,s1) = do
  let (n01, i01s) = second IS.toList $
                    fromMaybe (error $ "not a candidate: " ++ show (s0,s1)) $
                    M.lookup (s0,s1) jts
  (s01, mdl'@(Model _ _ ks')) <- Mdl.pushRule mdl (s0,s1) n01
  let here = (++) (" [" ++ show s01 ++ "]: ")

  -- :: update joints books :: --
  ((am,rm),_) <- Joints.delta (s0,s1) s01 str $
                 withPB n01 (here "Updating joint counts") $
                 S.each i01s
  let jts' = (jts `Joints.difference` rm) `Joints.union` am

  -- :: rewrite :: --
  str' <- S.foldM_ (D.subst2 s01) (return str) return $
          withPB n01 (here "Modifying string in place") $
          S.each i01s

  let msh' = Mesh mdl' str' jts'

  -- TODO: move to --verify-model
  -- <verification>
  when verifyString $ validateString msh' ()
  when verifyModel $ do
    let Model rs' n' _ = mdl'
    -- TODO: progress bar
    (Model _ nVerif ksVerif, _) <- Mdl.fromStream rs' $ D.stream str'
    unless (n' == nVerif) $
      error $ "Error in the maintenance of symbol count: " ++ show n'
      ++ " should be " ++ show nVerif

    ksEq <- liftA2 (==) (U.freeze ks') (U.freeze ksVerif)
    unless ksEq $ do
      v0 <- U.freeze ks'
      v1 <- U.freeze ksVerif
      error $ "Error in the maintenance of counts vector:\n" ++ show v0
        ++ "\nShould be:\n" ++ show v1
  -- </verification>

  return (s01, (am, rm), msh')
