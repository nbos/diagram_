{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections, LambdaCase #-}
module Diagram.Mesh (module Diagram.Mesh) where

import Control.Monad.Primitive (PrimMonad(PrimState))

import Data.Word (Word8)
import Data.Maybe
import Data.Tuple.Extra
import qualified Data.Map.Strict as M
import qualified Data.IntSet as IS

import Streaming hiding (first,second,join)
import qualified Streaming as S
import qualified Streaming.Prelude as S

import Diagram.Rules (Sym)
import qualified Diagram.Rules as R
import qualified Diagram.Doubly as D
import Diagram.Model (Model(..))
import qualified Diagram.Model as Model
import Diagram.Joints (Joints,Doubly)
import qualified Diagram.Joints as Joints
import Diagram.Source (Source)
import qualified Diagram.Source as Source
import Diagram.Progress

----------
-- MESH --
----------

-- | Symbol string with all the bookkeeping
data Mesh m r = Mesh {
  model :: !(Model (PrimState m)),   -- ^ String's model :: (rs,n,ks)
  string :: !(Doubly (PrimState m)), -- ^ Fixed size underlying string
  parity :: !Bool,       -- ^ Number of times last symbol is repeated
  candidates :: !Joints, -- ^ Joint counts + locations
  source :: !(Source m r)
}

full :: Mesh m r -> Bool
full (Mesh _ str _ _ _) = D.full str

checkParity :: PrimMonad m => Doubly (PrimState m) -> m Bool
checkParity str = (S.next (D.revStream str) >>=) $ \case
  Left () -> return False
  Right (sn, revRest) -> even <$> S.length_ (S.takeWhile (== sn) revRest)

-- | Construction with size `n` from a stream of atoms
fromStream :: (PrimMonad m, MonadIO m) =>
              Int -> Stream (Of Word8) m r -> m (Mesh m r)
fromStream n as = do
  let rs = R.empty
  (mdl,(str,(cdts,rest))) <- Model.fromStream rs $
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

  Mesh mdl str par cdts <$> Source.new rs rest

-- | Add a rule, rewrite, refill, with progress bars
pushRule :: (PrimMonad m, MonadIO m) =>
            Mesh m r -> (Sym,Sym) -> m (Sym, Mesh m r)
pushRule (Mesh mdl str _ cdts src) (s0,s1) = do
  (s01, mdl'@(Model rs' _ _)) <- Model.pushRule mdl (s0,s1) n01
  let here = (++) (" [" ++ show s01 ++ "]: ")

  ((am,rm),_) <- Joints.delta (s0,s1) s01 str $
                 withPB n01 (here "Computing change on candidates") $
                 S.each i01s
  let cdts' = (cdts `Joints.difference` rm) `Joints.union` am

  str' <- S.foldM_ (D.subst2 s01) (return str) return $
         withPB n01 (here "Modifying string in place") $
         S.each i01s
  par' <- checkParity str'

  src' <- Source.pushRule (s0,s1) s01 src
  (S.next (Source.splitAt rs' n01 src') >>=) $ \case
    Left src'' -> return (s01, Mesh mdl' str' par' cdts' src'')
    Right (s_0,ss) -> do
      i_n' <- fromMaybe (error "empty Mesh") <$> D.last str'
      ns' <- D.read str' i_n'
      (mdl'' :> (am', str'' :> src'')) <-
        S.foldM Model.incCount (return mdl') return $ -- inc Model counts
        S.map snd $ -- now, only for the Sym, dropping Index
        ( if par' then Joints.fromStreamOdd_ (i_n',ns') -- odd
          else Joints.fromStream_ ) M.empty $ S.copy $  -- even
        S.map fst $ -- drop every intermediate (Doubly m), keep (Index,Sym)
        fmap (S.first $ snd -- we only need the last (Doubly m), drop (Index,Sym)
               . fromJust) $ -- assume there is a last element
        S.last $ S.copy $ -- get last ((Index,Sym), Doubly m)
        S.scanM (\(_,l) s -> first (,s) . fromJust <$> D.trySnoc l s) -- snoc
                (return (bot,str)) return $
        withPB n01 "Filling mesh back to capacity" $
        S.yield s_0 >> ss

      par'' <- checkParity str''
      let cdts'' = cdts' `Joints.union` am'
      return (s01, Mesh mdl'' str'' par'' cdts'' src'')

  where
    bot = error "lazy bottom"
    err = error $ "not a candidate: " ++ show (s0,s1)
    (n01, i01s) = second IS.toList . fromMaybe err $ M.lookup (s0,s1) cdts
