{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections, LambdaCase #-}
module Diagram.Mesh (module Diagram.Mesh) where

import Control.Monad
import Control.Monad.Primitive (PrimMonad(PrimState))

import Data.Word (Word8)
import Data.Maybe
import Data.Bifunctor
import qualified Data.List as L
import qualified Data.Map.Strict as M
import Data.IntSet (IntSet)
import qualified Data.IntSet as IS

import Streaming hiding (first,second,join)
import qualified Streaming as S
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

last :: PrimMonad m => Mesh m -> m (Maybe Sym)
last (Mesh _ str _) = D.lastElem str

-- | Returns the parity at the end of the string in the form of a Bool:
-- True :: Odd, False :: Even.
checkParity :: PrimMonad m => Doubly (PrimState m) -> m Bool
checkParity str = (S.next (D.revStream str) >>=) $ \case
  Left () -> return False -- 0 :: Even :: False
  Right (sn, revRest) -> even <$> -- True if rest of string of sn's is even
    S.length_ (S.takeWhile (== sn) revRest)

-- | Drain and append a stream of symbols to the end of the
-- mesh. Assumes there is enough room in the underlying Doubly. Returns
-- the updated mesh, the new joints positions and the set of observed
-- symbols (i.e. those that had their counts increased)
append :: (PrimMonad m, Monad m) => Mesh m -> Stream (Of Sym) m r ->
          m (Mesh m, Joints, IntSet, r)
append msh@(Mesh mdl str jts) = (S.next >=>) $ \case
  Left r -> return (msh, M.empty, IS.empty, r)
  Right (s_0,ss) -> do
    i_n <- fromMaybe (error "empty Mesh") <$> D.lastKey str
    s_n <- D.read str i_n
    par <- checkParity str

    -- in one pass
    (observed :> (mdl' :> (am, str' :> r))) <-
      S.fold (flip IS.insert) IS.empty id $ -- record inc'd symbols
      S.foldM Mdl.incCount (return mdl) return $ S.copy $ -- inc Model counts
      S.map snd $ -- now, only for the Sym, dropping Index
      ( if par || s_0 /= s_n
        then Joints.fromStreamOdd_ (i_n,s_n) -- odd or different
        else Joints.fromStream_ ) M.empty $ S.copy $  -- even and same
      S.map fst $ -- drop every intermediate (Doubly m), keep (Index,Sym)
      fmap (S.first $ snd -- we only need the last (Doubly m), drop (Index,Sym)
            . fromJust) $ -- assume there is a last element
      S.last $ S.copy $ -- get last ((Index,Sym), Doubly m)
      S.drop 1 $ -- drop (error "_|_", str')
      S.scanM (\(_,l) s -> first (,s) . okSnoc <$> D.trySnoc l s) -- snoc
              (return (error "_|_", str)) return $
      S.yield s_0 >> ss

    let jts' = jts `Joints.union` am
    return (Mesh mdl' str' jts', am, observed, r)
  where
    okSnoc = fromMaybe $ error "Mesh.append: Underlying doubly linked list full"

-- | Add a rule and rewrite with progress bars
pushRule :: (PrimMonad m, MonadIO m) => Bool ->
            Mesh m -> (Sym,Sym) -> m (Sym, (Joints, Joints), Mesh m)
pushRule verifyModel (Mesh mdl str jts) (s0,s1) = do
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
