{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE InstanceSigs #-}
module Diagram.Source (module Diagram.Source) where

import Control.Monad hiding (join)
import Control.Monad.Primitive (PrimMonad(PrimState))

import Data.Word (Word8)
import Data.Maybe
import Data.Tuple.Extra
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Data.Trie (Trie)
import qualified Data.Trie as Trie
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS

import Streaming hiding (second,join)
import qualified Streaming.Prelude as S
import Diagram.Streaming () -- PrimMonad instance

import Diagram.Rules (Rules,Sym)
import qualified Diagram.Rules as R
import qualified Diagram.Doubly as Dly
import qualified Diagram.Dynamic as Dyn
import Diagram.Joints (Doubly)
import Diagram.Util

type DynVec m = Dyn.BoxedVec m

-- | Wrapper around a stream of bytes from source file to produce fully
-- constructed symbols on request.
data Source m r = Source {
  buffer :: !(Doubly (PrimState m)),    -- ^ Partial constructions
  bufExtension :: !ByteString,          -- ^ Extension of the buffer
  fwdRules :: !(Map (Sym,Sym) Sym),     -- ^ Construction rules (s0,s1) -> s01
  extensions :: !(DynVec m ByteString), -- ^ Extensions of each symbol
  partners :: !(DynVec m (Trie Sym)),   -- ^ Constructions by right partner
  atoms :: !(Stream (Of Word8) m r)     -- ^ Raw bytes from source file
}

instance Monad m => Functor (Source m) where
  fmap :: Monad m => (a -> b) -> Source m a -> Source m b
  fmap f src = src { atoms = fmap f (atoms src) }

new :: PrimMonad m => Rules -> Stream (Of Word8) m r -> m (Source m r)
new rs as = do
  buf <- Dly.new 8 -- arbitrary starting size
  exts <- Dyn.fromList $ BS.pack . R.extension rs <$> symbols
  tries <- Dyn.replicate numSymbols Trie.empty
  forM_ [256..numSymbols-1] $ \s -> do
    let (s0,s1) = rs R.! s
        ext = BS.pack $ R.extension rs s1
    Dyn.modify tries (Trie.insert ext s) s0
  return $ Source buf bufExt rsm exts tries as
  where
    numSymbols = R.numSymbols rs
    symbols = [0..numSymbols-1]
    bufExt = BS.empty
    rsm = R.toMap rs

pushRule :: PrimMonad m => (Sym, Sym) -> Sym -> Source m r -> m (Source m r)
pushRule s0s1@(s0,s1) s01 (Source buf bufExt rsm exts tries as) = do
  buf' <- S.foldM_ (Dly.subst2 s01) (return buf) return $
          Dly.streamKeysOfJoint buf s0s1
  ext0 <- Dyn.read exts s0
  ext1 <- Dyn.read exts s1
  let ext01 = ext0 <> ext1
  exts' <- Dyn.push exts ext01
  tries' <- Dyn.push tries Trie.empty
  Dyn.modify tries' (Trie.insert ext1 s01) s0
  -- (traceShow ("pushed",s0s1,s01) $ traceShowId rsm')
  return $ Source buf' bufExt rsm' exts' tries' as
  where
    rsm' = M.insert s0s1 s01 rsm

-- | Produce a stream of at most `n` fully constructed symbols from the
-- source, given a rule set equal or superset of any rule set previously
-- given to the source.
splitAt :: PrimMonad m => Rules -> Int -> Source m r ->
           Stream (Of Sym) m (Source m r)
splitAt rs = go
  where
    go n src | n <= 0 = return src
             | otherwise = (lift (next rs src) >>=) $ \case
                 Left r -> return $ src{ atoms = return r }
                 Right (s, src') -> S.yield s >> go (n-1) src'

-- | Produce a fully constructed symbol from the source, if not yet
-- empty, given a rule set equal or superset of any rule set previously
-- given to the source.
next :: forall m r. PrimMonad m =>
        Rules -> Source m r -> m (Either r (Sym, Source m r))
next rs (Source buf bufExt rsm exts tries as) = do
  robust <- (S.uncons (Dly.stream buf) >>=) $ \case
    Nothing -> return False
    Just (s0, ss) -> do
      len0 <- BS.length <$> Dyn.read exts s0
      checkRobust maxBound s0 ss $ BS.drop len0 bufExt

  -- pop a symbol
  if robust then (Dly.tryUncons buf >>=) $ \case
      Nothing -> error "impossible"
      Just (s,buf') -> do
        len <- BS.length <$> Dyn.read exts s
        let bufExt' = BS.drop len bufExt
        return $ Right (s, Source buf' bufExt' rsm exts tries as)

  -- read/append an atom + reduce
    else (S.next as >>=) $ \case
    Left r -> (Dly.tryUncons buf >>=) $ \case -- pop a symbol
      Nothing -> return $ Left r
      Just (s, buf') -> do
        len <- BS.length <$> Dyn.read exts s
        let bufExt' = BS.drop len bufExt
            as' = return r
        return $ Right (s, Source buf' bufExt' rsm exts tries as')

    Right (a, as') -> do
      buf' <- snocReduce buf $ fromEnum a -- Word8 -> Int
      let bufExt' = BS.snoc bufExt a
      next rs $ Source buf' bufExt' rsm exts tries as' -- rec

  where
    checkRobust :: Sym -> Sym -> Stream (Of Sym) m q -> ByteString -> m Bool
    checkRobust upperBound s0 ss ssExt  = do
      let sufs = R.suffixes rs s0
          bounds = upperBound : (min upperBound <$> init sufs)
      tries0 <- forM sufs $ Dyn.read tries
      -- that there exists a construction that is compatible with and
      -- extends further than the current buffer is proof the head is
      -- not robust
      let longer = concat $ zipWith (filter . (>)) bounds $
                   fmap (Trie.elems . Trie.submap ssExt) tries0
      if not (null longer) then return False else do
        -- if no construction is compatible with the current buffer
        -- (shorter or longer), then the symbol (and all those
        -- preceeding) is robust
        let shorter = concat $ zipWith (filter . (>)) bounds $
                      fmap (fmap snd3 . flip Trie.matches ssExt) tries0
        if null shorter then return True else (S.uncons ss >>=) $ \case
          -- otherwise if a certain head of the buffer could be a
          -- construction, we check if none of the following symbols are
          -- robust, with progress on the precedence
          Nothing -> return True
          Just (s0', ss') -> do
            let upperBound' = maximum shorter
            len0 <- BS.length <$> Dyn.read exts s0'
            let ssExt' = BS.drop len0 ssExt
            checkRobust upperBound' s0' ss' ssExt'

    snocReduce :: Doubly (PrimState m) -> Int -> m (Doubly (PrimState m))
    snocReduce ss s1 = ( -- traceShow ("snocReduce", s1, "on") (Dly.traceShow ss) >>
                         Dly.tryUnsnoc ss >>=) $ \case
      Nothing -> snd <$> Dly.snoc ss s1
      Just (ss',s0)
        | null constrs -> snd <$> (Dly.snoc ss' s0
                                   >>= flip Dly.snoc s1 . snd)
        | otherwise -> foldM snocReduce ss' recip01
                       >>= flip snocReduce s01
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
