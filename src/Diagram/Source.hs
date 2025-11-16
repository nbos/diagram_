{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections, LambdaCase #-}
{-# LANGUAGE InstanceSigs #-}
module Diagram.Source (module Diagram.Source) where

import Control.Monad hiding (join)
import Control.Monad.Primitive (PrimMonad(PrimState))

import Data.Word (Word8)
import Data.Maybe
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IM
import Data.Trie (Trie)
import qualified Data.Trie as Trie
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS

import Streaming hiding (second,join)
import qualified Streaming.Prelude as S
import Diagram.Streaming () -- PrimMonad instance

import Diagram.Rules (Rules,Sym)
import qualified Diagram.Rules as R
import qualified Diagram.Doubly as D
import Diagram.Joints (Doubly)
import Diagram.Util

-- | Wrapper around a stream of bytes from source file to optimally
-- produce fully constructed symbols upon request.
data Source m r = Source {
  buffer :: !(Doubly (PrimState m)),  -- ^ Partial constructions
  bufExt :: !ByteString,              -- ^ Extension of the buffer
  fwdRules :: !(Map (Sym,Sym) Sym),   -- ^ Construction rules (s0,s1) -> s01
  extensions :: !(IntMap ByteString), -- ^ Extensions by symbol
  extTrie :: !(Trie ()),              -- ^ Extensions trie
  atoms :: !(Stream (Of Word8) m r)   -- ^ Raw bytes from source file
}

instance Monad m => Functor (Source m) where
  fmap :: Monad m => (a -> b) -> Source m a -> Source m b
  fmap f src = src { atoms = fmap f (atoms src) }

new :: PrimMonad m => Rules -> Stream (Of Word8) m r -> m (Source m r)
new rs as = do
  buf <- D.new 10
  return $ Source buf bs rsm im trie as
  where
    numSymbols = R.numSymbols rs
    bs = BS.empty
    rsm = R.toMap rs
    exts = BS.pack . R.extension rs <$> [0..numSymbols-1]
    im = IM.fromDistinctAscList $ zip [0..numSymbols-1] exts
    trie = Trie.fromList $ (,()) <$> exts

pushRule :: PrimMonad m => (Sym, Sym) -> Sym -> Source m r -> m (Source m r)
pushRule s0s1 s01 (Source buf bs rsm im trie as) = do
  buf' <- S.foldM_ (D.subst2 s01) (return buf) return $
          D.streamKeysOfJoint buf s0s1
  -- (traceShow ("pushed",s0s1,s01) $ traceShowId rsm')
  return $ Source buf' bs rsm' im' trie' as
  where
    rsm' = M.insert s0s1 s01 rsm
    e01 = (im IM.! fst s0s1) <> (im IM.! snd s0s1)
    im' = IM.insert s01 e01 im
    trie' = Trie.insert e01 () trie

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
next rs (Source buf bs rsm im trie as)
  -- -- | traceShow (bs,notAPrefix,exts) False = undefined
  | notAPrefix = (D.tryUncons buf >>=) $ \case -- pop a symbol
      Nothing -> error "impossible"
      Just (s,buf') -> return $ Right (s, Source buf' bs' rsm im trie as)
          where bs' = BS.drop (BS.length $ im IM.! s) bs

  | otherwise = (S.next as >>=) $ \case -- read/append an atom
      Left r -> (D.tryUncons buf >>=) $ \case -- pop a symbol
        Nothing -> return $ Left r
        Just (s,buf') -> return $ Right (s, Source buf' bs' rsm im trie as')
          where bs' = BS.drop (BS.length $ im IM.! s) bs
                as' = return r

      Right (a, as') -> do
        buf' <- snocReduce buf $ fromEnum a -- Word8 -> Int
        let bs' = BS.snoc bs a
        next rs $ Source buf' bs' rsm im trie as' -- rec

  where
    exts = Trie.keys $ Trie.submap bs trie
    notAPrefix = not (BS.null bs) -- short circuit in case exts not lazy
                 && (null exts || exts == [bs])

    snocReduce :: Doubly (PrimState m) -> Int -> m (Doubly (PrimState m))
    snocReduce ss s1 = ( -- traceShow ("snocReduce", s1, "on") (D.traceShow ss) >>
                        D.lastElem ss >>=) $ \case
      Just s0 | not (null constrs) -> foldM snocReduce ss recip01
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

      _else -> snd <$> D.snoc ss s1 -- drop index
