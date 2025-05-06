{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Diagram.Trie (module Diagram.Trie) where

import Data.Word
import Data.Tuple.Extra
import Data.Trie (Trie(..))
import qualified Data.Trie as Trie
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS

import Streaming
import qualified Streaming.Prelude as S

err :: [Char] -> a
err = error . ("Diagram.Trie: " ++)

-- | Iteratively double the length of the query by fishing bytes in the
-- stream until the bottom of the trie is reached and return the lineage
-- from root to bottom without having to consume the whole stream (snd),
-- with the key that reached the bottom (fst) and the rest of the stream
-- (thd)
resolveGeneric :: forall a m r. Monad m =>
                  ByteString -> Trie a -> Stream (Of Word8) m r ->
                  m (ByteString, [a], Stream (Of Word8) m r)
resolveGeneric hd0 trie = go hd0
  where
    go :: ByteString -> Stream (Of Word8) m r ->
          m (ByteString, [a], Stream (Of Word8) m r)
    go hd tl = do
      let n = max 1 $ BS.length hd -- TODO: profile values > 1
      more :> tl' <- S.toList $ S.splitAt n tl
      let hd' = hd <> BS.pack more
          subtrie = Trie.submap hd' trie
      if Trie.null subtrie
        then return (hd', snd3 <$> Trie.matches trie hd', tl')
        else go hd' tl'
{-# INLINE resolveGeneric #-}

-- | Map a function to the elements of a trie, from the root to the
-- leaves, while the function returns `Just`s. If the function returns
-- `Nothing`, the element is not changed nor are any of its children
-- (values whose keys have it as prefix)
mapWhile :: (a -> Maybe a) -> Trie a -> Trie a
mapWhile _ Trie.Empty = Trie.Empty
mapWhile f (Trie.Branch p m tr0 tr1) =
  Trie.Branch p m (mapWhile f tr0) (mapWhile f tr1)
mapWhile f (Trie.Arc bs Nothing tr) =
  Trie.Arc bs Nothing $ mapWhile f tr
mapWhile f tr@(Trie.Arc bs (Just t) str) = case f t of
  Nothing -> tr
  Just t' -> Trie.Arc bs (Just t') $ mapWhile f str

-- | Compute a sum over the trie as long as values produce `Just` under
-- the given function, interrupting recursions upon `Nothing`
catWhile :: Monoid b => (a -> Maybe b) -> Trie a -> b
catWhile _ Trie.Empty = mempty
catWhile f (Trie.Branch _ _ tr0 tr1) =
  catWhile f tr0 <> catWhile f tr1
catWhile f (Trie.Arc _ Nothing tr) = catWhile f tr
catWhile f (Trie.Arc _ (Just t) str) = case f t of
  Nothing -> mempty
  Just b -> b <> catWhile f str

-- | A combination of `mapWhile` and `catWhile`
mapAccumWhile :: Monoid b => (a -> Maybe (b, a)) -> Trie a -> (b, Trie a)
mapAccumWhile _ Trie.Empty = (mempty, Trie.Empty)
mapAccumWhile f (Trie.Branch p m tr0 tr1) =
  let (b0, tr0') = mapAccumWhile f tr0
      (b1, tr1') = mapAccumWhile f tr1
  in (b0 <> b1, Trie.Branch p m tr0' tr1')
mapAccumWhile f (Trie.Arc bs Nothing tr) =
  Trie.Arc bs Nothing <$> mapAccumWhile f tr
mapAccumWhile f tr@(Trie.Arc bs (Just t) str) = case f t of
  Nothing -> (mempty, tr)
  Just (b, t') -> (b <>) *** Trie.Arc bs (Just t') $
                  mapAccumWhile f str

-- | Map a function to the first value in the trie by prefix order
mapRoot :: (a -> a) -> Trie a -> Trie a
mapRoot f trie = case Trie.minMatch trie BS.empty of
  Nothing -> trie
  Just (k, v, _) -> Trie.insert k (f v) trie

-- | Map a function to the first value in the trie by prefix order
mapRootF :: Functor f => (a -> f a) -> Trie a -> f (Trie a)
mapRootF f trie = case Trie.minMatch trie BS.empty of
  Nothing -> err "mapRootF: no root"
  Just (k, v, _) -> flip (Trie.insert k) trie <$> f v

mapSubtrie :: (Trie a -> Trie a) -> ByteString -> Trie a -> Trie a
mapSubtrie f k trie = Trie.mergeBy (err "Conflicting tries")
                      (f subtrie) rest
  where
    subtrie = Trie.submap k trie
    rest = Trie.deleteSubmap k trie
