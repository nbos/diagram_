-- | Doubly-linked list with random access
module Diagram.Doubly (module Diagram.Doubly) where

import Control.Monad
import Control.Monad.Primitive (PrimMonad(PrimState))

import Streaming
import qualified Streaming.Prelude as S

import Data.Maybe
import qualified Data.Vector.Strict as B
import qualified Data.Vector.Unboxed as U
import qualified Data.Vector.Generic.Mutable as MV

data Doubly s a = Doubly
  !(Maybe Int)       -- ^ head index
  ![Int]             -- ^ freed indexes
  !(B.MVector s a)   -- ^ elements
  !(U.MVector s Int) -- ^ previous indexes
  !(U.MVector s Int) -- ^ next indexes

-- | Allocate a new list of the given size with undefined values
new :: PrimMonad m => Int -> m (Doubly (PrimState m) a)
new sz = do
  elems <- MV.new sz
  prevs <- U.unsafeThaw (U.fromList ((sz-1):[0..sz-2]))
  nexts <- U.unsafeThaw (U.fromList ([1..sz-1]++[0]))
  return $ Doubly Nothing [0..sz-1] elems prevs nexts

capacity :: Doubly s a -> Int
capacity (Doubly _ _ elems _ _) = MV.length elems

full :: Doubly s a -> Bool
full (Doubly _ [] _ _ _) = True
full _ = False

-- | Clone the data in the given list into a new list with `n`
-- additional free slots
grow :: PrimMonad m => Doubly (PrimState m) a -> Int ->
        m (Doubly (PrimState m) a)
grow (Doubly mi0 free elems nexts prevs) n = do
  let len = MV.length elems
      len' = len + n
      free' = free ++ [len..len'-1]
  elems' <- MV.grow elems n
  -- forM_ [len..len'-1] $ flip (MV.write elems') Nothing -- init.
  nexts' <- MV.grow nexts n
  prevs' <- MV.grow prevs n
  return $ Doubly mi0 free' elems' nexts' prevs'

-- | Construct a doubly-linked list from a singly-linked list
fromList :: PrimMonad m => [a] -> m (Doubly (PrimState m) a)
fromList as = do
  elems <- B.unsafeThaw $ B.fromList as
  let len = MV.length elems
  prevs <- U.unsafeThaw (U.fromList ((len-1):[0..len-2]))
  nexts <- U.unsafeThaw (U.fromList ([1..len-1]++[0]))
  return $ Doubly (Just 0) [] elems prevs nexts

-- | Read the doubly-linked list into a singly-linked list. Use toStream
-- to not @sequence@ the reads.
toList :: PrimMonad m => Doubly (PrimState m) a -> m [a]
toList (Doubly Nothing _ _ _ _) = return [] -- empty
toList (Doubly (Just i0) _ elems _ nexts) = go i0
  where
    go i = do a <- MV.read elems i
              nxt <- MV.read nexts i
              if nxt == i0
                then return [a] -- looped back
                else (a:) <$> go nxt -- cont.

toStream :: PrimMonad m => Doubly (PrimState m) a -> Stream (Of a) m ()
toStream (Doubly Nothing _ _ _ _) = return () -- empty
toStream (Doubly (Just i0) _ elems _ nexts) = go i0
  where
    go i = do a <- lift $ MV.read elems i
              nxt <- lift $ MV.read nexts i
              S.yield a
              when (nxt /= i0) $ go nxt -- cont.

-- | Read the doubly-linked list into a singly-linked list in reverse
-- order. Use toRevStream to not @sequence@ the reads.
toRevList :: PrimMonad m => Doubly (PrimState m) a -> m [a]
toRevList (Doubly Nothing _ _ _ _) = return [] -- empty
toRevList (Doubly (Just i0) _ elems prevs _) = go i0
  where
    go i = do a <- MV.read elems i
              prv <- MV.read prevs i
              if prv == i0
                then return [a] -- looped back
                else (a:) <$> go prv -- cont.

toRevStream :: PrimMonad m => Doubly (PrimState m) a -> Stream (Of a) m ()
toRevStream (Doubly Nothing _ _ _ _) = return () -- empty
toRevStream (Doubly (Just i0) _ elems prevs _) = go i0
  where
    go i = do a <- lift $ MV.read elems i
              prv <- lift $ MV.read prevs i
              S.yield a
              when (prv /= i0) $ go prv -- cont.

read :: PrimMonad m => Doubly (PrimState m) a -> Int -> m a
read (Doubly _ _ elems _ _) = MV.read elems

-- | Return the index of the element preceeding the element at a given
-- index in the list
prev :: PrimMonad m => Doubly (PrimState m) a -> Int -> m Int
prev (Doubly _ _ _ _ prevs) = MV.read prevs

-- | Return the index of the element following the element at a given
-- index in the list
next :: PrimMonad m => Doubly (PrimState m) a -> Int -> m Int
next (Doubly _ _ _ nexts _) = MV.read nexts

-- | Modify an element at a given index. Throws an error if index is
-- undefined
modify :: PrimMonad m => Doubly (PrimState m) a -> (a -> a) -> Int -> m ()
modify (Doubly _ _ elems _ _) = MV.modify elems

-- | Delete the element at a given index and seam previous with next.
delete :: PrimMonad m => Doubly (PrimState m) a -> Int ->
                         m (Doubly (PrimState m) a)
delete l@(Doubly Nothing _ _ _ _) _ = return l -- empty ==> empty
delete (Doubly mi0@(Just i0) free elems prevs nexts) i = do
    prv <- MV.read prevs i -- prev <- i
    nxt <- MV.read nexts i --         i -> next
    MV.write prevs nxt prv -- prev <-( )-- next
    MV.write nexts prv nxt -- prev --( )-> next
    let mi0' | prv == nxt = Nothing -- singleton ==> empty
             | i   == i0  = Just nxt
             | otherwise  = mi0
    return $ Doubly mi0' (i:free) elems prevs nexts

-- | Append an element at the begining of the list. Grows the structure
-- in case there are no free spaces.
cons :: PrimMonad m => a -> Doubly (PrimState m) a ->
                       m (Doubly (PrimState m) a)
cons a l = fromMaybe (grow l (max 1 $ capacity l) >>= cons a) $
           tryCons a l

-- | Try to append an element at the beginning of the list, if the
-- capacity allows it.
tryCons :: PrimMonad m => a -> Doubly (PrimState m) a ->
                          Maybe (m (Doubly (PrimState m) a))
tryCons _ (Doubly _ [] _ _ _) = Nothing
tryCons a (Doubly Nothing (i:free) elems prevs nexts) = Just $ do
  MV.write elems i a
  MV.write nexts i i
  MV.write prevs i i
  return $ Doubly (Just i) free elems prevs nexts

tryCons a (Doubly (Just i0) (i:free) elems prevs nexts) = Just $ do
  -- i0 (old head)
  i_n <- MV.read prevs i0 -- get last
  MV.write prevs i0 i

  -- i_n (last)
  MV.write nexts i_n i

  -- i (new head)
  MV.write elems i a
  MV.write prevs i i_n
  MV.write nexts i i0

  return $ Doubly (Just i) free elems prevs nexts
{-# INLINABLE tryCons #-}

-- | Append an element to the end of the list. Grows the structure in
-- case there are no free spaces.
snoc :: PrimMonad m => Doubly (PrimState m) a -> a ->
                       m (Doubly (PrimState m) a)
snoc l a = fromMaybe (grow l (max 1 $ capacity l) >>= flip snoc a) $
           trySnoc l a

-- | Try to append an element to the end of the list, if the capacity
-- allows it.
trySnoc :: PrimMonad m => Doubly (PrimState m) a -> a ->
                          Maybe (m (Doubly (PrimState m) a))
trySnoc (Doubly _ [] _ _ _) _ = Nothing
trySnoc (Doubly Nothing (i:free) elems nexts prevs) a = Just $ do
  MV.write elems i a
  MV.write nexts i i
  MV.write prevs i i
  return $ Doubly (Just i) free elems nexts prevs

trySnoc (Doubly (Just i0) (i:free) elems nexts prevs) a = Just $ do
  -- i0 (head)
  i_n <- MV.read prevs i0 -- get last
  MV.write prevs i0 i

  -- i_n (old last)
  MV.write nexts i_n i

  -- i (new last)
  MV.write elems i a
  MV.write prevs i i_n
  MV.write nexts i i0

  return $ Doubly (Just i0) free elems nexts prevs
{-# INLINABLE trySnoc #-}

-- | Shift the list left by 1, placing the first element last
shiftL :: PrimMonad m => Doubly (PrimState m) a -> m (Doubly (PrimState m) a)
shiftL l@(Doubly Nothing _ _ _ _) = return l
shiftL (Doubly (Just i0) free elems prevs nexts) = do
  i1 <- MV.read nexts i0
  return $ Doubly (Just i1) free elems prevs nexts

-- | Shift the list right by 1, placing the last element first
shiftR :: PrimMonad m => Doubly (PrimState m) a -> m (Doubly (PrimState m) a)
shiftR l@(Doubly Nothing _ _ _ _) = return l
shiftR (Doubly (Just i0) free elems prevs nexts) = do
  i_n <- MV.read prevs i0
  return $ Doubly (Just i_n) free elems prevs nexts
