{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Doubly-linked list with random access
module Diagram.Doubly (module Diagram.Doubly) where

import Control.Monad
import Control.Monad.Primitive (PrimMonad(PrimState))

-- import Data.Primitive.MutVar
--   (modifyMutVar, newMutVar, readMutVar, writeMutVar, MutVar)
import qualified Data.Vector.Strict as B -- change for Lazy
import qualified Data.Vector.Unboxed as U
import qualified Data.Vector.Generic.Mutable as MV

data Doubly s a = Doubly
  !(Maybe Int)             -- ^ head index
  ![Int]                   -- ^ freed indexes
  !(B.MVector s (Maybe a)) -- ^ elements
  !(U.MVector s Int)       -- ^ previous indexes
  !(U.MVector s Int)       -- ^ next indexes

-- | Allocate a new list of the given size with undefined values
new :: PrimMonad m => Int -> m (Doubly (PrimState m) a)
new sz = do
  elems <- MV.replicate sz Nothing
  prevs <- U.unsafeThaw (U.fromList ((sz-1):[0..sz-2]))
  nexts <- U.unsafeThaw (U.fromList ([1..sz-1]++[0]))
  return $ Doubly Nothing [0..sz-1] elems prevs nexts

-- | Clone the data in the given list into a new list with `n`
-- additional free slots
grow :: PrimMonad m => Doubly (PrimState m) a -> Int ->
        m (Doubly (PrimState m) a)
grow (Doubly mi0 free elems nexts prevs) n = do
  let len = MV.length elems
      len' = len + n
      free' = free ++ [len..len'-1]
  elems' <- MV.grow elems n
  forM_ [len..len'-1] $ flip (MV.write elems') Nothing -- init.
  nexts' <- MV.grow nexts n
  prevs' <- MV.grow prevs n
  return $ Doubly mi0 free' elems' nexts' prevs'

-- | Construct a doubly-linked list from a singly-linked list
fromList :: PrimMonad m => [a] -> m (Doubly (PrimState m) a)
fromList as = do
  elems <- B.unsafeThaw $ B.fromList $ Just <$> as
  let len = MV.length elems
  prevs <- U.unsafeThaw (U.fromList ((len-1):[0..len-2]))
  nexts <- U.unsafeThaw (U.fromList ([1..len-1]++[0]))
  return $ Doubly (Just 0) [] elems prevs nexts

-- | Read the doubly-linked list into a singly-linked list
toList :: PrimMonad m => Doubly (PrimState m) a -> m [a]
toList (Doubly Nothing _ _ _ _) = return []
toList (Doubly (Just i0) _ elems _ nexts) = go i0
    where
      go i = (MV.read elems i >>=) $ \case
        Nothing -> return []
        Just x -> do nxt <- MV.read nexts i
                     if nxt == i0
                       then return [x] -- looped back
                       else (x:) <$> go nxt -- cont.

read :: PrimMonad m => Doubly (PrimState m) a -> Int -> m (Maybe a)
read (Doubly _ _ elems _ _) = MV.read elems

-- | Return the index of the element preceeding the element at a given
-- index in the list
prev :: PrimMonad m => Doubly (PrimState m) a -> Int -> m Int
prev (Doubly _ _ elems _ prevs) i = (MV.read elems i >>=) $ \case
  Nothing -> error $ "Doubly.prev: no element at index " ++ show i
  Just _ -> MV.read prevs i

-- | Return the index of the element following the element at a given
-- index in the list
next :: PrimMonad m => Doubly (PrimState m) a -> Int -> m Int
next (Doubly _ _ elems nexts _) i = (MV.read elems i >>=) $ \case
  Nothing -> error $ "Doubly.next: no element at index " ++ show i
  Just _ -> MV.read nexts i

-- | Modify an element at a given index. Throws an error if index is
-- undefined
modify :: PrimMonad m => Doubly (PrimState m) a -> (a -> a) -> Int -> m ()
modify (Doubly _ _ elems _ _) f i = flip (MV.modify elems) i $ \case
  Nothing -> error $ "Doubly.modify: no element at index " ++ show i
  Just a -> Just $ f a

-- | Delete (and return) the element at a given index and seam previous
-- with next
delete :: PrimMonad m => Doubly (PrimState m) a -> Int ->
          m (a, Doubly (PrimState m) a)
delete (Doubly Nothing _ _ _ _) _ = error "Doubly.delete: empty list"
delete (Doubly mi0@(Just i0) free elems nexts prevs) i =
  (MV.read elems i >>=) $ \case
  Nothing -> error $ "Doubly.delete: no element at index " ++ show i
  Just a -> do
    prv <- MV.read prevs i -- prev <- i
    nxt <- MV.read nexts i --         i -> next
    MV.write prevs nxt prv -- prev <-( )-- next
    MV.write nexts prv nxt -- prev --( )-> next
    let mi0' | prv == nxt = Nothing
             | i == i0    = Just nxt
             | otherwise  = mi0
    return (a, Doubly mi0' (i:free) elems nexts prevs)

-- TODO: cons and snoc could probably be better factored

-- | Add an element at the begining of the list. Grows the structure in
-- case there is no free spaces.
cons :: PrimMonad m => a -> Doubly (PrimState m) a ->
                       m (Doubly (PrimState m) a)
cons a l@(Doubly _ [] elems _ _) = grow l (max 1 $ MV.length elems)
                                   >>= cons a
cons a (Doubly Nothing (i:free) elems nexts prevs) = do
  MV.write elems i $ Just a
  MV.write nexts i i
  MV.write prevs i i
  return $ Doubly (Just i) free elems nexts prevs

cons a (Doubly (Just i0) (i:free) elems nexts prevs) = do
  -- i0 (old head)
  i_n <- MV.read prevs i0 -- get last
  MV.write prevs i0 i

  -- i_n (last)
  MV.write nexts i_n i

  -- i (new head)
  MV.write elems i $ Just a
  MV.write prevs i i_n
  MV.write nexts i i0

  return $ Doubly (Just i) free elems nexts prevs
