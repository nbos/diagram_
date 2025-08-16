{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Doubly-linked list with random access
module Diagram.Doubly (module Diagram.Doubly) where

import Control.Monad
import Control.Monad.Primitive (PrimMonad(PrimState))

import Data.Primitive.MutVar
  (modifyMutVar, newMutVar, readMutVar, writeMutVar, MutVar)
import qualified Data.Vector.Strict as B -- change for Lazy
import qualified Data.Vector.Unboxed as U
import qualified Data.Vector.Generic.Mutable as MV

data Doubly s a = Doubly
  !(MutVar s (Maybe Int))  -- ^ head index
  !(MutVar s [Int])        -- ^ freed indexes
  !(B.MVector s (Maybe a)) -- ^ elements
  !(U.MVector s Int)       -- ^ previous indexes
  !(U.MVector s Int)       -- ^ next indexes

-- | Allocate a new list of the given size with undefined values
new :: PrimMonad m => Int -> m (Doubly (PrimState m) a)
new sz = do
  mi0 <- newMutVar Nothing
  free <- newMutVar [0..sz-1]
  elems <- MV.replicate sz Nothing
  prevs <- U.unsafeThaw (U.fromList ((sz-1):[0..sz-2]))
  nexts <- U.unsafeThaw (U.fromList ([1..sz-1]++[0]))
  return $ Doubly mi0 free elems prevs nexts

-- | Clone the data in the given list into a new list with `n`
-- additional free slots
grow :: PrimMonad m => Doubly (PrimState m) a -> Int ->
        m (Doubly (PrimState m) a)
grow (Doubly mi0 free elems nexts prevs) n = do
  mi0' <- newMutVar =<< readMutVar mi0
  let len = MV.length elems
      len' = len + n
  free' <- newMutVar . (++ [len..len'-1]) =<< readMutVar free
  elems' <- MV.grow elems n
  forM_ [len..len'-1] $ flip (MV.write elems') Nothing -- init.
  nexts' <- MV.grow nexts n
  prevs' <- MV.grow prevs n
  return $ Doubly mi0' free' elems' nexts' prevs'

-- | Construct a list from a list of values
fromList :: PrimMonad m => [a] -> m (Doubly (PrimState m) a)
fromList as = do
  mi0 <- newMutVar $ Just 0
  free <- newMutVar []
  elems <- B.unsafeThaw $ B.fromList $ Just <$> as
  let len = MV.length elems
  prevs <- U.unsafeThaw (U.fromList ((len-1):[0..len-2]))
  nexts <- U.unsafeThaw (U.fromList ([1..len-1]++[0]))
  return $ Doubly mi0 free elems prevs nexts

-- | Convert a list into a list
toList :: PrimMonad m => Doubly (PrimState m) a -> m [a]
toList (Doubly mi0 _ elems _ nexts) = (readMutVar mi0 >>=) $ \case
  Nothing -> return []
  Just i0 -> go i0
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

-- | Delete (and return) and seam previous with next
delete :: PrimMonad m => Doubly (PrimState m) a -> Int -> m a
delete (Doubly mi0 free elems nexts prevs) i = (readMutVar mi0 >>=) $ \case
  Nothing -> error "Doubly.delete: empty list"
  Just i0 -> (MV.read elems i >>=) $ \case
    Nothing -> error $ "Doubly.delete: no element at index " ++ show i
    Just a -> do
      prv <- MV.read prevs i  -- prev <- i
      nxt <- MV.read nexts i  --         i -> next
      when (i == i0) $ writeMutVar mi0 $ Just nxt
      modifyMutVar free (i:)
      MV.write prevs nxt prv -- prev <-( )-- next
      MV.write nexts prv nxt -- prev --( )-> next
      return a

-- TODO: cons and snoc could probably be better factored

-- | Add an element at the begining of the list. Grows the structure in
-- case there is no free spaces.
cons :: PrimMonad m => a -> Doubly (PrimState m) a ->
                       m (Doubly (PrimState m) a)
cons a l@(Doubly mi0 free elems nexts prevs) = (readMutVar mi0 >>=) $ \case
  Nothing -> (readMutVar free >>=) $ \case
    [] -> fromList [a] -- singleton
    i:free' -> do
      writeMutVar mi0 $ Just i
      writeMutVar free free'
      MV.write elems i $ Just a
      MV.write nexts i i
      MV.write prevs i i
      return l

  Just i0 -> (readMutVar free >>=) $ \case
    [] -> cons a =<< grow l (max 1 $ MV.length elems)
    i:free' -> do
      writeMutVar mi0 $ Just i
      writeMutVar free free'
      MV.write elems i $ Just a

      -- i0 (old head)
      i_n <- MV.read prevs i0
      MV.write prevs i0 i

      -- i_n (last)
      MV.write nexts i_n i

      -- i (new head)
      MV.write prevs i i_n
      MV.write nexts i i0

      return l

-- | Add an element at the end of the list. Grows the structure in case
-- there is no free spaces.
snoc :: PrimMonad m => Doubly (PrimState m) a -> a ->
                       m (Doubly (PrimState m) a)
snoc l@(Doubly mi0 free elems nexts prevs) a = (readMutVar mi0 >>=) $ \case
  Nothing -> (readMutVar free >>=) $ \case
    [] -> fromList [a] -- singleton
    i:free' -> do
      writeMutVar mi0 $ Just i
      writeMutVar free free'
      MV.write elems i $ Just a
      MV.write nexts i i
      MV.write prevs i i
      return l

  Just i0 -> (readMutVar free >>=) $ \case
    [] -> flip snoc a =<< grow l (max 1 $ MV.length elems)
    i:free' -> do
      writeMutVar free free'
      MV.write elems i $ Just a

      -- i_p (old last)
      i_n <- MV.read prevs i0
      MV.write nexts i_n i

      -- i0 (head)
      MV.write prevs i0 i

      -- i (new last)
      MV.write prevs i i_n
      MV.write nexts i i0

      return l
