{-# LANGUAGE LambdaCase, ScopedTypeVariables, TypeApplications #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
module Diagram (module Diagram) where

import System.Environment (getArgs)
import System.Exit

import Control.Monad
import Control.Monad.Primitive
import Control.Exception (evaluate)

import qualified Data.List as L
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import qualified Data.IntMap.Strict as IM
import qualified Data.ByteString as BS

import qualified Data.Vector.Unboxed as U
import qualified Data.Vector.Generic.Mutable as MV
import qualified Data.Vector.Strict as B

import Streaming hiding (first,second)
import qualified Streaming as S
import qualified Streaming.Prelude as S

import Diagram.Model
import qualified Diagram.Rules as R
import Diagram.Progress
import Diagram.Util

main :: IO ()
main = do
  args <- getArgs
  case args of
    [filename] -> do
      bytestring <- BS.readFile filename
      let len = BS.length bytestring
          as = BS.unpack bytestring
          mdl = fromAtoms as
          ss = fromEnum <$> as
      pb0 <- newPB len "Initializing joint counts"
      (m,()) <- countJointsM $
                S.mapM (\s -> incPB pb0 >> return s) $
                S.each ss
      go mdl ss m

    _else -> do
      putStrLn "Usage: program <filename>"
      exitFailure
  where
    go mdl@(Model rs _ _) ss !m = do
      pb1 <- newPB (M.size m) "Computing losses"
      cdts <- forM (M.toList m) $ \(s0s1,n01) -> do
                loss <- evaluate $ infoDelta mdl s0s1 n01
                incPB pb1
                return (loss, s0s1, n01)

      putStrLn "Sorting candidates..."
      (loss,(s0,s1),n01) <- case L.sort cdts of
        [] -> error "no candidates"
        (c:cdts') -> do
          putStrLn "Top candidates:"
          forM_ (c:take 4 cdts') (putStrLn . showCdt rs)
          putStrLn ""
          return c

      when (loss > 0) ( putStrLn "Reached minimum. Terminating." >>
                        exitSuccess )

      let (s01, mdl'@(Model _ n' _)) = push mdl (s0,s1) n01

      putStrLn "New rule:"
      putStrLn $ "[" ++ show s01 ++ "]: " ++ showJoint rs s0 s1

      ss' <- pbSeq n' "Rewriting string" $
             subst (s0,s1) s01 ss

      pb2 <- newPB n' "Updating counts"
      (am,rm,()) <- recountM (s0,s1) s01 $
                    S.mapM (\s -> incPB pb2 >> return s) $
                    S.each ss'

      go mdl' ss' $
        M.mergeWithKey (const $ nothingIf (== 0) .: (+)) id id am $
        M.differenceWith (nothingIf (== 0) .: (-)) m rm

    showCdt rs (loss,(s0,s1),n01) =
      show loss ++ ": "
      ++ showJoint rs s0 s1
      ++ " (" ++ show n01 ++ ")"

    showJoint rs s0 s1 = "\"" ++ R.toEscapedString rs [s0]
      ++ "\" + \"" ++ R.toEscapedString rs [s1]
      ++ "\" ==> \"" ++ R.toEscapedString rs [s0,s1] ++ "\" "
      ++ show (s0,s1)

    -- DEBUG --
    --       deltam = M.filter (uncurry (/=)) $ mergeMaps m' $
    --                countJoints ss'
    --   if not $ M.null deltam
    --     then error $ "counts discrepancy (updated,recounted): " ++ show deltam
    --          ++ "\njust added: "
    --          ++ show (mapMaybe (\k -> (k,) <$> (am M.!? k)) $
    --                    M.keys deltam)
    --          ++ "\njust removed: "
    --          ++ show (mapMaybe (\k -> (k,) <$> (rm M.!? k)) $
    --                    M.keys deltam )
    --     else go mdl' ss' m' -- continue
    -- mergeMaps :: Ord a => M.Map a b -> M.Map a b -> M.Map a (Maybe b, Maybe b)
    -- mergeMaps = M.mergeWithKey
    --  (\_ v1 v2 -> Just (Just v1, Just v2))
    --  (M.mapMaybeWithKey (\_ v1 -> Just (Just v1, Nothing)))
    --  (M.mapMaybeWithKey (\_ v2 -> Just (Nothing, Just v2)))

-- | Substitute a pair of symbols for a constructed joint symbol in a
-- string of symbols
subst :: (Int,Int) -> Int -> [Int] -> [Int]
subst (s0,s1) s01 = go
  where
    go [] = []
    go [s] = [s]
    go (s:s':ss) | s == s0 && s' == s1 = s01:go ss
                 | otherwise = s:go (s':ss)

-- | Count the changes in counts (additions, removals) concerning the
-- two parts of a newly substituted joint symbol in the given string
recountM :: forall m r. PrimMonad m => (Int,Int) -> Int ->
            Stream (Of Int) m r -> m ( Map (Int, Int) Int
                                     , Map (Int, Int) Int, r)
recountM (s0,s1) s01 str0 = do
  s0s1ref <- newPrimRef @U.MVector (0 :: Int) -- (s0,s1) (redundant but w/e)
  s1s0ref <- newPrimRef @U.MVector (0 :: Int) -- (s1,s0)
  prevvec <- MV.replicate @m @U.MVector s01 (0 :: Int) -- (i,s01)
  nextvec <- MV.replicate @m @U.MVector s01 (0 :: Int) -- (s01,i)
  autoref <- newPrimRef @U.MVector (0 :: Int) -- (s01,s01)
  correct <- newPrimRef @B.MVector IM.empty -- alignment correction

  let go :: Bool -> Int -> Stream (Of Int) m r -> m r
      go parity prev str = (S.next str >>=) $ \case
        Left r -> return r
        Right (s,ss)
          | s == s01 -> do
              MV.modify prevvec (+1) prev
              -- parity check on ...-prev-s0
              when (not parity && prev == s0) $
                modifyPrimRef correct $ IM.insertWith (+) prev 1
              goMatch ss

          | otherwise -> go (s == s0 && not parity) s ss

      -- the part of `go` without the `prev` part is needed at the start
      goMatch :: Stream (Of Int) m r -> m r
      goMatch ss = do
        n :> ss' <- fmap (S.first (+1)) $ S.length $ S.span (== s01) ss
        modifyPrimRef s0s1ref (+n)
        when (s0 /= s1) $ modifyPrimRef s1s0ref (+(n-1))

        modifyPrimRef autoref (+(n `div` 2))
        (S.next ss' >>=) $ \case
          Left r -> return r -- (end chunk; no next)
          Right (next,ss'') -> do -- (typical case)
            MV.modify nextvec (+1) next

            -- parity check on s1-next-...
            if s0 /= s1 && s1 == next then do
              n' :> ss''' <- S.length $ S.span (== next) ss''
              when (odd n') $
                modifyPrimRef correct $ IM.insertWith (+) next 1
              go (next == s0) next ss'''
              else do go (next == s0) next ss''

  r <- (S.next str0 >>=) $ \case
    Left r -> return r
    Right (s,ss) | s == s01 -> goMatch ss
                 | otherwise -> go (s == s0) s ss

  amref <- newPrimRef @B.MVector M.empty
  rmref <- newPrimRef @B.MVector M.empty

  -- read
  do n <- readPrimRef s0s1ref
     when (n > 0) $ modifyPrimRef rmref $ M.insert (s0,s1) n

  when (s0 /= s1) $ do
    n <- readPrimRef s1s0ref
    when (n > 0) $ modifyPrimRef rmref $ M.insert (s1,s0) n

  MV.iforM_ prevvec $ \prev n -> when (n > 0) $ do
    modifyPrimRef rmref $ M.insertWith (+) (prev,s0) n
    modifyPrimRef amref $ M.insert (prev,s01) n
  MV.iforM_ nextvec $ \next n -> when (n > 0) $ do
    when (s0 /= s1 || s1 /= next) $
      modifyPrimRef rmref $ M.insertWith (+) (s1,next) n
    modifyPrimRef amref $ M.insert (s01,next) n

  do n <- readPrimRef autoref
     when (n > 0) $ modifyPrimRef amref $ M.insert (s01,s01) n

  do im <- readPrimRef correct
     forM_ (IM.toList im) $ \(next,n) -> do
       modifyPrimRef amref $ M.insertWith (+) (next,next) n

  am <- readPrimRef amref
  rm <- readPrimRef rmref
  return (am, rm, r)

  where
    newPrimRef :: MV.MVector v a => a -> m (v (PrimState m) a)
    newPrimRef = MV.replicate 1
    modifyPrimRef :: MV.MVector v a => v (PrimState m) a -> (a -> a) -> m ()
    modifyPrimRef v f = MV.modify v f 0 -- TODO: unsafe
    readPrimRef :: MV.MVector v a => v (PrimState m) a -> m a
    readPrimRef = flip MV.read 0 -- TODO: unsafe

countJoints :: [Int] -> Map (Int,Int) Int
countJoints = go M.empty -- fst . runIdentity . countJointsM . S.each
  where
    go !m [] = m
    go !m [_] = m
    go !m [s0,s1] = M.insertWith (+) (s0,s1) 1 m
    go !m (s0:s1:s2:ss)
      | s0 == s1 && s1 == s2 = go m' (s2:ss)
      | otherwise = go m' (s1:s2:ss)
      where
        m' = M.insertWith (+) (s0,s1) 1 m

-- | (redundant) counts the joints concerning one symbol
countJointsOf :: Int -> [Int] -> Map (Int,Int) Int
countJointsOf s = go M.empty
  where
    go !m [] = m
    go !m [_] = m
    go !m (s0:s1:ss)
      | s0 == s || s1 == s = case ss of
          s2:_ | s0 == s1
               , s2 == s2 -> go m' ss
          _else -> go m' (s1:ss)
      | otherwise = go m (s1:ss)
      where
        m' = M.insertWith (+) (s0,s1) 1 m

countJointsM :: Monad m => Stream (Of Int) m r -> m (Map (Int,Int) Int, r)
countJointsM = go M.empty
  where
    inc s0s1 = M.insertWith (+) s0s1 1
    go !m ss = (S.next ss >>=) $ \case
      Left r -> return (m,r) -- end
      Right (s0,ss') -> (S.next ss' >>=) $ \case
        Left r -> return (m,r) -- singleton, end
        Right (s1,ss'') -> (S.next ss'' >>=) $ \case
          Left r -> return (inc (s0,s1) m, r) -- last joint
          Right (s2,ss''') -> go (inc (s0,s1) m) $ ms1 >> S.yield s2 >> ss'''
            where ms1 | s0 == s1 && s1 == s2 = return ()
                      | otherwise = S.yield s1
