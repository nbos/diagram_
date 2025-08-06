{-# LANGUAGE LambdaCase, TupleSections, ScopedTypeVariables, TypeApplications #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
module Diagram (module Diagram) where

import Debug.Trace
import System.Environment (getArgs)
import System.Exit

import Control.Monad
import Control.Monad.ST
import Control.Exception (evaluate)
import Control.Monad.State.Strict

import Data.STRef
import Data.Maybe
import Data.Tuple.Extra
import qualified Data.List as L
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import qualified Data.ByteString as BS

import qualified Data.Vector.Unboxed as U
import qualified Data.Vector.Generic.Mutable as MV

import Streaming hiding (first,second)
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

      traceShow mdl' $ putStrLn "New rule:"
      putStrLn $ "[" ++ show s01 ++ "]: " ++ showJoint rs s0 s1

      pb2 <- newPB n' "Rewriting string"
      (ss', (am,rm)) <- fmap S.lazily $ S.toList $
                        S.mapM (\s -> incPB pb2 >> return s) $
                        rewriteM (s0,s1) s01 ss

      let m' = M.unionWith (+) am $
               M.differenceWith (nothingIf (== 0) .: (-)) m rm

    -- TODO : remove DEBUG --

          deltam = M.filter (uncurry (/=)) $ mergeMaps  m' $
                   countJoints ss'

      if not $ M.null deltam
        then error $ "counts discrepancy (act,exp): " ++ show deltam
             ++ "\njust added: "
             ++ show (mapMaybe (\k -> (k,) <$> (am M.!? k)) $
                       M.keys deltam)
             ++ "\njust removed: "
             ++ show (mapMaybe (\k -> (k,) <$> (rm M.!? k)) $
                       M.keys deltam )

        else go mdl' ss' m' -- continue

    mergeMaps :: Ord a => M.Map a b -> M.Map a b -> M.Map a (Maybe b, Maybe b)
    mergeMaps = M.mergeWithKey
     (\_ v1 v2 -> Just (Just v1, Just v2))
     (M.mapMaybeWithKey (\_ v1 -> Just (Just v1, Nothing)))
     (M.mapMaybeWithKey (\_ v2 -> Just (Nothing, Just v2)))

    --

    showCdt rs (loss,(s0,s1),n01) =
      show loss ++ ": "
      ++ showJoint rs s0 s1
      ++ " (" ++ show n01 ++ ")"

    showJoint rs s0 s1 = "\"" ++ R.toEscapedString rs [s0]
      ++ "\" + \"" ++ R.toEscapedString rs [s1]
      ++ "\" ==> \"" ++ R.toEscapedString rs [s0,s1] ++ "\""

rewrite :: (Int, Int) -> Int -> [Int] -> ([Int], ( Map (Int, Int) Int
                                                 , Map (Int, Int) Int ))
rewrite = S.lazily . runIdentity . S.toList .:. rewriteM

rewriteM :: forall m. Monad m => (Int, Int) -> Int -> [Int] ->
            Stream (Of Int) m ( Map (Int, Int) Int
                              , Map (Int, Int) Int )
rewriteM = undefined

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
recount :: (Int,Int) -> Int -> [Int] -> ( Map (Int, Int) Int
                                        , Map (Int, Int) Int )
recount (s0,s1) s01 str = runST $ do
  s0s1ref <- newSTRef (0 :: Int) -- (s0,s1) (redundant but w/e)
  s1s0ref <- newSTRef (0 :: Int) -- (s1,s0)
  prevvec <- MV.replicate @_ @U.MVector s01 (0 :: Int) -- (i,s01)
  nextvec <- MV.replicate @_ @U.MVector s01 (0 :: Int) -- (s01,i)
  autoref <- newSTRef (0 :: Int) -- (s01,s01)

  let go _ [] = return ()
      go prev (s:ss)
        | s == s01 = case first ((+1) . length) $ span (== s01) ss of
            (n, next:ss') -> do -- (typical case)
              modifySTRef' s0s1ref (+n)
              when (s0 /= s1) $ modifySTRef' s1s0ref (+(n-1))
              MV.modify prevvec (+1) prev
              when (s0 /= s1 || s1 /= next) $ MV.modify nextvec (+1) next
              modifySTRef' autoref (+(n `div` 2))
              go next ss' -- continue

            (n, []) -> do -- (end chunk; no next)
              modifySTRef' s0s1ref (+n)
              when (s0 /= s1) $ modifySTRef' s1s0ref (+(n-1))
              MV.modify prevvec (+1) prev
              modifySTRef' autoref (+(n `div` 2))

        | otherwise = go s ss -- continue

  case str of
    [] -> return ()
    (s:ss)
      | s == s01 -> do -- (start chunk, no prev)
          case first ((+1) . length) $ span (== s01) ss of
            (n, next:ss') -> do
              modifySTRef' s0s1ref (+n)
              when (s0 /= s1) $ modifySTRef' s1s0ref (+(n-1))
              when (s0 /= s1 || s1 /= next) $ MV.modify nextvec (+1) next
              modifySTRef' autoref (+(n `div` 2))
              go next ss' -- go

            (n, []) -> do -- (just s01s, no prev, no next)
              modifySTRef' s0s1ref (+n)
              when (s0 /= s1) $ modifySTRef' s1s0ref (+(n-1))
              modifySTRef' autoref (+(n `div` 2))

      | otherwise -> go s ss -- go

  amref <- newSTRef M.empty
  rmref <- newSTRef M.empty

  -- read
  modifySTRef' rmref . M.insert (s0,s1) =<< readSTRef s0s1ref
  modifySTRef' rmref . M.insert (s1,s0) =<< readSTRef s1s0ref
  MV.iforM_ prevvec $ \prev n -> when (n > 0) $ do
    modifySTRef' rmref $ M.insert (prev,s0) n
    modifySTRef' amref $ M.insert (prev,s01) n
  MV.iforM_ nextvec $ \next n -> when (n > 0) $ do
    modifySTRef' rmref $ M.insert (s1,next) n
    modifySTRef' amref $ M.insert (s01,next) n
  modifySTRef' amref . M.insert (s01,s01) =<< readSTRef autoref

  am <- readSTRef amref
  rm <- readSTRef rmref
  return (am, rm)

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
