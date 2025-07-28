{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
module Diagram where

import Debug.Trace
import System.Environment (getArgs)
import System.Exit
import System.ProgressBar

import Control.Monad
import Control.Exception (evaluate)
import qualified Data.List as L
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import qualified Data.ByteString as BS

import Streaming
import qualified Streaming.Prelude as S

import Diagram.Model
import qualified Diagram.Rules as R
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

      when (loss > 0) ( putStrLn "Reached minimum. Terminating."
                        >> exitSuccess )

      let (s01, mdl'@(Model _ n' _)) = push mdl (s0,s1) n01

      traceShow mdl' $ putStrLn "New rule:"
      putStrLn $ "[" ++ show s01 ++ "]: " ++ showJoint rs s0 s1

      pb2 <- newPB n' "Rewriting string"
      (ss', deltas) <- fmap S.lazily $ S.toList $
                       S.mapM (\s -> incPB pb2 >> return s) $
                       rewrite (s0,s1) s01 ss

      let m' = M.differenceWith (nothingIf (== 0) .: (+)) m deltas

          -- TODO : remove DEBUG --
          deltam = M.differenceWith (nothingIf (== 0) .: (+)) m' $
                   (0-) <$> countJoints ss'
      if not $ M.null deltam then error $ "counts discrepancy: " ++ show deltam
      else go mdl' ss' m' -- continue

    showCdt rs (loss,(s0,s1),n01) =
      show loss ++ ": "
      ++ showJoint rs s0 s1
      ++ " (" ++ show n01 ++ ")"

    showJoint rs s0 s1 = "\"" ++ R.toString rs [s0]
      ++ "\" + \"" ++ R.toString rs [s1]
      ++ "\" ==> \"" ++ R.toString rs [s0,s1] ++ "\""

    newPB n message = newProgressBar style 10 (Progress 0 n ())
      where
        style = defStyle{
          stylePrefix = msg (message <> " ") <> exact,
          stylePostfix = percentage <> msg "% ETA: "
                         <> remainingTime renderDuration "00"
                         <> msg " DUR: " <> elapsedTime renderDuration,
          styleDone = '#',
          styleCurrent = '#',
          styleTodo = '-' }

    incPB pb = incProgress pb 1

-- | Rewrite the symbol string with a new rule [s01/(s0,s1)] and return
-- a delta of the counts of candidates in the string after the
-- application of the rule relative to before.
rewrite :: Monad m => (Int, Int) -> Int -> [Int] ->
           Stream (Of Int) m (Map (Int, Int) Int)
rewrite (s0,s1) s01 str = case str of
  [] -> return M.empty
  [s] -> S.yield s >> return M.empty
  s:s':ss | s == s0 && s' == s1 -> do
              S.yield s01
              go s01 ss (M.singleton (s0,s1) (-1))

          | otherwise -> do
              S.yield s
              go s (s':ss) M.empty
  where
    inc s0s1 = M.insertWith (+) s0s1 1
    dec s0s1 = M.insertWith (+) s0s1 (-1)

    -- FIXME: over-decs by 1 on pattern [s,s,s,s]
    go _ []  !m = return m
    go _ [s] !m = S.yield s >> return m
    go prev (s:s':ss) !m
      | s == s0 && s' == s1 = do
          S.yield s01 -- construct
          let m' = dec (prev,s0) $ dec (s0,s1) $ inc (prev,s01) m
          go s01 ss $ case subst ss of
            [] -> m'
            (s'':_)
              | s'' == s01 -> dec (s1,s0) m' -- (s01,s01) not ours
              | otherwise -> dec (s1,s'') $
                             inc (s01,s'') m'

      | otherwise = S.yield s >> go s (s':ss) m

    -- go, without the count deltas
    subst [] = []
    subst [s] = [s]
    subst (s:s':ss) | s == s0 && s' == s1 = s01:subst ss
                    | otherwise = s:subst (s':ss)

countJoints :: [Int] -> Map (Int,Int) Int
countJoints = fst . runIdentity . countJointsM . S.each

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
