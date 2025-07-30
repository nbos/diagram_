{-# LANGUAGE LambdaCase, TupleSections #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
module Diagram (module Diagram) where

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
      (ss', (am,rm)) <- fmap S.lazily $ S.toList $
                       S.mapM (\s -> incPB pb2 >> return s) $
                       rewriteM (s0,s1) s01 ss

      let m' = M.unionWith (+) am $
               M.differenceWith (nothingIf (== 0) .: (-)) m rm

    -- TODO : remove DEBUG --

          deltam = M.filter (uncurry (/=)) $
                   mergeMaps  m' $ countJoints ss'
      if not $ M.null deltam
        then error $ "counts discrepancy: " ++ show deltam
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

rewrite :: (Int, Int) -> Int -> [Int] -> ([Int], ( Map (Int, Int) Int
                                                 , Map (Int, Int) Int ))
rewrite = S.lazily . runIdentity . S.toList .:. rewriteM

-- | Rewrite the symbol string with a new rule [s01/(s0,s1)] and return
-- a delta of the counts of candidates in the string after the
-- application of the rule relative to before.
rewriteM :: Monad m => (Int, Int) -> Int -> [Int] ->
            Stream (Of Int) m ( Map (Int, Int) Int
                              , Map (Int, Int) Int )
rewriteM (s0,s1) s01 str = case str of
  [] -> return (M.empty, M.empty)
  [s] -> S.yield s >> return (M.empty, M.empty)
  s:s':ss | s == s0 && s' == s1 -> do
              S.yield s01
              go s01 ss M.empty $ M.singleton (s0,s1) (-1)

          | otherwise -> do
              S.yield s
              go s (s':ss) M.empty M.empty
  where
    inc s0s1 = M.insertWith (+) s0s1 1

    go _ [] !am !rm = return (am, rm)
    go _ [s] !am !rm = S.yield s >> return (am, rm)
    go prev (s:s':ss) !am !rm
      | s == s0 && s' == s1 = S.yield s01 >>
                              go s01 ss am'' rm''
      | otherwise = S.yield s >>
                    go s (s':ss) am rm
      where
        (am',rm') | prev == s01 = ( inc (s01,s01) am
                                  , inc (s0,s1) rm )
                  | otherwise = ( inc (prev,s01) am
                                , inc (prev,s0) $
                                  inc (s0,s1) rm )

        (am'', rm'')
          | (next:_) <- subst ss =
              ( if next == s01 then am' else inc (s01,next) am'
              , if s0 == s1 && s1 == next then rm' else inc (s1,next) rm' )
          -- if next == s01 then [s01,s01] will be inc'd when self is prev
          | otherwise = (am', rm')

    -- go without counting
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
