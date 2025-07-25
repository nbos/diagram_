{-# LANGUAGE BangPatterns #-}
module Diagram where

import System.Environment (getArgs)
import System.Exit

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import qualified Data.ByteString as BS

import Streaming
import qualified Streaming.Prelude as S

import Diagram.Model

main :: IO ()
main = do
  args <- getArgs
  case args of
    [filename] -> do
      bytestring <- BS.readFile filename
      let as = BS.unpack bytestring
          mdl = fromAtoms as
          ss = fromEnum <$> as
          m = listCandidates ss
          (mdl',ss') = go mdl m ss
      exitSuccess

    _else -> do
      putStrLn "Usage: program <filename>"
      exitFailure
  where
    go mdl ss m = undefined

-- | Rewrite the symbol string with a new rule [s01/(s0,s1)] and return
-- a delta of the counts of candidates in the string after the
-- application of the rule relative to before.
rewrite :: (Int,Int) -> Int -> [Int] -> ([Int], Map (Int,Int) Int)
rewrite (s0,s1) s01 str = S.lazily $ runIdentity $ S.toList $ case str of
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

listCandidates :: [Int] -> Map (Int,Int) Int
listCandidates = go M.empty
  where
    inc s0s1 = M.insertWith (+) s0s1 1
    go !m [] = m
    go !m [_] = m
    go !m [s0,s1] = inc (s0,s1) m
    go !m (s0:s1:s2:ss) =
      go (inc (s0,s1) m) $ if s0 == s1 && s1 == s2
                           then s2:ss
                           else s1:s2:ss
