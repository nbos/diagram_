module Diagram where

import qualified Data.List as L
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

listCandidates :: [Int] -> Map (Int,Int) Int
listCandidates [] = M.empty
listCandidates (s0:ss) = L.foldl' (flip f) M.empty $ zip (s0:ss) ss
  where f k = M.insertWith (+) k 1
