module Diagram.Head (module Diagram.Head) where

import Data.Tuple.Extra (dupe)

-- | Isomorphic to a list of successive predictions where each
-- subsequent prediction is predicated on the last:
-- (((((x,x),x),x),x),x), etc.
type Head = (Int,Int)

fromAtoms :: [Int] -> [Head]
fromAtoms = fmap dupe

-- | Return @True@ iff the constructive interval begins and ends on the
-- same symbol
isSingleton :: Head -> Bool
isSingleton = uncurry (==)

-- | Project into the symbol if there is only one
getSingle :: Head -> Maybe Int
getSingle (pMin,pMax) | pMin == pMax = Just pMin
                      | otherwise = Nothing
