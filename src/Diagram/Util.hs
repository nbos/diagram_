{-# LANGUAGE PatternGuards, BangPatterns, TupleSections, ScopedTypeVariables #-}
module Diagram.Util where

import Control.Monad.State.Strict
import Control.Exception
import System.IO.Unsafe

import Data.Maybe
import qualified Data.Bits as B
import qualified Data.List.Extra as L

import qualified Data.Vector as V
import Data.Hashable (Hashable)
import qualified Data.HashSet as HS
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM

--------------
-- Wrappers --
--------------

newtype Squash a = Squash { unSquash :: a }
    deriving (Show,Read)

instance Eq (Squash a) where
    _ == _ = True

instance Ord (Squash a) where
    compare _ _ = EQ

----------
-- Misc --
----------

-- | https://stackoverflow.com/questions/62680939/
-- abusing-unsafeperformio-to-catch-partial-functions
catchE :: Exception e => a -> Either e a
catchE = unsafePerformIO . try . evaluate

assertId :: (a -> Bool) -> a -> a
assertId f a = assert (f a) a

(+-) :: Num a => a -> a -> (a,a)
(+-) n i = (n-i,n+i)
{-# INLINE (+-) #-}

inf :: RealFloat a => a
inf = 1/0
{-# INLINE inf #-}

-- | Expects third agument to be in the range [0-1]
lerp :: Fractional a => a -> a -> a -> a
lerp a b r = r*a + r'*b
  where r' = 1 - r

-- | Computes a\/(a+b) with division-by-zero mitigation. Expects input
-- to be positive
ratio :: RealFrac a => a -> a -> a
ratio a b = min 1 $ max 0 $ a/(a+b)

justIf :: (a -> Bool) -> a -> Maybe a
justIf p a = if p a then Just a else Nothing
{-# INLINE justIf #-}

nothingIf :: (a -> Bool) -> a -> Maybe a
nothingIf p a = if p a then Nothing else Just a
{-# INLINE nothingIf #-}

-- | Rust-brained Maybe unwrapper
expect :: String -> Maybe a -> a
expect = fromMaybe . error

leftIf :: (a -> Bool) -> a -> Either a a
leftIf p a = if p a then Left a else Right a
{-# INLINE leftIf #-}

-- Reverse an ordering
rev :: Ordering -> Ordering
rev LT = GT
rev GT = LT
rev eq = eq
{-# INLINE rev #-}

eqOn :: Eq e => (a -> e) -> a -> a -> Bool
eqOn f a b = f a == f b
{-# INLINE eqOn #-}

compareOn :: Ord o => (a -> o) -> a -> a -> Ordering
compareOn f a b = f a `compare` f b
{-# INLINE compareOn #-}

boolXor :: Bool -> Bool -> Bool
boolXor = (/=)
{-# INLINE boolXor #-}

-- List from `lo` (inclusive) to `hi` (exclusive) by increments
range :: (Ord a,Num a) => a -> a -> a -> [a]
range lo up step =
  lo:L.unfoldr (fmap dupe . nothingIf (>= up) . (+ step)) lo
{-# INLINE range #-}

-- | Memoize a monadic function
memoM :: (Monad m, Hashable k, Eq k) => (a -> k) -> (a -> m b) ->
         a -> StateT (HashMap k b) m b
memoM keyOf f a = do
  let k = keyOf a
  m <- get
  case HM.lookup k m of
    Just b -> return b
    Nothing -> do
      b <- lift $ f a
      put $ HM.insert k b m
      return b

-- | Prefix-sum (a.k.a. scan) with the given operator, but in a
-- balanced fashion (i.e. the operator isn't associative and works
-- better if elements of similar depths are joined together)
balancedScan :: forall m a. Monad m => (a -> a -> m a) -> [a] -> m [a]
balancedScan op l = flip evalStateT hm0 $
                    mapM go ((0,) <$> [1..len])
  where
    as = V.fromList l
    len = V.length as
    hm0 = HM.fromList $ zip (zip [0..] [1..]) l -- up - lo == 1

    go :: (Int,Int) -> StateT (HashMap (Int,Int) a) m a
    go (lo,up) = do
      ma <- gets $ HM.lookup (lo,up)
      case ma of
        Just a  -> return a
        Nothing -> do -- up - lo > 1
          let n = up - lo
              n1 = n `div` 2
              n0 = n - n1 -- (== n1) or (== n1 + 1)
          a0 <- go (lo,lo+n0)
          a1 <- go (lo+n0,up)
          a <- lift $ a0 `op` a1
          modify $ HM.insert (lo,up) a
          return a

-- | Heat map color function, maps [0-1] interval to a 7-color RGB
-- byte triples spectrum (black,blue,cyan,green,yellow,red,white)
heat :: Float -> (Int,Int,Int)
heat frac = v V.! n $ floor $ r * 255
  where
    (n,r) = properFraction $ 4 * frac
    v = V.fromList
        [ (0  , 0  ,    )              -- black to blue
        , uncurry (0,,) . toSnd (255-) -- blue to green
        , uncurry (,,0) . toSnd (255-) -- green to red
        , uncurry (255,,) . dupe       -- red to white
        , const (255,255,255) ]        -- white

----------
-- Bits --
----------

-- | Return a list of the indices of the set bits in the Int, counting
-- from the right
unpackComb :: Int -> [Int]
unpackComb 0 = []
unpackComb n = let i = B.countTrailingZeros n
               in i : unpackComb (n `B.xor` B.bit i)

-- | [1, 2, 4, 8, 16, 32, 64, 128, ...]
powers :: [Int]
powers = fmap (B.shift 1) [0..B.finiteBitSize (1 :: Int) - 1]
{-# INLINE powers #-}

isPow2 :: Int -> Bool
isPow2 = (== 1) . B.popCount
{-# INLINE isPow2 #-}

-- | Floor of the logBase 2 of an Int
intLog2 :: Int -> Int
intLog2 = (63 -) . B.countLeadingZeros

-- | Produces a mask 00..000111..11 with the given number of 1 bits
bits :: (Num a, B.Bits a) => Int -> a
bits = (+(-1)) . B.bit

--------------
-- Functors --
--------------

funzip :: Functor f => f (a, b) -> (f a, f b)
funzip xs = (fmap fst xs, fmap snd xs)
{-# INLINE funzip #-}

funzipWith :: Functor f => (a -> (b,c)) -> f a -> (f b, f c)
funzipWith = funzip .: fmap
{-# INLINE funzipWith #-}

ffmap :: (Functor f1, Functor f2) => (a -> b) -> f1 (f2 a) -> f1 (f2 b)
ffmap = fmap . fmap
{-# INLINE ffmap #-}

fffmap :: (Functor f1, Functor f2, Functor f3) =>
          (a -> b) -> f1 (f2 (f3 a)) -> f1 (f2 (f3 b))
fffmap = fmap . fmap . fmap
{-# INLINE fffmap #-}

ffffmap :: (Functor f1, Functor f2, Functor f3, Functor f4) =>
          (a -> b) -> f1 (f2 (f3 (f4 a))) -> f1 (f2 (f3 (f4 b)))
ffffmap = fmap . fmap . fmap . fmap
{-# INLINE ffffmap #-}

(<<&>>) :: (Functor f1, Functor f2) => f1 (f2 a) -> (a -> b) -> f1 (f2 b)
(<<&>>) = flip (<<$>>)
{-# INLINE (<<&>>) #-}
infixl 1 <<&>>

(<<$>>) :: (Functor f1, Functor f2) => (a -> b) -> f1 (f2 a) -> f1 (f2 b)
(<<$>>) = fmap . fmap
{-# INLINE (<<$>>) #-}
infixl 4 <<$>>

(<<<$>>>) :: (Functor f1, Functor f2, Functor f3) =>
             (a -> b) -> f1 (f2 (f3 a)) -> f1 (f2 (f3 b))
(<<<$>>>) = fmap . fmap . fmap
{-# INLINE (<<<$>>>) #-}
infixl 4 <<<$>>>

(<<<<$>>>>) :: (Functor f1, Functor f2, Functor f3, Functor f4) =>
             (a -> b) -> f1 (f2 (f3 (f4 a))) -> f1 (f2 (f3 (f4 b)))
(<<<<$>>>>) = fmap . fmap . fmap . fmap
{-# INLINE (<<<<$>>>>) #-}
infixl 4 <<<<$>>>>

(<<$) :: (Functor f1, Functor f2) => a -> f1 (f2 b) -> f1 (f2 a)
(<<$) = fmap . (<$)
{-# INLINE (<<$) #-}
infixl 4 <<$

(<<<$) :: (Functor f1, Functor f2, Functor f3) =>
          a -> f1 (f2 (f3 b)) -> f1 (f2 (f3 a))
(<<<$) = fmap . fmap . (<$)
{-# INLINE (<<<$) #-}
infixl 4 <<<$

(>.>) :: (a -> b) -> (b -> c) -> a -> c
(>.>) f g = g . f
{-# INLINE (>.>) #-}
infixr 1 >.>

-----------
-- Lists --
-----------

uncons :: [a] -> (a,[a])
uncons (hd:tl) = (hd,tl)
uncons [] = error "Util.uncons: empty list"

-- | Doesn't go further than it needs to for comparing length
compareLength :: Int -> [a] -> Ordering
compareLength len | len < 0   = const LT
                  | otherwise = go len
  where go 0 [] = EQ
        go _ [] = GT
        go 0 (_:_) = LT
        go n (_:tl) = go (n-1) tl

lengthEQ :: Int -> [a] -> Bool
lengthEQ = (EQ ==) .: compareLength
{-# INLINE lengthEQ #-}

lengthLT :: Int -> [a] -> Bool
lengthLT = (LT ==) .: compareLength
{-# INLINE lengthLT #-}

lengthGT :: Int -> [a] -> Bool
lengthGT = (GT ==) .: compareLength
{-# INLINE lengthGT #-}

-- Zip lists, throwing an error if lengths don't match
zipExact :: [a] -> [b] -> [(a, b)]
zipExact = zipExactWith (,)

zipExactWith :: (a -> b -> c) -> [a] -> [b] -> [c]
zipExactWith f = go
  where go (a:as) (b:bs) = f a b : go as bs
        go [] [] = []
        go _ _ = error "Util.zipExactWith: mismatched list lengths"

-- Zip lists, throwing an error if lengths don't match
zipExact3 :: [a] -> [b] -> [c] -> [(a, b, c)]
zipExact3 = zipExactWith3 (,,)

zipExactWith3 :: (a -> b -> c -> d) -> [a] -> [b] -> [c] -> [d]
zipExactWith3 f = go
  where go (a:as) (b:bs) (c:cs) = f a b c : go as bs cs
        go [] [] [] = []
        go a b c = error $ "Util.zipExactWith3: mismatched list lengts: "
                   ++ show (length a, length b, length c)

unzipWith :: (a -> (b,c)) -> [a] -> ([b],[c])
unzipWith = funzipWith
{-# INLINE unzipWith #-}

-- Like zip, but one after the other rather than side by side
interleave :: [a] -> [a] -> [a]
interleave (a:restA) (b:restB) = a:b:interleave restA restB
interleave [] bs = bs
interleave as [] = as

-- The following merge functions are sourced from
-- https://hackage.haskell.org/package/base-4.16.0.0/docs/src/Data.OldList.html#sortBy
mergeAll :: Ord a => [[a]] -> [a]
mergeAll [x] = x
mergeAll xs = mergeAll (mergePairs xs)

mergeAllBy :: (a -> a -> Ordering) -> [[a]] -> [a]
mergeAllBy cmp = go
  where go [x] = x
        go xs = go (mergePairsBy cmp xs)

mergePairs :: Ord a => [[a]] -> [[a]]
mergePairs (a:b:xs) = let !x = L.merge a b
                      in x : mergePairs xs
mergePairs xs = xs

mergePairsBy :: (a -> a -> Ordering) -> [[a]] -> [[a]]
mergePairsBy cmp = go
  where go (a:b:xs) = let !x = L.mergeBy cmp a b
                      in x : go xs
        go xs = xs

liftOrdList :: (a -> a -> Ordering) -> [a] -> [a] -> Ordering
liftOrdList comp = go
  where go (x:xs) (y:ys) = case comp x y of EQ -> go xs ys
                                            o -> o
        go []     []     = EQ
        go []     (_:_)  = LT
        go (_:_)  []     = GT

safeTail :: [a] -> [a]
safeTail (_:xs) = xs
safeTail [] = []

safeInit :: [a] -> [a]
safeInit [] = []
safeInit (x:xs) = init' x xs
  where init' _ []     = []
        init' y (z:zs) = y : init' z zs

-- | Does nothing if null
mapHead :: (a -> a) -> [a] -> [a]
mapHead f (hd:tl) = f hd : tl
mapHead _ [] = []
{-# INLINE mapHead #-}

-- | Does nothing if null
mapLast :: (a -> a) -> [a] -> [a]
mapLast f l = reverse $ mapHead f (reverse l)
{-# INLINE mapLast #-}

-- | Does nothing if null
mapTail :: (a -> a) -> [a] -> [a]
mapTail f (hd:tl) = hd : fmap f tl
mapTail _ [] = []
{-# INLINE mapTail #-}

-- | Like `inits` but with sub-lists reversed
-- Linear rather than quadratic space complexity
revInits :: [a] -> [[a]]
revInits = scanl (flip (:)) []
{-# INLINE revInits #-}

-- | Reverse the first list and append the second to it
revAppend :: [a] -> [a] -> [a]
revAppend l r = L.foldl' (flip (:)) r l
-- Below would be slightly faster judging from tests with
-- GHC.Lists.reverse, but LSP complains
-- revAppend [] l = l
-- revAppend (x:xs) l = revAppend xs (x:l)
{-# INLINE revAppend #-}

-- | splitAt, but construct the first list in reverse
revSplitAt :: Int -> [a] -> ([a], [a])
revSplitAt n ls
  | n <= 0 = ([], ls)
  | otherwise = go n [] ls
    where
        go :: Int -> [a] -> [a] -> ([a], [a])
        go _ acc []     = (acc, [])
        go 1 acc (x:xs) = (x:acc, xs)
        go m acc (x:xs) = go (m - 1) (x:acc) xs

-- | Only keep the first instance, returns in original order
-- About as fast as `sortNubOn`
hashNubOn :: (Hashable b, Eq b) => (a -> b) -> [a] -> [a]
hashNubOn f = go HS.empty
  where go _ [] = []
        go s (a:as) | HS.member b s = go s as
                    | otherwise = a : go (HS.insert b s) as
          where b = f a

-- | Return all the ways to choose exactly one element per list of the
-- input. If one of the input list is [], returns []. The length of
-- the output list is the product of the lengths of the input lists.
cartesianProduct :: [[a]] -> [[a]]
cartesianProduct = foldr (\xs ls -> [ x:l | l <- ls, x <- xs]) [[]]
{-# INLINE cartesianProduct #-}

sorted :: Ord a => [a] -> Bool
sorted [] = True
sorted xs = and $ zipWith (<=) xs (tail xs)
{-# INLINE sorted #-}

segment :: [Int] -> [a] -> [[a]]
segment [] _ = []
segment (n:rest) l =
  let (hd,tl) = splitAt n l
  in hd : segment rest tl

-- | Ways to choose two elements from a set (no duplicates)
choose2 :: [a] -> [(a,a)]
choose2 [] = []
choose2 (a:rest) = fmap (a,) rest ++ choose2 rest

-- | Cartesian square of a set (w/ duplicates, i.e. diagonal)
cartesian :: [a] -> [(a,a)]
cartesian [] = []
cartesian (a:rest) = (a,a) : fmap (a,) rest ++ cartesian rest

-- | Pad internal lists with a given element such that the resulting
-- list contains lists of same length
padLists :: a -> [[a]] -> [[a]]
padLists = padToAtLeast 0

-- | Pad inner lists to a given size, or larger if one of the lists
-- already exceeds that length
padToAtLeast :: Int -> a -> [[a]] -> [[a]]
padToAtLeast n z l = zipWith ((++) . flip replicate z) pad_lengths l
  where lengths = fmap length l
        maxLen = maximum lengths
        pad_lengths = fmap (max n maxLen-) lengths

-- | From strictly increasing prototype and list of (a,[a]), add empty
-- list for every missing 'a starting at 0
fillGaps :: (Show a, Ord a) => [a] -> [(a, [a])] -> [[a]]
fillGaps is [] = [] <$ is
fillGaps (i:rest) ixss@((j,ixs):rest') =
  case compare i j of
        LT -> [] : fillGaps rest ixss -- gap
        EQ -> ixs : fillGaps rest rest' -- no gap
        GT -> error "Util.fillGaps: unprototyped element"
fillGaps is js = error $ "Util.fillGaps: more elements than prototypes:\n"
                       ++ show is ++ "\n" ++ show js

factorPrefix :: Eq a => [[a]] -> ([a],[[a]])
factorPrefix [] = ([],[])
factorPrefix l
  | any L.null l = ([],l)
  | L.allSame (head <$> l) = mapFst (head (head l) :) $
                             factorPrefix $ fmap tail l
  | otherwise = ([],l)

-- | Given a list of `n` elements, return `n` lists of `n-1` elements,
-- each missing a different element of the original list
except1 :: [a] -> [[a]]
except1 [] = []
except1 (a:as) = as : fmap (a:) (except1 as)
{-# INLINE except1 #-}

normalize :: [Double] -> [Double]
--normalize [_] = [1]
normalize xs | denom == 0 = 0 <$ xs
             | otherwise = (/denom) <$> xs
  where denom = sum xs
{-# INLINE normalize #-}

-- -- | Normalize a list of numbers in log-space, such that the sum of
-- -- exp's equals to 1 (or equivalently the logSumExp equals 0)
-- logNormalize :: [Double] -> [Double]
-- --logNormalize [_] = [0]
-- logNormalize xs | denom == -inf = -inf <$ xs
--                 | otherwise = (+(-denom)) <$> xs
--   where denom = logSumExp xs
-- {-# INLINE logNormalize #-}

-- | Replace every instance of a given element with a sequence of
-- elements in a list
replace :: Eq a => a -> [a] -> [a] -> [a]
replace a as = go
  where go [] = []
        go (hd:tl) | a == hd = as ++ go tl
                   | otherwise = a:go tl
{-# INLINE replace #-}

distinctAscListUnion :: Ord a => [a] -> [a] -> [a]
distinctAscListUnion [] c = c
distinctAscListUnion c [] = c
distinctAscListUnion (i0:rest0) (i1:rest1)
  | i0 < i1   = i0 : distinctAscListUnion rest0 (i1:rest1)
  | i0 > i1   = i1 : distinctAscListUnion (i0:rest0) rest1
  | otherwise = i0 : distinctAscListUnion rest0 rest1
{-# SPECIALIZE distinctAscListUnion :: [Int] -> [Int] -> [Int] #-}

catPairs :: [(a,a)] -> [a]
catPairs [] = []
catPairs ((x,y):xys) = x:y:catPairs xys
{-# INLINE catPairs #-}

countdown :: Int -> [Int]
countdown n = [n,n-1..0]

---------------
-- Functions --
---------------

-- | Apply f $ f $ ... $ f $ x , `n` times, collecting the
-- results. Output length is `n` so e.g. `nest f 0 a` returns `[]`,
-- `nest f 1 a` returns `[f a]`, etc.
nest :: (a -> a) -> Int -> a -> [a]
nest f n = take n . tail . L.iterate f
{-# INLINE nest #-}

-- | Compose f a >>= f >>= ... >>= f, `n` times, collecting the
-- results. Output length is `n` so e.g. `nest f 0 a` is `return []`.
nestM :: Monad m => (a -> m a) -> Int -> a -> m [a]
nestM f = go []
  where go acc n a = case compare n 0 of
          LT -> error "Util.nestM: negative argument"
          EQ -> return $ reverse acc
          GT -> do a' <- f a
                   go (a':acc) (n-1) a'

curry3 :: ((a, b, c) -> d) -> a -> b -> c -> d
curry3 = (.:. (,,))
{-# INLINE curry3 #-}

curry' :: (a -> (b,c) -> d) -> a -> b -> c -> d
curry' = (.) (.: (,))
{-# INLINE curry' #-}

uncurry' :: (a -> b -> c -> d) -> a -> (b,c) -> d
uncurry' = uncurry .: ($)
{-# INLINE uncurry' #-}

-- Compose w/ two arguments
(.:) :: (b -> c) -> (a1 -> a2 -> b) -> a1 -> a2 -> c
(.:) = (.).(.)
infixr 8 .:
{-# INLINE (.:) #-}

-- three
(.:.) :: (b -> c) -> (a1 -> a2 -> a3 -> b) -> a1 -> a2 -> a3 -> c
(.:.) = (.).(.:)
infixr 8 .:.
{-# INLINE (.:.) #-}

-- four
(.::) :: (b -> c) -> (a1 -> a2 -> a3 -> a4 -> b) -> a1 -> a2 -> a3 -> a4 -> c
(.::) = (.).(.:.)
infixr 8 .::
{-# INLINE (.::) #-}

-- five
(.::.) :: (b -> c) -> (a1 -> a2 -> a3 -> a4 -> a5 -> b) -> a1 -> a2 -> a3 -> a4 -> a5 -> c
(.::.) = (.).(.::)
infixr 8 .::.
{-# INLINE (.::.) #-}

-- Flip w/ two arguments
flip2 :: (a -> b1 -> b2 -> c) -> b1 -> b2 -> a -> c
flip2 = flip .: flip
{-# INLINE flip2 #-}

-- three
flip3 :: (a -> b1 -> b2 -> b3 -> c) -> b1 -> b2 -> b3 -> a -> c
flip3 = flip .:. flip2
{-# INLINE flip3 #-}

-- four
flip4 :: (a -> b1 -> b2 -> b3 -> b4 -> c) -> b1 -> b2 -> b3 -> b4 -> a -> c
flip4 = flip2 .:. flip2
{-# INLINE flip4 #-}

-- five
flip5 :: (a -> b1 -> b2 -> b3 -> b4 -> b5 -> c) -> b1 -> b2 -> b3 -> b4 -> b5 -> a -> c
flip5 = flip2 .:: flip3
{-# INLINE flip5 #-}

-------------
-- Tuples  --
-------------

both :: (a -> Bool) -> (a, a) -> Bool
both = uncurry (&&) .: mapBoth
{-# INLINE both #-}

eitherIs :: (a -> Bool) -> (a, a) -> Bool
eitherIs = uncurry (||) .: mapBoth
{-# INLINE eitherIs #-}

mapFst :: (a -> c) -> (a, b) -> (c, b)
mapFst f (a, b) = (f a, b)
{-# INLINE mapFst #-}

toFst :: (a -> b) -> a -> (b, a)
toFst f a = (f a, a)
{-# INLINE toFst #-}

toFstM :: Functor m => (a -> m b) -> a -> m (b, a)
toFstM f a = (,a) <$> f a
{-# INLINE toFstM #-}

mapSnd :: (b -> c) -> (a, b) -> (a, c)
mapSnd f (a, b) = (a, f b)
{-# INLINE mapSnd #-}

toSnd :: (a -> b) -> a -> (a, b)
toSnd f a = (a, f a)
{-# INLINE toSnd #-}

mapBoth :: (a -> b) -> (a, a) -> (b, b)
mapBoth f (a, b) = (f a, f b)
{-# INLINE mapBoth #-}

dupe :: a -> (a,a)
dupe a = (a,a)
{-# INLINE dupe #-}

sortPairBy :: (a -> a -> Ordering) -> a -> a -> (a, a)
sortPairBy f a b | GT <- f a b = (b,a)
                 | otherwise   = (a,b)
{-# INLINE sortPairBy #-}

sortPairOn :: Ord b => (a -> b) -> a -> a -> (a, a)
sortPairOn f a b = if f a > f b then (b, a) else (a, b)
{-# INLINE sortPairOn #-}

sortPair :: Ord a => a -> a -> (a, a)
sortPair a0 a1 = if a0 > a1 then (a1, a0) else (a0, a1)
{-# INLINE sortPair #-}

mapFst3 :: (a -> d) -> (a, b, c) -> (d, b, c)
mapFst3 f (a, b, c) = (f a, b, c)
{-# INLINE mapFst3 #-}

mapSnd3 :: (b -> d) -> (a, b, c) -> (a, d, c)
mapSnd3 f (a, b, c) = (a, f b, c)
{-# INLINE mapSnd3 #-}

mapThd3 :: (c -> d) -> (a, b, c) -> (a, b, d)
mapThd3 f (a, b, c) = (a, b, f c)
{-# INLINE mapThd3 #-}

fst4 :: (a, b, c, d) -> a
fst4 (a, _, _, _) = a
{-# INLINE fst4 #-}

snd4 :: (a, b, c, d) -> b
snd4 (_, b, _, _) = b
{-# INLINE snd4 #-}

thd4 :: (a, b, c, d) -> c
thd4 (_, _, c, _) = c
{-# INLINE thd4 #-}

fth4 :: (a, b, c, d) -> d
fth4 (_, _, _, d) = d
{-# INLINE fth4 #-}

mapFst4 :: (a -> e) -> (a, b, c, d) -> (e, b, c, d)
mapFst4 f (a, b, c, d) = (f a, b, c, d)
{-# INLINE mapFst4 #-}

mapSnd4 :: (b -> e) -> (a, b, c, d) -> (a, e, c, d)
mapSnd4 f (a, b, c, d) = (a, f b, c, d)
{-# INLINE mapSnd4 #-}

mapThd4 :: (c -> e) -> (a, b, c, d) -> (a, b, e, d)
mapThd4 f (a, b, c, d) = (a, b, f c, d)
{-# INLINE mapThd4 #-}

------------
-- Monads --
------------

bind2 :: Monad m => (t1 -> t2 -> m b) -> m t1 -> m t2 -> m b
bind2 f ma mb = do
  a <- ma
  b <- mb
  f a b
{-# INLINE bind2 #-}

bind3 :: Monad m => (t1 -> t2 -> t3 -> m b) -> m t1 -> m t2 -> m t3 -> m b
bind3 f ma mb mc = do
  a <- ma
  b <- mb
  c <- mc
  f a b c
{-# INLINE bind3 #-}

(>==>) :: Monad m => (t1 -> t2 -> m a) -> (a -> m b) -> t1 -> t2 -> m b
f >==> g = \x y -> f x y >>= g
{-# INLINE (>==>) #-}

(<==<) :: Monad m => (a -> m b) -> (t1 -> t2 -> m a) -> t1 -> t2 -> m b
g <==< f = \x y -> f x y >>= g
{-# INLINE (<==<) #-}

returning :: Monad m => (a -> m b) -> a -> m a
returning f a = f a >> return a
