{-# LANGUAGE LambdaCase, ScopedTypeVariables, TypeApplications #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
module Diagram (module Diagram) where

import System.IO (openFile, IOMode(..), hFileSize, hPutStrLn, hFlush, hClose)
import System.Directory (createDirectoryIfMissing)
import System.FilePath (takeBaseName)
import System.Environment (getArgs)
import System.Exit

import Control.Monad
import Control.Monad.Primitive

import Text.Printf
import Data.Time (getCurrentTime, formatTime, defaultTimeLocale)
import Data.Maybe
import qualified Data.List as L
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import qualified Data.IntMap.Strict as IM
import qualified Data.ByteString as BS
import Data.Trie (Trie)
import qualified Data.Trie as Trie

import qualified Data.Vector.Generic as V
import qualified Data.Vector.Unboxed as U
import qualified Data.Vector.Generic.Mutable as MV
import qualified Data.Vector.Strict as B

import Streaming hiding (first,second)
import qualified Streaming as S
import qualified Streaming.Prelude as S
import qualified Streaming.ByteString as Q

import Diagram.Model (Model(Model))
import qualified Diagram.Model as Mdl
import qualified Diagram.Rules as R
import Diagram.Progress
import Diagram.Util hiding (ratio)
import Diagram.Information

data TrainState m = TrainState {
  trainModel :: !Model, -- model fitted on trainBuffer
  fwdRules :: !(Map (Int,Int) Int), -- (s0,s1) -> s01
  extensionTrie :: !(Trie ()), -- extensions of all symbols
  trainBuffer :: ![Int], -- constructed data
  symbolSource :: !(Stream (Of Int) m ()), -- source for appending data
  symbolCandidates :: !(Map (Int,Int) Int), -- (s0,s1) -> n01
  bufExtLength :: !Int,
  symbolLengths :: !(U.Vector Int) -- atomic length of symbol's extensions
}

main :: IO ()
main = do
  (maxBufLen, filename) <- (getArgs >>=) $ \case
    [filename] -> return (maxBound, filename)
    [maxBufLenStr, filename] -> return (read maxBufLenStr, filename)
    _else -> putStrLn "Usage: diagram [SIZE] FILENAME" >>
             exitFailure

  srcHandle <- openFile filename ReadMode
  srcLen <- hFileSize srcHandle -- number of atoms in the source
  let origCodeLen = srcLen * 8 -- in bits
      origInfo = fromIntegral origCodeLen :: Double

  createDirectoryIfMissing True "data"
  currentTime <- getCurrentTime
  let timestamp = formatTime defaultTimeLocale "%Y%m%d-%H%M%S" currentTime
      logFilePath = "data/" ++ takeBaseName filename
                    ++ "-run-" ++ timestamp ++ ".csv"
  csvHandle <- openFile logFilePath WriteMode

  -- <main loop>
  let go (TrainState mdl@(Model rs n ks) rsm trie buf src cdts bel sls) = do
        let here = (++) (" [" ++ show (R.numSymbols rs) ++ "]: ")
            scale = fromIntegral srcLen / fromIntegral bel

            -- <Mdl.scaledInformation>
            sn     = scale * fromIntegral n
            rsInfo = ceiling @_ @Int $ R.information rs
            nInfo  = ceiling @_ @Int $ eliasInfo (round sn)
            ksInfo = ceiling @_ @Int $ Mdl.fDistrInfo sn (fromIntegral $ V.length ks)
            ssInfo = ceiling @_ @Int $ Mdl.scaledStringInfo scale mdl
            approxTotalInfo = rsInfo + nInfo + ksInfo + ssInfo
            -- </Mdl.scaledInformation>

            approxRatio = fromIntegral approxTotalInfo / origInfo
            approxFactor = recip approxRatio

        putStrLn $ here $ "Length (bits): " ++
          printf "%s (%s + %s + %s + %s), %.2f%% of orig., factor: %.4f"
          (commaize approxTotalInfo)
          (commaize rsInfo)
          (commaize nInfo)
          (commaize ksInfo)
          (commaize ssInfo)
          (approxRatio * 100)
          approxFactor

        cdtList <- pbSeq (M.size cdts) (here "Computing losses") $
                   (<$> M.toList cdts) $ \(s0s1,n01) ->
          let loss = Mdl.scaledInfoDelta scale mdl s0s1 n01
          in loss `seq` (loss, s0s1, n01)

        putStrLn $ here "Sorting candidates..."
        (loss,(s0,s1),n01) <- case L.sort cdtList of
          [] -> error "no candidates"
          (c@(loss,(s0,s1),_):cdts') -> do
            when (loss < 0) $ putStrLn $ here $
                              "Intro: " ++ showJoint rs s0 s1
            putStrLn $ here "Top candidates:"
            forM_ (c:take 4 cdts') (putStrLn . showCdt rs)
            return c

        hPutStrLn csvHandle $
          printf "%d, %d, %d, %d, %d, %d, %d, %d, %d, %.2f, \"%s\", \"%s\", \"%s\""
          (R.numSymbols rs) -- %d
          approxTotalInfo rsInfo nInfo ksInfo ssInfo -- %d, %d, %d, %d, %d
          s0 s1 n01 loss -- %d, %d, %d, %f
          (R.toEscapedString rs [s0])
          (R.toEscapedString rs [s1])
          (R.toEscapedString rs [s0,s1])
        hFlush csvHandle

        when (loss > 0) ( putStrLn (here "Reached minimum. Terminating.")
                          >> hClose csvHandle
                          >> exitSuccess )

        let (s01, mdl'@(Model rs' n' _)) = Mdl.pushRule mdl (s0,s1) n01
            rsm' = M.insert (s0,s1) s01 rsm
            bs01 = BS.pack $ R.extension rs' s01
            trie' = Trie.insert bs01 () trie

        buf' <- pbSeq n' (here "Rewriting string") $
                subst1 (s0,s1) s01 buf

        (am,rm,sn') <- recountM (s0,s1) s01 $ -- count maps (am,rm)
                       withPB n' (here "Updating counts") $
                       fmap (fromMaybe (error "empty buf") -- Maybe a -> a
                              . S.fst') $ -- drop ()
                       S.last $ S.copy $ -- last symbol :: Maybe a
                       S.each buf'

        -- extend the buffer
        ss :> src' <- S.toList $
                      R.splitAtSubst rs' rsm' trie' (n - n') src

        -- refine state with new symbols
        let mdl'' = Mdl.addCounts mdl' ss
            buf'' | null ss = buf'
                  | otherwise = buf' ++ ss
            cdts' = (countJoints_ cdts sn' ss `sub` rm) `add` am
            bel' = bel + sum ((sls' V.!) <$> ss)
            sls' = V.snoc sls (sls V.! s0 + sls V.! s1)

        putStrLn ""
        go $ TrainState mdl'' rsm' trie' buf'' src' cdts' bel' sls'
  -- </main loop>

      src0 = S.map fromEnum $ Q.unpack $ Q.fromHandle srcHandle

  buf0 :> n0 :> src0' <- S.toList $ S.length $ S.copy $
                         S.splitAt maxBufLen src0
  let mdl0 = Mdl.addCounts Mdl.empty buf0
  (cdts0,()) <- countJointsM $
                withPB n0 "Initializing joint counts" $
                S.each buf0
  let bel0 = n0
      sls0 = V.replicate 256 1

  -- go
  go $ TrainState mdl0 M.empty Trie.empty buf0 src0' cdts0 bel0 sls0

  where
    -- | O(log(n)) equiv. of M.filter (> 0) .: M.unionWith (+)
    add :: Map (Int,Int) Int -> Map (Int,Int) Int -> Map (Int,Int) Int
    add = M.mergeWithKey (const $ nothingIf (== 0) .: (+)) id id

    -- | O(log(n) equiv. of M.filter (> 0) .: M.unionWith (-)
    sub :: Map (Int,Int) Int -> Map (Int,Int) Int -> Map (Int,Int) Int
    sub = M.differenceWith (nothingIf (== 0) .: (-))

    showCdt rs (loss,(s0,s1),n01) = "   "
      ++ show loss ++ ": "
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

-- | Substitute a single pair of symbols for a constructed joint symbol
-- in a string of symbols
subst1 :: (Int,Int) -> Int -> [Int] -> [Int]
subst1 (s0,s1) s01 = go
  where
    go [] = []
    go [s] = [s]
    go (s:s':ss) | s == s0 && s' == s1 = s01:go ss
                 | otherwise = s:go (s':ss)

-- | Monadic single construction rule substitution using Streams
subst1M :: forall m r. Monad m => (Int, Int) -> Int ->
          Stream (Of Int) m r -> Stream (Of Int) m r
subst1M (s0,s1) s01 = go
  where
    go :: Stream (Of Int) m r -> Stream (Of Int) m r
    go ss = (lift (S.next ss) >>=) $ \case
      Left r -> return r
      Right (s,ss') -> goCons s ss'

    goCons s ss
      | s == s0 = (lift (S.next ss) >>=) $ \case
          Left r -> S.yield s >> return r
          Right (s',ss')
            | s' == s1 -> S.yield s01 >> go ss'
            | otherwise -> S.yield s0 >> goCons s' ss'
      | otherwise = S.yield s >> go ss

-- | Single construction rule substitution on a Vector representation
substV :: PrimMonad m => (Int, Int) -> Int -> U.MVector (PrimState m) Int ->
          m Int
substV (s0,s1) s01 mv = go 0 0
  where
    len = MV.length mv
    go readIdx writeIdx
      | readIdx < len - 1 = do
          s <- MV.read mv readIdx
          s' <- MV.read mv (readIdx + 1)
          if s == s0 && s' == s1
            then MV.write mv writeIdx s01 >>
                 go (readIdx + 2) (writeIdx + 1)
            else MV.write mv writeIdx s >>
                 go (readIdx + 1) (writeIdx + 1)
      | readIdx == len - 1 =
          MV.read mv readIdx
          >>= MV.write mv writeIdx
          >> return (writeIdx + 1)
      | otherwise = return writeIdx

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
countJoints [] = M.empty
countJoints (s0:ss) = countJoints_ M.empty s0 ss

-- | Count the joints in a list given the map of counts and the previous
-- symbol
countJoints_ :: Map (Int,Int) Int -> Int -> [Int] -> Map (Int,Int) Int
countJoints_ !m _ [] = m
countJoints_ !m s0 [s1] = M.insertWith (+) (s0,s1) 1 m
countJoints_ !m s0 (s1:s2:ss)
  | s0 == s1 && s1 == s2 = countJoints_ m' s2 ss
  | otherwise = countJoints_ m' s1 (s2:ss)
  where m' = M.insertWith (+) (s0,s1) 1 m

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

-- | Counts the joints concerning one symbol
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

-- | Turn an MVector into a Stream
toStream :: (PrimMonad m, MV.MVector v b) =>
            v (PrimState m) b -> Stream (Of b) m ()
toStream mv = S.mapM (MV.read mv) $
              S.each [0.. MV.length mv - 1]

-- | Write the elements of a Stream to an MVector
writeStream :: (PrimMonad m, MV.MVector v b) =>
               v (PrimState m) b -> Stream (Of b) m r -> m r
writeStream mv = S.mapM_ (uncurry $ MV.write mv)
                 . S.zip (S.enumFrom 0)

commaize :: (Integral a, Show a) => a -> String
commaize n =
  let s = show (abs n)
      chunks = reverse . group3 . reverse $ s
      body = L.intercalate "," chunks
  in (if n < 0 then "-" else "") ++ body
  where
    group3 :: [a] -> [[a]]
    group3 [] = []
    group3 xs = let (h,t) = splitAt 3 xs in h : group3 t
