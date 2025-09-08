{-# LANGUAGE LambdaCase, ScopedTypeVariables, TypeApplications #-}
{-# LANGUAGE BangPatterns, TupleSections #-}
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
import qualified Data.List as L
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import qualified Data.IntMap.Strict as IM

import qualified Data.Vector.Unboxed as U
import qualified Data.Vector.Generic.Mutable as MV
import qualified Data.Vector.Strict as B

import Streaming hiding (first,second)
import qualified Streaming as S
import qualified Streaming.Prelude as S
import qualified Streaming.ByteString as Q

import Diagram.Information
import Diagram.Model (Model(Model))
import qualified Diagram.Model as Mdl
import qualified Diagram.Rules as R
import Diagram.Mesh (Mesh(Mesh))
import qualified Diagram.Mesh as Mesh
import Diagram.Progress

main :: IO ()
main = do
  (maxStrLen, filename) <- (getArgs >>=) $ \case
    [filename] -> return (maxBound, filename)
    [maxLenStr, filename] -> return (read maxLenStr, filename)
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

  -- take n + count how many
  str0 :> src0 <- S.toList $ S.splitAt maxStrLen $ S.map fromEnum $
                  Q.unpack $ Q.fromHandle srcHandle

  msh0 <- Mesh.fromList R.empty str0

  -- <main loop>
  case () of
    _ -> go msh0 src0 where
      go msh@(Mesh mdl@(Model rs n ks) _ _ _ _ _ _ cdts) src = do
        sel <- Mesh.extLen msh
        let here = (++) (" [" ++ show (R.numSymbols rs) ++ "]: ")
            scale = fromIntegral srcLen / fromIntegral sel

            -- <Mdl.scaledInformation>
            sn     = scale * fromIntegral n
            rsInfo = ceiling @_ @Int $ R.information rs
            nInfo  = ceiling @_ @Int $ eliasInfo (round sn)
            ksInfo = ceiling @_ @Int $ Mdl.fDistrInfo sn (fromIntegral $ MV.length ks)
        ssInfo <- ceiling @_ @Int <$> Mdl.scaledStringInfo scale mdl
        let approxTotalInfo = rsInfo + nInfo + ksInfo + ssInfo
            -- </Mdl.scaledInformation>

            approxRatio = fromIntegral approxTotalInfo / origInfo
            approxFactor = recip approxRatio

        putStrLn $ here $ "LEN: " ++
          printf ("%s bits (%s + %s + %s + %s), %.2f%% of orig., "
                  ++ "factor: %.4f, over %.2f%% of input")
          (commaize approxTotalInfo)
          (commaize rsInfo)
          (commaize nInfo)
          (commaize ksInfo)
          (commaize ssInfo)
          (approxRatio * 100)
          approxFactor
          (100 * recip scale)

        cdtList <- S.toList_ $
          S.mapM (\cdt -> (,cdt) <$> uncurry (Mdl.scaledInfoDelta scale mdl) cdt) $
          withPB (M.size cdts) (here "Computing losses") $
          S.each $ M.toList cdts

        putStrLn $ here "Sorting candidates..."
        (loss,((s0,s1),n01)) <- case L.sort cdtList of
          [] -> error "no candidates"
          (c@(loss,_):cdts') -> do
            when (loss < 0) $ putStrLn $ here $
                              "Intro: \n   " ++ showCdt rs c
            putStrLn $ here "Next top candidates:"
            forM_ (take 4 cdts') (putStrLn . ("   " ++) . showCdt rs)
            return c

        hPutStrLn csvHandle $
          printf "%d, %.4f, %d, %d, %d, %d, %d, %d, %d, %d, %.2f, %s, %s, %s"
          (R.numSymbols rs) approxFactor -- %d, %.4f
          approxTotalInfo rsInfo nInfo ksInfo ssInfo -- %d, %d, %d, %d, %d
          s0 s1 n01 loss -- %d, %d, %d, %f
          (R.toEscapedString rs [s0])
          (R.toEscapedString rs [s1])
          (R.toEscapedString rs [s0,s1])
        hFlush csvHandle

        -- [EXIT]
        when (loss > 0) ( putStrLn (here "Reached minimum. Terminating.")
                          >> hClose csvHandle
                          >> exitSuccess )

        (_s01, msh') <- Mesh.pushRule msh (s0,s1)
        (msh'', src') <- fill msh' src

        putStrLn ""
        go msh'' src'
  -- </main loop>

  where
    fill msh src
      | Mesh.full msh = return (msh,src)
      | otherwise = (S.next src >>=) $ \case
          Left r -> return (msh, return r)
          Right (s,src') -> Mesh.snoc msh s >>= flip fill src'

    showCdt rs (loss,((s0,s1),n01)) = printf "%+.2f bits (%d × s%d s%d): %s + %s ==> %s"
      loss n01 s0 s1
      (show $ R.toString rs [s0])
      (show $ R.toString rs [s1])
      (show $ R.toString rs [s0,s1])

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

-- TODO: write this properly
commaize :: (Integral a, Show a) => a -> String
commaize n =
  let s = show $ abs $ fromIntegral @_ @Integer n
      chunks = reverse . fmap reverse . group3 . reverse $ s
      body = L.intercalate "," chunks
  in (if n < 0 then "-" else "") ++ body
  where
    group3 :: [a] -> [[a]]
    group3 [] = []
    group3 xs = let (h,t) = splitAt 3 xs in h : group3 t
