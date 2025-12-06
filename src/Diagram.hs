{-# LANGUAGE ScopedTypeVariables, TypeApplications, LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module Diagram (module Diagram) where

import System.IO (hClose, hFileSize, hFlush, hPutStrLn, openFile, IOMode(WriteMode, ReadMode))
import System.Directory (createDirectoryIfMissing)
import System.FilePath (takeBaseName)
import System.Exit (exitSuccess)

import Options.Applicative

import Control.Monad

import Text.Printf (printf)
import Data.Maybe
import Data.Time (getCurrentTime, formatTime, defaultTimeLocale)
import qualified Data.List as L
import qualified Data.Map.Strict as M
import Numeric.MathFunctions.Comparison (relativeError)

import qualified Data.Vector.Unboxed as U
import qualified Data.Vector.Generic.Mutable as MV

import Streaming
import qualified Streaming.Prelude as S
import qualified Streaming.ByteString as Q

import qualified Diagram.Rules as R
import Diagram.Model (Model(Model))
import qualified Diagram.Model as Mdl
import qualified Diagram.Joints as Joints
import Diagram.Mesh (Mesh(Mesh))
import qualified Diagram.Mesh as Mesh
import Diagram.TrainMesh (TrainMesh(TrainMesh))
import qualified Diagram.TrainMesh as TrainMesh
import Diagram.Progress (withPB)

data LossFn = CodeLen -- code length formula (default)
            | Count   -- max count
            | Cond    -- pointwise mutual information: k01 * (log p(s1|s0) - log p(s1))
            | WCond !Double -- weighted pointwise mutual information
  deriving (Show,Read)

-- | Command-line options for the diagram program
data Options = Options
  { optFilename         :: !FilePath
  , optLoss             :: !(Maybe LossFn)
  , optEval             :: !(Maybe FilePath)
  , optTargetM          :: !(Maybe Int)
  -- , optTolerance        :: !(Maybe Int)
  , optSubsample        :: !(Maybe Int)
  , optVerifyMinLoss    :: !Bool
  , optVerifyStringMeta :: !Bool
  } deriving (Show)

-- | Parser for command-line options
optionsParser :: Parser Options
optionsParser = Options
  <$> argument str
  ( metavar "FILENAME"
    <> help "Training data" )
  <*> optional
  (option auto
    ( long "loss"
      <> short 'l'
      <> metavar "FUN"
      <> help "Loss function [CodeLen (default), Count, Cond]" ))
  <*> optional
  (option str
    ( long "eval"
      <> short 'e'
      <> metavar "FILENAME"
      <> help "String to evaluate loss on (default: same as train)" ))
  <*> optional
  (option auto
    ( long "to-size"
      <> short 'm'
      <> metavar "NUM"
      <> help "Produce dictionary of given size" ))
  -- <*> optional
  -- (option auto
  --   ( long "tolerance"
  --     <> short 't'
  --     <> metavar "NUM"
  --     <> help "Number of positive losses tolerated (default: 0)" ))
  <*> optional
  (option auto
    ( long "subsample"
      <> short 's'
      <> metavar "VAL"
      <> help "Subsample size (default: process entire file)" ))
  <*> switch
  ( long "verify-min-loss"
    <> help "Verify top candidate has min loss" )
  <*> switch
  ( long "verify-string-meta"
     <> help "Verify train length, counts & joint counts" )

main :: IO ()
main = do
  opts <- execParser $ info (optionsParser <**> helper) fullDesc

  let maxStrLen = fromMaybe maxBound (optSubsample opts)
      filename = optFilename opts
      verifyMinLoss = optVerifyMinLoss opts
      verifyStringMeta = optVerifyStringMeta opts
      policy = fromMaybe CodeLen $ optLoss opts
      lossFn = case policy of
        CodeLen -> Joints.codeLenLoss
        Count -> Joints.maxCountLoss
        Cond -> Joints.condLoss
        WCond a -> Joints.wCondLoss a
      -- hp0 = fromMaybe 0 $ optTolerance opts
      -- targetM = fromMaybe 256 $ optTargetM opts

  srcHandle <- openFile filename ReadMode
  srcByteLen <- hFileSize srcHandle -- number of atoms in the source

  createDirectoryIfMissing True "data"
  currentTime <- getCurrentTime
  let timestamp = formatTime defaultTimeLocale "%Y%m%d-%H%M%S" currentTime
      logFilePath = "data/" ++ timestamp ++ "-"
                    ++ takeBaseName filename ++ ".csv"
  csvHandle <- openFile logFilePath WriteMode

  let strLen = min maxStrLen $ fromInteger srcByteLen
      -- codeLen0 = strLen * 8
      sls0 = U.replicate 256 (1 :: Int) -- symbol lengths
  msh0 <- TrainMesh.fromStream lossFn strLen $
          join $ withPB strLen "Initializing train mesh" $ S.splitAt maxStrLen $
          Q.unpack $ Q.fromHandle srcHandle

  (evalLen0, meval0) <- case optEval opts of
    Nothing -> return (0, Nothing)
    Just evalFilename -> do
      evalHandle <- openFile evalFilename ReadMode
      evalLen <- fromInteger @Int <$> hFileSize evalHandle
      (eval0, _) <- Mesh.fromStream evalLen $
                    withPB evalLen "Initializing eval mesh" $
                    Q.unpack $ Q.fromHandle evalHandle
      return (evalLen, Just eval0)

  -- <main loop>
  case () of
    _ -> go sls0 msh0 meval0 -- go

      where
      go sls msh@(TrainMesh (Mesh mdl@(Model rs n ks) _ jts) _ ls _) meval = do
        let numSymbols = R.numSymbols rs
            here = (++) (" [" ++ show numSymbols ++ "]: ")

        -- :: Print stats to STDOUT :: -
        meshByteLen <- -- TODO: something smarter than O(m) every cycle
          MV.ifoldl' (\acc i k -> acc + k * (sls U.! i)) 0 ks
        (mCodeLen, rsCodeLen, nCodeLen, ksCodeLen, ssCodeLen) <-
          Mdl.codeLenParts mdl

        let trainCodeLen = mCodeLen + rsCodeLen + nCodeLen + ksCodeLen + ssCodeLen
            trainRatio = fromIntegral trainCodeLen
                         / fromIntegral (meshByteLen * 8) :: Double
            trainFactor = recip trainRatio
            srcCoverage = fromIntegral meshByteLen
                          / fromIntegral srcByteLen :: Double
        putStrLn ""
        putStrLn $ here $
          printf ("TRAIN LEN: %s bits (%s + %s + %s + %s + %s), %.2f%% of orig., "
                  ++ "factor: %.4f, N = %s (%.2f%% of input)")
          (commaize trainCodeLen)
          (commaize mCodeLen)  -- (train)
          (commaize rsCodeLen) -- (train)
          (commaize nCodeLen)  -- (train)
          (commaize ksCodeLen) -- (train)
          (commaize ssCodeLen) -- (train)
          (trainRatio * 100)
          trainFactor
          (commaize n)
          (100 * srcCoverage)

        -- :: Find next rule :: --
        let (minLoss, s0s1s) = Joints.findMin numSymbols n ls
            (s0,s1) = head s0s1s -- TODO: something smarter?
            (k01,_) = jts M.! (s0,s1)

        putStrLn $ here $ "INTRO: " ++
          printf "%s + %s ==> %s (%d × s%d s%d) (loss: %+.2f)"
          (show $ R.toString rs [s0])
          (show $ R.toString rs [s1])
          (show $ R.toString rs [s0,s1])
          k01 s0 s1 minLoss

        -- :: Maybe Eval :: --
        (factor, codeLen, meval') <- case meval of
          Nothing -> return (trainFactor, trainCodeLen, Nothing)
          Just emsh@(Mesh emdl _ _) -> do
            -- : stats :
            evalCodeLen <- Mdl.codeLen emdl
            let evalRatio = fromIntegral evalCodeLen
                            / fromIntegral (evalLen0 * 8) :: Double
                evalFactor = recip evalRatio
            -- : push rule :
            (_, _, emsh') <- Mesh.pushRule verifyStringMeta emsh (s0,s1)
            return (evalFactor, evalCodeLen, Just emsh')

        -- :: Print stats to CSV :: --
        hPutStrLn csvHandle $
          printf "%d, %.4f, %d, %d, %d, %d, %d, %d, %d, %d, %d, %.2f, %s, %s, %s"
          (R.numSymbols rs) -- %d
          factor -- %.4f
          codeLen -- %d
          mCodeLen rsCodeLen nCodeLen ksCodeLen ssCodeLen -- %d %d %d %d %d
          s0 s1 k01 minLoss -- %d, %d, %d, %f
          (R.toEscapedString rs [s0])
          (R.toEscapedString rs [s1])
          (R.toEscapedString rs [s0,s1])
        hFlush csvHandle

        -- <verification>
        when verifyMinLoss $ do
          cdtList <- S.toList_ $
            S.mapM (\cdt@(s0s1,(k01',_)) -> do
                       k0 <- MV.read ks $ fst s0s1
                       k1 <- MV.read ks $ snd s0s1
                       let k0k1 = (k0,k1)
                           loss = Joints.evalLoss lossFn numSymbols n k01' s0s1 k0k1
                       return (loss, cdt)) $
            withPB (M.size jts) (here "Evaluating all losses (--verify-min-loss)") $
            S.each $ M.toList jts

          putStrLn $ here "Sorting joints by loss (--verify-min-loss)..."
          (minLoss',((s0',s1'),(k01',_))) <- case L.sort cdtList of
            [] -> error "no candidates"
            (c@(loss,_):cdts') -> do
              when (loss < 0) $
                putStr (here "Top candidate: \n   ") >> printCdt rs ks c
              putStrLn (here "Next top candidates:")
              forM_ (take 4 cdts') $ \c' -> putStr "   "
                                            >> printCdt rs ks c'
              return c

          -- TODO: relax this condition: sometimes the head candidate is
          -- not the one with the minLoss because +/- relative error
          -- pushes it a bit back
          when (relativeError minLoss minLoss' > 1e-5
                || notElem (s0',s1') s0s1s) $ do
            -- let rLoss = Mdl.rLoss numSymbols
            --     nLoss = Mdl.nLoss n k01
            --     kLoss = Mdl.kLoss numSymbols n k01
            -- k0 <- MV.read ks s0
            -- k1 <- MV.read ks s1
            -- let sLoss | s0 == s1 = Mdl.sLoss1 k01 k0
            --           | otherwise = Mdl.sLoss2 k01 k0 k1
            naiveParts <- Mdl.naiveInfoDeltaParts mdl (s0',s1') k01'
            error $ "loss mismatch:\nfrom map:   "
              ++ show ((("minLoss" :: String, minLoss)
                       ,("k01" :: String, k01))
                      ,(("head s0s1s" :: String, head s0s1s)
                       ,("tail s0s1s" :: String, tail s0s1s)))
--              ++ "\nfields:     " ++ show (rLoss,nLoss,kLoss,sLoss)
              ++ "\nfrom naive: " ++ show (minLoss', k01', (s0',s1'))
              ++ "\nfields:     " ++ show naiveParts
        -- </verification>

        -- [EXIT]
        when (maybe (minLoss > 0) (numSymbols >=) (optTargetM opts)) $
          putStrLn (here "Reached stopping condition. Terminating.")
          >> hClose csvHandle
          >> exitSuccess

        (_, mdl') <- Mdl.pushRule mdl (s0,s1) k01 -- clones
        codeLen' <- Mdl.codeLen mdl'

        let lenChange = codeLen' - trainCodeLen
            lenChangeStr = case compare lenChange 0 of
              GT -> "\ESC[31m+" ++ commaize lenChange ++ "\ESC[0m" -- red
              LT -> "\ESC[32m" ++ commaize lenChange ++ "\ESC[0m"  -- green
              EQ -> commaize lenChange                             -- white
        putStrLn $ here $ printf "TRAIN LEN CHANGE: %s bits" lenChangeStr

        let sls' = U.snoc sls $ sum $ R.symbolLength rs <$> [s0,s1]
        (_, msh') <- TrainMesh.pushRule verifyStringMeta msh (s0,s1)
        go sls' msh' meval' -- continue

  -- </main loop>

  where
    printCdt rs ks (loss,((s0,s1),(n01,_))) = do
      k0 <- MV.read ks s0
      k1 <- MV.read ks s1
      printf "%+.2f: %d × s%d(%d) s%d(%d): %s + %s ==> %s\n"
        loss n01 s0 k0 s1 k1
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
