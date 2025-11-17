{-# LANGUAGE ScopedTypeVariables, TypeApplications #-}
{-# LANGUAGE OverloadedStrings #-}
module Diagram (module Diagram) where

import System.IO (hClose, hFileSize, hFlush, hPutStrLn, openFile, IOMode(WriteMode, ReadMode))
import System.Directory (createDirectoryIfMissing)
import System.FilePath (takeBaseName)

import Options.Applicative

import Control.Monad

import Text.Printf (printf)
import Data.Time (getCurrentTime, formatTime, defaultTimeLocale)
import qualified Data.List as L
import qualified Data.Map.Strict as M
import Numeric.MathFunctions.Comparison (relativeError)

import qualified Data.Vector.Unboxed as U
import qualified Data.Vector.Generic.Mutable as MV

import qualified Streaming.Prelude as S
import qualified Streaming.ByteString as Q

import qualified Diagram.Rules as R
import Diagram.Model (Model(Model))
import qualified Diagram.Model as Mdl
import qualified Diagram.Joints as Joints
import Diagram.Mesh (Mesh(Mesh))
import qualified Diagram.Mesh as Mesh
import Diagram.Progress

-- | Command-line options for the diagram program
data Options = Options
  { optFilename        :: !FilePath
  , optSubsample       :: !Int
  , optVerifyCandidate :: !Bool
  } deriving (Show)

-- | Parser for command-line options
optionsParser :: Parser Options
optionsParser = Options
  <$> argument str
      ( metavar "FILENAME"
     <> help "Input file to process" )
  <*> option auto
      ( long "subsample"
     <> metavar "VAL"
     <> value maxBound
     <> help "Subsample size (default: process entire file)" )
  <*> switch
      ( long "verify"
     <> help "Run verification code for candidate selection" )

main :: IO ()
main = do
  opts <- execParser $ info (optionsParser <**> helper)
    ( fullDesc
   <> progDesc "Process FILENAME and generate compression diagram"
   <> header "diagram - a compression analysis tool" )

  let maxStrLen = optSubsample opts
      filename = optFilename opts
      verifyCandidate = optVerifyCandidate opts

  srcHandle <- openFile filename ReadMode
  srcByteLen <- hFileSize srcHandle -- number of atoms in the source

  createDirectoryIfMissing True "data"
  currentTime <- getCurrentTime
  let timestamp = formatTime defaultTimeLocale "%Y%m%d-%H%M%S" currentTime
      logFilePath = "data/" ++ timestamp ++ "-"
                    ++ takeBaseName filename ++ ".csv"
  csvHandle <- openFile logFilePath WriteMode

  let strLen = min maxStrLen $ fromInteger srcByteLen
      codeLen0 = strLen * 8
      sls0 = U.replicate 256 (1 :: Int) -- symbol lengths
  msh0 <- Mesh.fromStream strLen $
          join $ withPB strLen "Initializing mesh" $ S.splitAt maxStrLen $
          Q.unpack $ Q.fromHandle srcHandle
  -- <main loop>
  case () of
    _ -> go codeLen0 sls0 msh0 -- go

      where
      go codeLen sls msh@(Mesh mdl@(Model rs n ks) _ jts _ ls _) = do
        let numSymbols = R.numSymbols rs
            here = (++) (" [" ++ show numSymbols ++ "]: ")

        -- :: Print stats to STDOUT :: -
        meshByteLen <- MV.ifoldl' (\acc i k -> acc + k * (sls U.! i)) 0 ks -- O(m)
        (mCodeLen, rsCodeLen, nCodeLen
          , ksCodeLen, ssCodeLen) <- Mdl.codeLenParts mdl
        let codeLen' = mCodeLen + rsCodeLen + nCodeLen + ksCodeLen + ssCodeLen
            ratio = fromIntegral codeLen'
                    / fromIntegral (meshByteLen * 8) :: Double
            factor = recip ratio
            srcCoverage = fromIntegral meshByteLen
                          / fromIntegral srcByteLen :: Double
        putStrLn ""
        putStrLn $ here $ printf "LEN CHANGE: %s bits" $
          commaize (codeLen' - codeLen)
        putStrLn $ here $
          printf ("LEN: %s bits (%s + %s + %s + %s + %s), %.2f%% of orig., "
                  ++ "factor: %.4f, over %.2f%% of input")
          (commaize codeLen')
          (commaize mCodeLen)
          (commaize rsCodeLen)
          (commaize nCodeLen)
          (commaize ksCodeLen)
          (commaize ssCodeLen)
          (ratio * 100)
          factor
          (100 * srcCoverage)

        -- :: Find next rule :: --
        let (minLoss, s0s1s) = Joints.findMin numSymbols n ls
            (s0,s1) = head s0s1s -- TODO: something smarter?
        let (k01,_) = jts M.! (s0,s1)

        putStrLn $ here $ "INTRO: " ++
          printf "%s + %s ==> %s (%d × s%d s%d) (%+.2f bits)"
          (show $ R.toString rs [s0])
          (show $ R.toString rs [s1])
          (show $ R.toString rs [s0,s1])
          k01 s0 s1 minLoss

        -- <verification>
        when verifyCandidate $ do
          k0 <- MV.read ks s0
          k1 <- MV.read ks s1
          cdtList <- S.toList_ $
            S.mapM (\cdt@(s0s1,(n01',_)) -> do
                       loss <- Mdl.naiveInfoDelta mdl s0s1 n01'
                       return (loss,cdt)) $
            withPB (M.size jts) (here "Computing losses (--verify)") $
            S.each $ M.toList jts

          putStrLn $ here "Sorting candidates (--verify)..."
          (minLoss',((s0',s1'),(k01',_))) <- case L.sort cdtList of
            [] -> error "no candidates"
            (c@(loss,_):cdts') -> do
              when (loss < 0) $ putStrLn $ here $
                                "Top candidate: \n   " ++ showCdt rs c
              putStrLn $ here "Next top candidates:"
              forM_ (take 4 cdts') (putStrLn . ("   " ++) . showCdt rs)
              return c

          when (relativeError minLoss minLoss' > 1e-5
                || notElem (s0',s1') s0s1s) $ do
            let rLoss = Mdl.rLoss numSymbols
                nLoss = Mdl.nLoss n k01
                kLoss = Mdl.kLoss numSymbols n k01
                sLoss | s0 == s1 = Mdl.sLoss1 k01 k0
                      | otherwise = Mdl.sLoss2 k01 k0 k1
            naiveParts <- Mdl.naiveInfoDeltaParts mdl (s0',s1') k01'
            error $ "loss mismatch:\nfrom map:   "
              ++ show (minLoss, k01, head s0s1s, tail s0s1s)
              ++ "\nfields:     " ++ show (rLoss,nLoss,kLoss,sLoss)
              ++ "\nfrom naive: " ++ show (minLoss', k01', (s0',s1'))
              ++ "\nfields:     " ++ show naiveParts
        -- </verification>

        -- :: Print stats to CSV :: --
        hPutStrLn csvHandle $
          printf "%d, %.4f, %d, %d, %d, %d, %d, %d, %d, %d, %d, %.2f, %s, %s, %s"
          (R.numSymbols rs) -- %d
          factor -- %.4f
          codeLen' -- %d
          mCodeLen -- %d
          rsCodeLen -- %d
          nCodeLen -- %d
          ksCodeLen -- %d
          ssCodeLen -- %d
          s0 s1 k01 minLoss -- %d, %d, %d, %f
          (R.toEscapedString rs [s0])
          (R.toEscapedString rs [s1])
          (R.toEscapedString rs [s0,s1])
        hFlush csvHandle

        -- [EXIT]
        if minLoss > 0
          then putStrLn (here "Reached minimum. Terminating.")
               >> hClose csvHandle -- end
          else let sls' = U.snoc sls $ sum $ R.symbolLength rs <$> [s0,s1]
               in Mesh.pushRule msh (s0,s1) >>= go codeLen' sls' . snd -- continue
  -- </main loop>

  where
    showCdt rs (loss,((s0,s1),(n01,_))) = printf "%+.2f bits (%d × s%d s%d): %s + %s ==> %s"
      loss n01 s0 s1
      (show $ R.toString rs [s0])
      (show $ R.toString rs [s1])
      (show $ R.toString rs [s0,s1])

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
