{-# LANGUAGE LambdaCase, ScopedTypeVariables, TypeApplications #-}
{-# LANGUAGE OverloadedStrings #-}
module Diagram (module Diagram) where

import System.IO (hClose, hFileSize, hFlush, hPutStrLn, openFile, IOMode(WriteMode, ReadMode))
import System.Directory (createDirectoryIfMissing)
import System.FilePath (takeBaseName)
import System.Environment (getArgs)
import System.Exit (exitFailure)

import Control.Monad

import Text.Printf (printf)
import Data.Time (getCurrentTime, formatTime, defaultTimeLocale)
import qualified Data.List as L
import qualified Data.Map.Strict as M
import qualified Streaming.Prelude as S
import qualified Streaming.ByteString as Q

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

  let strLen = min maxStrLen $ fromInteger srcLen
  (msh0, asrc0) <- Mesh.fromStream strLen $
                   withPB strLen "Initializing mesh" $
                   S.splitAt maxStrLen $
                   Q.unpack $ Q.fromHandle srcHandle
  -- <main loop>
  case () of
    _ -> go msh0 (S.map fromEnum asrc0) -- go

      where
      go msh@(Mesh mdl@(Model rs _ _) _ _ _ _ _ _ cdts) src = do
        sel <- Mesh.extLen msh
        let here = (++) (" [" ++ show (R.numSymbols rs) ++ "]: ")
            scale = fromIntegral srcLen / fromIntegral sel

        cdtList <- S.toList_ $
          S.mapM (\cdt@(s0s1,(n01,_)) -> do
                     loss <- Mdl.scaledInfoDelta scale mdl s0s1 n01
                     return (loss,cdt)) $
          withPB (M.size cdts) (here "Computing losses") $
          S.each $ M.toList cdts

        putStrLn $ here "Sorting candidates..."
        (minLoss,((s0,s1),(n01,_))) <- case L.sort cdtList of
          [] -> error "no candidates"
          (c@(loss,_):cdts') -> do
            when (loss < 0) $ putStrLn $ here $
                              "Intro: \n   " ++ showCdt rs c
            putStrLn $ here "Next top candidates:"
            forM_ (take 4 cdts') (putStrLn . ("   " ++) . showCdt rs)
            return c

        -- <log stats>
        (rsInfo, nInfo, ksInfo, ssInfo) <- Mdl.scaledInformationParts scale mdl
        let approxInfo = rsInfo + nInfo + ksInfo + ssInfo
            approxRatio = approxInfo / origInfo
            approxFactor = recip approxRatio

        -- STDOUT
        putStrLn $ here $ "LEN: " ++
          printf ("%s bits (%s + %s + %s + %s), %.2f%% of orig., "
                  ++ "factor: %.4f, over %.2f%% of input")
          (commaize $ ceiling @_ @Int approxInfo)
          (commaize $ ceiling @_ @Int rsInfo)
          (commaize $ ceiling @_ @Int nInfo)
          (commaize $ ceiling @_ @Int ksInfo)
          (commaize $ ceiling @_ @Int ssInfo)
          (approxRatio * 100)
          approxFactor
          (100 * recip scale)

        -- CSV
        hPutStrLn csvHandle $
          printf "%d, %.4f, %d, %d, %d, %d, %d, %d, %d, %d, %.2f, %s, %s, %s"
          (R.numSymbols rs) approxFactor -- %d, %.4f
          (ceiling @_ @Int approxInfo) -- %d
          (ceiling @_ @Int rsInfo) -- %d
          (ceiling @_ @Int nInfo) -- %d
          (ceiling @_ @Int ksInfo) -- %d
          (ceiling @_ @Int ssInfo) -- %d
          s0 s1 n01 minLoss -- %d, %d, %d, %f
          (R.toEscapedString rs [s0])
          (R.toEscapedString rs [s1])
          (R.toEscapedString rs [s0,s1])
        hFlush csvHandle
        putStrLn ""
        -- </log stats>

        if minLoss > 0
          then putStrLn (here "Reached minimum. Terminating.")
               >> hClose csvHandle -- end

          else Mesh.pushRule msh (s0,s1)
               >>= flip fill src . snd
               >>= uncurry go -- (msh'', src')

  -- </main loop>
  where
    fill msh src
      | Mesh.full msh = return (msh,src)
      | otherwise = (S.next src >>=) $ \case
          Left r -> return (msh, return r)
          Right (s,src') -> Mesh.snoc msh s >>= flip fill src'

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
