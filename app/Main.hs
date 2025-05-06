module Main where

import System.Environment (getArgs)
import System.Exit (die)
import qualified Data.ByteString as BS

import Diagram ()

main :: IO ()
main = do
  args <- getArgs
  case args of
    [filePath] -> do
      putStrLn "Reading file..."
      _bs <- BS.readFile filePath
      return ()

    _other -> die "Usage: program <file-path>"

