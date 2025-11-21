{-# LANGUAGE OverloadedStrings #-}
module Diagram.Progress (module Diagram.Progress) where

import qualified Data.Text.Lazy as Text
import System.ProgressBar
import Streaming
import qualified Streaming.Prelude as S

-- | Evaluate to WHNF each element of the list and log the progress with
-- a ProgressBar given the length of the list and a label
pbSeq :: Int -> String -> [a] -> IO [a]
pbSeq n message as = do
  pb <- newPB n message
  S.toList_ $
    S.mapM (\a -> incPB pb >> return a) $ -- streaming handles Seq
    S.each as

-- | Evaluate to WHNF each element of the list and log the progress with
-- a ProgressBar without knowing the length of the list given a label
pbSeq' :: String -> [a] -> IO [a]
pbSeq' message as = do
  pb <- newPB' message
  S.toList_ $
    S.mapM (\a -> incPB pb >> return a) $
    S.each as

withPB :: MonadIO m => Int -> String -> Stream (Of a) m r -> Stream (Of a) m r
withPB n message str = do
  pb <- lift $ liftIO $ newPB n message
  S.mapM (\a -> liftIO (incPB pb) >> return a) str

-- | Increment ProgressBar by 1
incPB :: ProgressBar s -> IO ()
incPB pb = incProgress pb 1

-- | Create a new ProgressBar given amount of work to do and a label
newPB :: Int -> String -> IO (ProgressBar ())
newPB n message = newProgressBar style 10 (Progress 0 n ())
  where
    width = 70 -- lower if using a smaller window
    nLen = length $ show n
    exactLen = 2*nLen + 1
    message' = padOrTruncate (width - exactLen) message
    style = defStyle{
      stylePrefix = msg (Text.pack message' <> " ") <> exact
                    <> msg " " <> percentage,
                    -- <> msg " ETA: " <> remainingTime renderDuration "00"
                    -- <> msg " DUR: " <> elapsedTime renderDuration,
      stylePostfix = mempty,
      styleDone = '#',
      styleCurrent = '#',
      styleTodo = '-' }

-- | Create a new ProgressBar for an undetermined amount of work to do
-- given a label
newPB' :: String -> IO (ProgressBar ())
newPB' message = newProgressBar style 10 (Progress 0 (2^(28::Int)) ())
  where
    style = defStyle{
      stylePrefix = msg (Text.pack message <> " ") <> customExact
                    <> msg " " <> customPercentage,
                    -- <> msg " ETA: " <> customETA
                    -- <> msg " DUR: " <> elapsedTime renderDuration,
      stylePostfix = mempty,
      styleDone = '#',
      styleCurrent = '#',
      styleTodo = '-' }
    
    customExact = Label $ \progress _ -> 
      Text.pack $ show (progressDone progress) ++ "/??"
    
    customPercentage = Label $ \_ _ -> "??"
    -- customETA = Label $ \_ _ -> "∞"

padOrTruncate :: Int -> String -> String
padOrTruncate width str = case compare len width of
  EQ -> str
  LT -> str ++ replicate (width - len) ' '
  GT | width <= 3 -> take width (replicate width '.')
     | otherwise -> take (width - 3) str ++ "..."
  where len = length str
