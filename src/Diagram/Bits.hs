module Diagram.Bits where

import Control.Exception (assert)
import Data.Word (Word8, Word16, Word32)
import Data.Bits (finiteBitSize, shiftL, shiftR, (.|.), (.&.))

pack8s :: Word8 -> Word8 -> Int
pack8s a b = (fromIntegral a `shiftL` 8) .|. fromIntegral b

unpack8s :: Int -> (Word8, Word8)
unpack8s i = (a, b)
  where a = fromIntegral $ (i `shiftR` 8) .&. 0xFF
        b = fromIntegral $ i .&. 0xFF

pack16s :: Word16 -> Word16 -> Int
pack16s a b = (fromIntegral a `shiftL` 16) .|. fromIntegral b

unpack16s :: Int -> (Word16, Word16)
unpack16s i = (a, b)
  where a = fromIntegral $ (i `shiftR` 16) .&. 0xFFFF
        b = fromIntegral $ i .&. 0xFFFF

pack32s :: Word32 -> Word32 -> Int
pack32s a b = assert (finiteBitSize (0 :: Int) >= 64) $
              (fromIntegral a `shiftL` 32) .|. fromIntegral b

unpack32s :: Int -> (Word32, Word32)
unpack32s i = assert (finiteBitSize (0 :: Int) >= 64) $
              (a, b)
  where a = fromIntegral $ (i `shiftR` 32) .&. 0xFFFFFFFF
        b = fromIntegral $ i .&. 0xFFFFFFFF
