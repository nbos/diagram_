module Diagram.Streaming (module Diagram.Streaming) where

import Streaming
import qualified Streaming.Prelude as S
import Data.Maybe

import Diagram.Util

-- | Return the return values of the streams if they are equal, Nothing
-- if they are not
eq :: (Monad m, Eq a) =>
      Stream (Of a) m r -> Stream (Of a) m s -> m (Maybe (r,s))
eq str0 str1 = do
  ea0 <- S.next str0
  ea1 <- S.next str1
  case (ea0,ea1) of
    (Left r, Left s) -> return $ Just (r,s)
    (Right (a0,str0'), Right (a1,str1')) | a0 == a1 -> eq str0' str1'
                                       | otherwise -> return Nothing
    (_, _) -> return Nothing

-- | True if the streams contain equal sequences of values
eq_ :: (Monad m, Eq a) => Stream (Of a) m r -> Stream (Of a) m s -> m Bool
eq_ = fmap isJust .: eq
