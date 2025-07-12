{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
module Diagram.Candidates (module Diagram.Candidates) where

import Data.Maybe
import Data.Tuple.Extra
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

import Diagram.Head (Head,Symbol)
import qualified Diagram.Head as H
import Diagram.Rules (Rules)
import qualified Diagram.Rules as R

err :: [Char] -> a
err = error . ("Diagram.Candidates: " ++)

data Candidate = Candidate {
  cParts :: !(Symbol,Symbol),
  cPP :: !Symbol,
  cCount :: !Int
}

data PPType = Atomic -- ^ Case: pp is atomic and necessarily begins
                     -- h1. No overlap between h0 and h1.

            | S0IsFst -- ^ Case: pp ends h0, right after s0. Symbol `snd
                      -- pp` begins h1.

            | S1IsSnd -- ^ Case: pp begins h1 where s1 is not exercised
                      -- but only produced by pp, i.e. the presence of
                      -- pp implies the presence of s1.

            | SndS0AndFstS1 -- ^ Case: pp is in a singleton head
                            -- overlapping both h0 and h1.

ppType :: Rules -> Candidate -> PPType
ppType rs (Candidate (s0,s1) pp _) = case rs R.!? pp of
  Nothing -> Atomic
  Just (ppA,_) | ppA == s0 -> S0IsFst
  Just (_,ppB) | ppB == s1 -> S1IsSnd
  Just _ -> SndS0AndFstS1 -- assert?

-- | Given a ruleset and a new rule, rewrite a string represented as a
-- list of heads and count the delta in candidates, returned in a map of
-- delta counts (positive or negative, non-zero)
updateString :: Rules -> Candidate -> Int -> [Head] -> ( Map (Int,Int) Int
                                                       , [Head] )
updateString rs cdt s01 hs =
  ( M.filter (/= 0) $ M.unionsWith (+) ms
  , catMaybes mhs )
  where
    mhs = applyRule rs cdt s01 hs
    chunks = deltaChunks [] $ zip hs mhs
    ms = (<$> chunks) $ \c ->
      let (shs,shs') = second catMaybes $ unzip c
          cs = H.countJoints rs shs
          cs' = H.countJoints rs shs'
      in M.filter (/= 0) $ M.unionWith (+) ((0-) <$> cs) cs'

    deltaChunks _ [] = []
    deltaChunks bwd (a:rest)
      | Just (fst a) == snd a = deltaChunks (a:bwd) rest
      | otherwise = let (as,bs) = first (a:) $ splitAfter2Eq rest
                    in as : deltaChunks (reverse as ++ bwd) bs

    splitAfter2Eq [] = ([],[])
    splitAfter2Eq [a] = ([a],[])
    splitAfter2Eq (a0:a1:rest)
      | Just (fst a0) == snd a0
      , Just (fst a1) == snd a1 = ([a0,a1], rest)
      | otherwise = let (as,bs) = splitAfter2Eq (a1:rest)
                    in (a0:as, bs)

-- | Given a ruleset and a new rule, rewrite a string represented as a
-- list of heads into a list of equal size with Nothing's in the place
-- of deleted heads.
applyRule :: Rules -> Candidate -> Int -> [Head] -> [Maybe Head]
applyRule rs cdt@(Candidate (s0,s1) pp _) s01 = case ppType rs cdt of
  Atomic -> go2 f
    where f h0 h1 = (snd h0 == s0
                     || (snd <$> (rs R.!? snd h0)) == Just s0)
                    && fst h1 == pp
                    && s1 `elem` R.prefixes rs (snd h1)
  S0IsFst -> go2 f
    where f h0 h1 = snd h0 == pp
                    && fst h0 /= pp
                    && s1 `elem` R.prefixes rs (snd h1)
  S1IsSnd -> go2 f
    where f h0 h1 = snd h0 == s0
                    && fst h1 == pp

  SndS0AndFstS1 -> go3 f
    where f h0 ih h1 = snd h0 == s0
                       && ih == (pp,pp)
                       && s1 `elem` R.prefixes rs (snd h1)
  where
    go2 f = go
      where
        go [] = []
        go [h] = [Just h]
        go (h0:h1:hs)
          | f h0 h1 = Just h0' : (if null rh1B then Nothing : go hs
                                  else go (h1':hs))
          | otherwise = Just h0 : go (h1:hs)
            where
              (rh1B,_) = span (/= s1) $ H.unpack rs h1 -- large to small
              h0' = s01 <$ h0 -- push s01
              h1' = (last rh1B, head rh1B) -- pack

    go3 f = go
      where
        go [] = []
        go [h] = [Just h]
        go [h0,h1] = Just <$> [h0,h1]
        go (h0:ih:h1:hs)
          | f h0 ih h1 = Just h0' : Nothing :
                         (if null rh1B then Nothing : go hs
                          else go (h1':hs))
          | otherwise = Just h0 : go (ih:h1:hs)
            where
              (rh1B,_) = span (/= s1) $ H.unpack rs h1 -- large to small
              h0' = s01 <$ h0 -- push s01
              h1' = (last rh1B, head rh1B) -- pack
