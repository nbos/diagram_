{-# LANGUAGE ScopedTypeVariables, RankNTypes #-}
{-# LANGUAGE LambdaCase #-}
-- | Construction rules
module Diagram.Rules (module Diagram.Rules) where

import Prelude

import Control.Monad
import Control.Monad.ST
import Control.Exception (assert)

import Data.Word (Word8)
import Data.Maybe
import Data.Tuple.Extra
import qualified Data.List as L
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import qualified Data.ByteString.UTF8 as UTF8
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Data.Trie (Trie)
import qualified Data.Trie as Trie

import qualified Data.Vector.Strict as B
import qualified Data.Vector.Unboxed as U
import qualified Data.Vector.Generic as V
import qualified Data.Vector.Generic.Mutable as MV

import Streaming
import qualified Streaming.Prelude as S

import qualified Codec.Elias.Natural as Elias
import qualified Codec.Arithmetic.Variety as Var
import Codec.Arithmetic.Variety.BitVec (BitVec)

import Diagram.Util
import Diagram.Information

type Sym = Int -- symbol

-- | Self-referrential vector of recipes for the construction of all
-- symbols above 256 indexed at s-256
type Rules = U.Vector (Sym,Sym)

-- | New empty rule set
empty :: Rules
empty = V.empty

-- | Number of rules
size :: Rules -> Int
size = V.length

-- | Number of defined symbols
numSymbols :: Rules -> Int
numSymbols = (256 +) . size

-- | O(len). Compute the length of a symbol
symbolLength :: Rules -> Sym -> Int
symbolLength rs = go
  where
    go s | s < 256   = 1
         | otherwise = let (s0,s1) = rs V.! (s - 256)
                       in go s0 + go s1

-- | O(numSymbols). Return a vector of the length of each symbol.
symbolLengths :: Rules -> U.Vector Int
symbolLengths rs = runST $ do
  mv <- MV.new (numSymbols rs)
  forM_ [0..255] $ \s -> MV.write mv s 1
  forM_ [256..numSymbols rs - 1] $ \s -> do
    let (s0,s1) = rs ! s
    len0 <- MV.read mv s0
    len1 <- MV.read mv s1
    MV.write mv s (len0 + len1)
  U.freeze mv

fromList :: [(Sym,Sym)] -> Rules
fromList = V.fromList

-- | Add a new symbol with a construction rule. Returns updated rules
-- and index of new symbol. O(n)
pushRule :: (Sym,Sym) -> Rules -> (Sym, Rules)
pushRule s0s1 rs =
  assert (uncurry (&&) $ both (< s01) s0s1)
  (s01, V.snoc rs s0s1)
  where s01 = numSymbols rs

-- | Lookup the rule for constructing a given symbol
(!) :: Rules -> Sym -> (Sym,Sym)
(!) rs s = rs V.! (s - 256)
infixl 9 !

-- | Lookup the rule for constructing a given symbol. Nothing returned
-- if the given symbol is atomic (<256) or not yet defined
(!?) :: Rules -> Sym -> Maybe (Sym,Sym)
(!?) = invLookup
infixl 9 !?

-- | Lookup the rule for constructing a given symbol. Nothing returned
-- if the given symbol is atomic (<256) or not yet defined
invLookup :: Rules -> Sym -> Maybe (Sym,Sym)
invLookup rs s | s < 256   = Nothing
               | otherwise = Just $ rs ! s

-- | Deconstruct a symbol back into a list of bytes
extension :: Rules -> Sym -> [Word8]
extension rs = go
  where
    go s | s < 256 = [toEnum s]
         | otherwise = let (s0,s1) = rs V.! (s - 256)
                       in go s0 ++ go s1

bytestring :: Rules -> Sym -> ByteString
bytestring = BS.pack .: extension

-- | List the symbols that are constructive prefixes of the given
-- symbol, from large to small, starting with the symbol itself and
-- ending with the first atomic symbol of its extension
prefixes :: Rules -> Sym -> [Sym]
prefixes rs = go
  where
    go s | s < 256 = [s]
         | otherwise = let (s0,_) = rs V.! (s - 256)
                       in s : go s0

-- | List the symbols that are constructive suffixes of the given
-- symbol, from large to small, starting with the symbol itself and
-- ending with the last atomic symbol of its extension
suffixes :: Rules -> Sym -> [Sym]
suffixes rs = go
  where
    go s | s < 256 = [s]
         | otherwise = let (_,s1) = rs V.! (s - 256)
                       in s : go s1

-- | "Left-reciprocal" of a symbol is the string of symbols after a
-- second symbol is removed from the right. The second symbol must be a
-- member of the suffixes of the first as specified by the `suffixes`
-- function. The extension of the subtracted symbol prepended by the
-- returned string is equal to the extension of the first given symbol.
lRecip :: Rules -> Sym -> Sym -> [Sym]
lRecip rs s01 s1 = go s01
  where
    go s | s == s1 = []
         | Just (l,r) <- rs !? s = l:go r
         | otherwise = error $ "bad arguments: "
                       ++ show (s01, s1, suffixes rs s01)

-- | "Right-reciprocal" of a symbol is the string of symbols after
-- another symbol is removed from the left. The second symbol must be a
-- member of the prefixes of the first as specified by the `prefixes`
-- functions. The extension of the returned string prepended by the
-- subtracted symbol is equal to the extension of the first given
-- symbol.
rRecip :: Rules -> Sym -> Sym -> [Sym]
rRecip rs s01 s0 = go [] s01
  where
    go acc s | s == s0 = acc
             | Just (l,r) <- rs !? s = go (r:acc) l
             | otherwise = error $ "bad arguments: "
                           ++ show (s01, s0, prefixes rs s01)

-- | Resolve the symbol back into a string of chars
toString :: Rules -> [Sym] -> String
toString = UTF8.toString
           . BS.pack
           .: concatMap
           . extension

toEscapedString :: Rules -> [Sym] -> String
toEscapedString = concatMap escapeChar .: toString
  where
    escapeChar '\n' = "\\n"    -- Replace newline with \n
    escapeChar '\t' = "\\t"    -- Replace tab with \t
    escapeChar '\r' = "\\r"    -- Replace carriage return with \r
    escapeChar '\\' = "\\\\"   -- Replace backslash with \\
    escapeChar '\"' = "\\\""   -- Replace double quote with \"
    escapeChar '\'' = "\\'"    -- Replace single quote with \'
    escapeChar ',' = "\\,"     -- for CSV
    escapeChar c    = [c]      -- Leave other characters unchanged

type FwdRules = Map (Sym,Sym) Sym -- (s0,s1) -> s01

subst :: Rules -> [Sym] -> [Sym]
subst rs = subst_ rs rsm []
  where rsm = toMap rs

-- | Given a rule set (forward) and a reversed list of previous symbols
-- (closest first) and a forward list of following symbols, return the
-- full list in forward order with all possible constructions made
subst_ :: Rules -> FwdRules -> [Sym] -> [Sym] -> [Sym]
subst_ rs rsm = reverse .: L.foldl' (revReduce rs rsm)

revReduce :: Rules -> FwdRules -> [Sym] -> Sym -> [Sym]
revReduce rs rsm = go
  where
    go [] s1 = [s1]
    go (s0:bwd) s1
      | null constrs = s1:s0:bwd
      | otherwise = flip go s01 $ L.foldl' go bwd recip01
      where
        s01 = minimum constrs
        recip01 = lRecip rs s0 (fst $ rs ! s01)
        constrs = catMaybes $
                  -- check for a construction between s0 and s1, and
                  (M.lookup (s0,s1) rsm :) $
                  -- check for a construction overriding one in s0...
                  fmap (\suf0 -> let (_,r0) = rs ! suf0
                                 in M.lookup (r0,s1) rsm
                                    >>= nothingIf (>= suf0)) $
                  -- ...over composite suffixes of s0
                  init $ suffixes rs s0

-- | Take exactly `n` fully constructed symbols from a stream of
-- potentially unconstructed or partially constructed symbols, returning
-- a stream equal in extension to the remainder but with its head
-- possibly partially constructed. Makes it possible to iteratively
-- consume a stream in chunks of given sizes.
splitAtSubst :: Monad m => Rules -> FwdRules -> Trie () -> Int ->
                Stream (Of Sym) m r -> Stream (Of Sym) m (Stream (Of Sym) m r)
splitAtSubst rs rsm trie = go []
  where
    yieldUntilPrefixing fwd
      | (hd:tl) <- fwd
      , null keys || keys == [key] = S.yield hd >>
                                     yieldUntilPrefixing tl
      | otherwise = return fwd -- :: extension of fwd is a prefix
      where
        key = BS.pack $ concatMap (extension rs) fwd
        keys = Trie.keys $ Trie.submap key trie

    go bwd n src = (lift (S.next src) >>=) $ \case
      Left r -> let (ss,rest) = splitAt n $ reverse bwd
                in S.each ss >>
                   return (S.each rest >> return r)
      Right (s,src') -> do
        let bwd' = revReduce rs rsm bwd s
        m :> rest <- S.length $ S.copy $ S.splitAt n $ -- yield at most `n`
                     yieldUntilPrefixing $ reverse bwd'
        extra :> fwd' <- lift $ S.toList rest
        if not (null extra) then return $ S.each extra >>
                                 S.each fwd' >> src' -- done
          else go (reverse fwd') (n - m) src'

--------------
-- INDEXING --
--------------

-- | Switch from an inverse to forward indexing of the construction
-- rules
toMap :: Rules -> FwdRules
toMap = M.fromList . flip zip [256..] . V.toList

asGen :: ((Sym,Sym) -> Sym) -> Rules -> B.Vector [Sym]
asGen f rs = V.create $ do
  mv <- MV.replicate (numSymbols rs) []
  forM_ [256..numSymbols rs - 1] $ \s ->
    MV.modify mv (s:) $ f (rs ! s)
  return mv
{-# INLINE asGen #-}

-- | For every symbol, the list of composite symbols that have that
-- symbol as first/left part.
asFsts :: Rules -> B.Vector [Sym]
asFsts = asGen fst

-- | For every symbol, the list of composite symbols that have that
-- symbol as second/right part.
asSnds :: Rules -> B.Vector [Sym]
asSnds = asGen snd

-------------------
-- SERIALIZATION --
-------------------

encode :: Rules -> BitVec
encode rs = lenCode <> rulesCode -- cat of rulesLen + rules
  where
    lenCode = Elias.encodeDelta $ fromIntegral $ V.length rs
    rulesCode = Var.encode $
                foldr (\(a,b) acc -> a : b : acc) [] $
                zipWith (\(s0,s1) base -> ( (fromIntegral s0, base)
                                          , (fromIntegral s1, base) ))
                (V.toList rs)
                [256::Integer ..]

decode :: BitVec -> Maybe (Rules, BitVec)
decode bv = do
  (len,bv') <- Elias.decodeDelta bv
  let bases = foldr (\a acc -> a:a:acc) [] $ -- dupe each
              take (fromIntegral len) [256..]
  (vals,bv'') <- Var.decode bases bv'
  Just ( V.fromList $ go $ fromIntegral <$> vals
       , bv'' )
  where
    go [] = []
    go (a:b:rest) = (a,b):go rest
    go (_:_) = error "impossible"

--------------------------
-- INFORMATION MEASURES --
--------------------------

-- | The amount of information (in bits) in the rule set (more
-- efficient)
information :: Rules -> Double
information rs = fromIntegral lenCodeLen + rsInfo
  where (lenCodeLen, rsInfo) = informationParts rs

informationParts :: Rules -> (Int, Double)
informationParts rs = (lenCodeLen, rulesCodeInfo)
  where
    len = V.length rs
    lenCodeLen = eliasCodeLen len
    rulesCodeInfo = log2e * 2 * ( iLogFactorial (256 + len)
                                  - iLogFactorial (256 :: Int) )

-- | The forward difference between the information of the rule set
-- after adding a new rule relative to the information of the rule set
-- now. @fwdDeltaInfo rs@ approximately computes @information (snd $
-- push (s0,s1) rs) - information rs@
infoDelta :: Rules -> Double
infoDelta = infoDelta' . numSymbols

-- | Difference in information, given `m` the number of symbols (>= 256)
infoDelta' :: Int -> Double
infoDelta' m = fromIntegral lenDeltaInfo + rulesDeltaInfo
  where (lenDeltaInfo, rulesDeltaInfo) = infoDeltaParts m

-- | Difference in information by field, given `m` the number of symbols
-- (>= 256)
infoDeltaParts :: Int -> (Int, Double)
infoDeltaParts m = (lenDeltaInfo, rulesDeltaInfo)
  where len = m - 256
        lenDeltaInfo = eliasCodeLen (len + 1) - eliasCodeLen len
        rulesDeltaInfo = log2e * 2 * log (fromIntegral m)

-- -- | The exact length of the code (in bits) of the serialization of the
-- -- rule set (exact but not very efficient)
-- codeLen :: Rules -> Int
-- codeLen rs = lenCodeLen + rulesCodeLen
--   where
--     len = V.length rs
--     lenCode = Elias.encodeDelta $ fromIntegral len
--     lenCodeLen = BV.length lenCode
--     rulesCodeLen = Var.codeLen1 $ product $
--                    (\a -> a*a) <$> take len [256..]
