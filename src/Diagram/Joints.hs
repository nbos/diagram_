{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections, BangPatterns, LambdaCase, TypeApplications #-}
module Diagram.Joints (module Diagram.Joints) where

import Control.Monad
import Control.Monad.Primitive (PrimMonad(PrimState))

import qualified Data.List as L
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IM
import Data.IntSet (IntSet)
import qualified Data.IntSet as IS
import qualified Data.Set as Set

import qualified Data.Vector.Strict as B
import qualified Data.Vector.Unboxed as U
import Data.Vector.Unboxed.Mutable (MVector)
import qualified Data.Vector.Generic.Mutable as MV

import Streaming
import qualified Streaming.Prelude as S

import Diagram.Rules (Sym)
import Diagram.Doubly (Index)
import qualified Diagram.Doubly as D
import qualified Diagram.Model as Mdl
import Diagram.Information
import Diagram.Util

type Doubly s = D.Doubly MVector s Sym

type Joints = Map (Sym,Sym) (Int, IntSet)
type JointsByLoss = IntMap -- k01 :: Int ->
                    ( Double -- ( sLossMinBound :: Double
                    , Map Double -- , sLoss :: Double ->
                          (Map (Sym,Sym) IntSet) ) -- (s0,s1) -> is )

-- | Construction using the indices of the doubly-linked list
fromList :: PrimMonad m => Doubly (PrimState m) -> m Joints
fromList = fmap fst
           . fromList_ M.empty
           . D.streamWithKey

fromList_ :: Monad m => Joints -> Stream (Of (Index,Sym)) m r -> m (Joints, r)
fromList_ m0 iss0 = (S.next iss0 >>=) $ \case
  Left r -> return (m0, r)
  Right ((i0,s0),iss0') -> go i0 s0 m0 iss0'
  where
    go i0 s0 !m iss = (S.next iss >>=) $ \case
      Left r -> return (m,r) -- end
      Right ((i1,s1),ss') -> (S.next ss' >>=) $ \case
        Left r -> return (m', r) -- last joint
        Right (is2@(_,s2),ss'') -> f m' $ S.yield is2 >> ss''
          where f | s0 == s1 && s1 == s2 = fromList_ -- even
                  | otherwise            = go i1 s1     -- odd
        where m' = insert' m (s0,s1) i0

-- | Given the vector of symbol counts (priors), index the joints by
-- their counts (k01) first and loss (sLoss) second.
byLoss :: PrimMonad m => U.MVector (PrimState m) Int -> Joints -> m JointsByLoss
byLoss ks jts = do
  im <- IM.fromListWith (M.unionWith $ M.unionWith err) <$>
        mapM mkEntry (M.toList jts)
  return $ IM.mapWithKey (\k01 e -> (sLossMinBound k01, e)) im
  where
    err = error "Joints.byLoss: collision"
    mkEntry ((s0,s1),(k01,is))
      | s0 == s1 = do
          k0 <- MV.read ks s0
          return (k01, M.singleton (Mdl.sLoss1 k01 k0) $
                       M.singleton (s0,s1) is)
      | otherwise = do
          k0 <- MV.read ks s0
          k1 <- MV.read ks s1
          return (k01, M.singleton (Mdl.sLoss2 k01 k0 k1) $
                       M.singleton (s0,s1) is)

-- | Given the number of symbols and length of the string, return the
-- joints that have the minimal loss
findMin :: Int -> Int -> JointsByLoss -> (Double, Map (Sym,Sym) IntSet)
findMin m n im = case IM.toDescList im of
  [] -> error "Jonints.findMin: empty set of joints"
  (k01,(_,sLossMap)):rest -> go (loss,jts) rest
    where
      (sLoss,jts) = M.findMin sLossMap
      nLoss = fromIntegral $ Mdl.nLoss n k01
      kLoss = Mdl.kLoss m n k01
      loss = rLoss + sLoss + nLoss + kLoss
  where
    err = error "Joints.findMin: collision"
    rLoss = Mdl.rLoss m
    go e [] = e
    go e@(bestLoss,bestJts) ((k01,(sMinBound,sLossMap)):rest)
      | lossMinBound > bestLoss = e -- end
      | otherwise = case compare loss bestLoss of
          EQ -> go (loss, M.unionWith err bestJts jts) rest -- append
          LT -> go (loss, jts) rest            -- replace
          GT -> go e rest                      -- continue
      where
        nLoss = fromIntegral $ Mdl.nLoss n k01
        kLoss = Mdl.kLoss m n k01
        rnkLoss = rLoss + nLoss + kLoss
        lossMinBound = rnkLoss + sMinBound
        (sLoss,jts) = M.findMin sLossMap
        loss = rnkLoss + sLoss

sLossMinBound :: Int -> Double
sLossMinBound = iLogFactorial -- == (\k -> sLoss2 k k k)

insert' :: Joints -> (Sym,Sym) -> Index -> Joints
insert' jts s0s1 i = M.insertWith f s0s1 (1, IS.singleton i) jts
  where f _ (n,is) = (n + 1, IS.insert i is)

-- | The union of two sets of counts + indices
union' :: Joints -> Joints -> Joints
union' = M.mergeWithKey (const f) id id
  where f (a,s) (b,t) = nothingIf ((== 0) . fst) (a + b, IS.union s t)

-- | Subtrack the counts + indices in the second map from the first map
difference' :: Joints -> Joints -> Joints
difference' = M.mergeWithKey (const f) id id
  where f (a,s) (b,t) = nothingIf ((== 0) . fst) (a - b, IS.difference s t)

type Boxed = B.MVector
-- | Given a construction rule `(s0,s1) ==> s01`, a list and a stream of
-- the indices of the construction sites, compute the changes
-- (added,subtracted) to apply to candidates\/joints counts\/locations
-- were the constructions to take place assuming that the construction
-- substitutes the left (s0) part of the joint and the right part (s1)
-- gets freed.
delta :: forall m r. PrimMonad m => (Sym,Sym) -> Sym ->
         Doubly (PrimState m) -> Stream (Of Index) m r -> m ((Joints, Joints), r)
delta _ _ (D.Doubly Nothing _ _ _ _) is0 = ((M.empty, M.empty), ) <$> S.effects is0
delta (s0,s1) s01 ss@(D.Doubly (Just ihead) _ _ _ _) is0 = do
  s0s1ref <- newPrimRef      @Boxed     IS.empty -- (s0,s1) (-) (redundant (n01))
  s1s0ref <- newPrimRef      @Boxed     IS.empty -- (s1,s0) (-)
  prevvec <- MV.replicate @_ @Boxed s01 IS.empty -- (i,s01) (-/+)
  nextvec <- MV.replicate @_ @Boxed s01 IS.empty -- (s1,i)  (-)
  nxtvec' <- MV.replicate @_ @Boxed s01 IS.empty -- (s01,i) (+)
  s0s0ref <- newPrimRef      @Boxed     IS.empty -- (s0,s0) (prev correction)
  s1s1ref <- newPrimRef      @Boxed     IS.empty -- (s1,s1) (+) (parity switch)
  autoref <- newPrimRef      @Boxed     IS.empty -- (s01,s01) (+)

  -- <loop>
  r <- case () of
    _ -> go is0 where
      go :: Stream (Of Index) m r -> m r
      go is = (S.next is >>=) $ \case
        Left r -> return r -- end
        Right (i0,is') -> do
          iprev <- prevOf i0
          prev <- readSym iprev

          -- skip sites that immediately follow a site (operate on chunks)
          ipprev <- prevOf iprev
          pprev <- readSym ipprev
          let preceededByConstr = (pprev, prev) == (s0, s1)
                                  && i0 /= ihead
                                  && iprev /= ihead
          if preceededByConstr then go is' else do

            -- prev
            unless (i0 == ihead) $ do
              MV.modify prevvec (IS.insert iprev) prev
              when (prev == s0) $ do -- assert (s0 /= s1)
                n0 <- (+1) <$> S.length_ ( S.break (/= s0) $
                                           D.revStreamFrom ss iprev )
                when (odd n0) $ -- correct
                  modifyPrimRef s0s0ref $ IS.insert iprev

            -- s0s1's
            n <- S.length_ $ S.span (== (s0,s1)) $ sChunks2 $ D.streamFrom ss i0
            i0i1s <- S.toList_ $ S.splitAt n $ sChunks2 $ D.streamKeysFrom ss i0
            modifyPrimRef s0s1ref $ insertList $ fst <$> i0i1s
            unless (s0 == s1) $
              modifyPrimRef s1s0ref $ insertList $ init $ snd <$> i0i1s
            modifyPrimRef autoref $ insertList $ fst . fst <$> lChunks2 i0i1s

            -- next
            let (i0',i1') = last i0i1s
            inext <- nextOf i1' -- ((i0',i1') ~> i0') -> inext
            unless (inext == ihead) $ do
              next <- readSym inext
              MV.modify nxtvec' (IS.insert i0') next -- (s01,next) (+)
              if next /= s1 then MV.modify nextvec (IS.insert i1') next -- (s1,next) (-)
                else if s0 == s1 then return () -- there was no (s1,next) joint
                else do -- switch parity
                n1 <- S.length_ $ S.break (/= s1) $ D.streamFrom ss i1'
                i1s <- S.toList_ $ S.take n1 $ D.streamKeysFrom ss i1'
                let evens = fst <$> lChunks2 i1s
                    odds = fst <$> lChunks2 (tail i1s)
                forM_ evens $ \i -> MV.modify nextvec (IS.insert i) s1
                forM_ odds $ modifyPrimRef s1s1ref . IS.insert

            go is' -- continue
  -- </loop>

  amref <- newPrimRef @Boxed M.empty
  rmref <- newPrimRef @Boxed M.empty

  -- read --
  readPrimRef s0s1ref >>= minsert rmref (s0,s1) -- (-)
  readPrimRef s1s0ref >>= minsert rmref (s1,s0) -- (-)

  MV.iforM_ prevvec $ minsert amref . (,s01) -- (+)
  s0s0is <- readPrimRef s0s0ref
  MV.modify prevvec (IS.\\ s0s0is) s0 -- correct prev[s0]
  MV.iforM_ prevvec $ minsert rmref . (,s0) -- (-)

  MV.iforM_ nextvec $ minsert rmref . (s1,)  -- (-)
  MV.iforM_ nxtvec' $ minsert amref . (s01,) -- (+)

  readPrimRef s1s1ref >>= minsert amref (s1,s1)   -- (+)
  readPrimRef autoref >>= minsert amref (s01,s01) -- (+)

  -- end --
  am <- toFst IS.size <<$>> readPrimRef amref
  rm <- toFst IS.size <<$>> readPrimRef rmref
  return ((am,rm),r)

  where
    prevOf = D.prev ss
    nextOf = D.next ss
    readSym = D.read ss

    insertList :: [Index] -> IntSet -> IntSet
    insertList = flip $ L.foldl' $ flip IS.insert

    minsert :: Boxed (PrimState m) (Map (Sym,Sym) IntSet) ->
               (Sym,Sym) -> IntSet -> m ()
    minsert m key is = unless (IS.null is) $ modifyPrimRef m $
                       M.insertWith (const $ IS.union is) key is

    -- pair consecutive items (non-overlapping) of a list
    lChunks2 :: [a] -> [(a,a)]
    lChunks2 (a0:a1:as) = (a0,a1):lChunks2 as
    lChunks2 _ = []

    -- pair consecutive items (non-overlapping) of a stream
    sChunks2 :: Stream (Of a) m r' -> Stream (Of (a,a)) m r'
    sChunks2 str = (lift (S.next str) >>=) $ \case
      Left r -> return r
      Right (a,str') -> (lift (S.next str') >>=) $ \case
        Left r -> return r
        Right (a',str'') -> S.yield (a,a') >> sChunks2 str''

    newPrimRef :: MV.MVector v a => a -> m (v (PrimState m) a)
    newPrimRef = MV.replicate 1
    modifyPrimRef :: MV.MVector v a => v (PrimState m) a -> (a -> a) -> m ()
    modifyPrimRef v f = MV.unsafeModify v f 0
    readPrimRef :: MV.MVector v a => v (PrimState m) a -> m a
    readPrimRef = flip MV.unsafeRead 0

-- | Re-compute the joint counts + locations to check the validity of a
-- given joints map. Throws an error if they differ.
validate :: PrimMonad m => Joints -> Doubly (PrimState m) -> a -> m a
validate cdts ss a = do
  cdtsRef <- fromList ss
  when (cdts /= cdtsRef) $
    let cdtsSet = Set.fromList $ M.toList cdts
        refSet = Set.fromList $ M.toList cdtsRef
    in error $ "Joints.validate:\n"
       ++ "should include: " ++ show (refSet Set.\\ cdtsSet) ++ "\n"
       ++ "not:            " ++ show (cdtsSet Set.\\ refSet)
  return a


---------------
-- GRAVEYARD --
---------------

countJoints :: [Int] -> Map (Sym,Sym) Int
countJoints [] = M.empty
countJoints (s0:ss) = countJoints_ M.empty s0 ss

-- | Count the joints in a list given the map of counts and the previous
-- symbol
countJoints_ :: Map (Sym,Sym) Int -> Sym -> [Sym] -> Map (Sym,Sym) Int
countJoints_ !m _ [] = m
countJoints_ !m s0 [s1] = M.insertWith (+) (s0,s1) 1 m
countJoints_ !m s0 (s1:s2:ss)
  | s0 == s1 && s1 == s2 = countJoints_ m' s2 ss
  | otherwise = countJoints_ m' s1 (s2:ss)
  where m' = M.insertWith (+) (s0,s1) 1 m

countJointsM :: Monad m => Stream (Of Int) m r -> m (Map (Sym,Sym) Int, r)
countJointsM = countJointsM_ M.empty

countJointsM_ :: Monad m => Map (Sym,Sym) Int -> Stream (Of Int) m r ->
                            m (Map (Sym,Sym) Int, r)
countJointsM_ m0 ss0 = (S.next ss0 >>=) $ \case
  Left r -> return (m0, r)
  Right (s0,ss0') -> go m0 s0 ss0'
  where
    go !m s0 ss = (S.next ss >>=) $ \case
      Left r -> return (m,r) -- end
      Right (s1,ss') -> (S.next ss' >>=) $ \case
        Left r -> return (m', r) -- last joint
        Right (s2,ss'') | s0 == s1 && s1 == s2 ->
                            countJointsM_ m' $ S.yield s2 >> ss'' -- even
                        | otherwise -> go m' s1 $ S.yield s2 >> ss'' -- odd
        where m' = M.insertWith (+) (s0,s1) 1 m

-- | Return a map of the differences of counts of affected joints upon
-- introduction of the given rule and the modified (constructed/updated)
-- symbol string. Naive because it reads the whole string for matches of
-- the introduced rule. Use @recountM@ if you know the indices of the
-- construction sites.
naiveRecountM :: forall m r. PrimMonad m =>
                 Doubly (PrimState m) -> (Sym,Sym) -> Int ->
                 Stream (Of Int) m r -> m (Map (Int, Int) Int, r)
naiveRecountM (D.Doubly Nothing _ _ _ _) _ _ is0 = (M.empty, ) <$> S.effects is0
naiveRecountM ss@(D.Doubly (Just i0) _ _ _ _) (s0,s1) s01 is0 = do
  s0s1ref <- newPrimRef      @U.MVector     0 -- (s0,s1) (-) (redundant)
  s1s0ref <- newPrimRef      @U.MVector     0 -- (s1,s0) (-)
  prevvec <- MV.replicate @_ @U.MVector s01 0 -- (i,s01) (-/+)
  nextvec <- MV.replicate @_ @U.MVector s01 0 -- (s01,i) (-/+)
  s0s0ref <- newPrimRef      @U.MVector     0 -- (s0,s0) (+) (prev[s0] correction)
  s1s1ref <- newPrimRef      @U.MVector     0 -- (s1,s1) (+) (next[s1] correction)
  autoref <- newPrimRef      @U.MVector     0 -- (s01,s01) (+)

  -- <loop>
  r <- case () of
    _ -> go is0 where
      go :: Stream (Of Index) m r -> m r
      go is = (S.next is >>=) $ \case
        Left r -> return r -- end
        Right (i,is') -> do
          -- prev
          unless (i == i0) $ do
            iprev <- D.prev ss i
            prev <- D.read ss iprev
            MV.modify prevvec (+1) prev
            when (prev == s0) $ do -- assert (s0 /= s1)
              n0 <- (+1) <$> S.length_ ( S.break (/= s0) $
                                         D.revStreamFrom ss iprev )
              when (odd n0) $ modifyPrimRef s0s0ref (+1) -- correct

          -- s0s1's
          n <- S.length_ $ S.break (/= s01) $ D.streamFrom ss i
          modifyPrimRef s0s1ref (+n)
          when (s0 /= s1) $ modifyPrimRef s1s0ref (+(n-1))
          modifyPrimRef autoref (+(n `div` 2))

          -- next
          (S.next (S.drop (n-1) $ S.yield i >> is') >>=) $ \case
            Left r -> return r -- impossible?
            Right (i',is'') -> do
              inext <- D.next ss i'
              unless (inext == i0) $ do
                next <- D.read ss inext
                MV.modify nextvec (+1) next
                when (next == s1) $ do -- check parity
                  n1 <- if s0 == s1 then return 3
                        else do (+1) <$> S.length_ ( S.break (/= s1) $
                                                     D.streamFrom ss inext)
                  when (odd n1) $ modifyPrimRef s1s1ref (+1) -- -1+1 == 0
              go is'' -- continue
  -- </loop>

  resref <- newPrimRef @B.MVector M.empty
  let rinsert k n = when (n /= 0) $
                    modifyPrimRef resref $
                    M.insertWith (+) k n
  -- read --
  rinsert (s0,s1) . (0-) =<< readPrimRef s0s1ref -- (-)
  rinsert (s1,s0) . (0-) =<< readPrimRef s1s0ref -- (-)
  MV.iforM_ prevvec $ \prev n -> rinsert (prev,s0) (-n)  -- (-)
                                 >> rinsert (prev,s01) n -- (+)
  MV.iforM_ nextvec $ \next n -> rinsert (s1,next) (-n)  -- (-)
                                 >> rinsert (s01,next) n -- (+)
  rinsert (s0,s0) =<< readPrimRef s0s0ref   -- (+)
  rinsert (s1,s1) =<< readPrimRef s1s1ref   -- (+)
  rinsert (s01,s01) =<< readPrimRef autoref -- (+)

  -- end --
  (,r) <$> readPrimRef resref

  where
    newPrimRef :: MV.MVector v a => a -> m (v (PrimState m) a)
    newPrimRef = MV.replicate 1
    modifyPrimRef :: MV.MVector v a => v (PrimState m) a -> (a -> a) -> m ()
    modifyPrimRef v f = MV.modify v f 0 -- TODO: unsafe
    readPrimRef :: MV.MVector v a => v (PrimState m) a -> m a
    readPrimRef = flip MV.read 0 -- TODO: unsafe
