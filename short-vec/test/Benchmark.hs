-- Copyright 2018-2021 Google LLC
--
-- Licensed under the Apache License, Version 2.0 (the "License");
-- you may not use this file except in compliance with the License.
-- You may obtain a copy of the License at
--
--      http://www.apache.org/licenses/LICENSE-2.0
--
-- Unless required by applicable law or agreed to in writing, software
-- distributed under the License is distributed on an "AS IS" BASIS,
-- WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
-- See the License for the specific language governing permissions and
-- limitations under the License.

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module Main where

import Prelude hiding ((++))

import Control.Applicative (liftA2, liftA3)
import Control.Exception (evaluate)
import Data.Foldable (foldl', foldr', toList)
import Data.Semigroup (Sum(..))

import Control.DeepSeq (force)
import Data.Vec.Short
import Data.Fin.Int (fin, finToInt, modNegate)
import Data.Functor.WithIndex (FunctorWithIndex(..))

import qualified Gauge as G

theAnswer :: Vec 64 Int
theAnswer = pure 42

benchForce_DeepSeq
  , benchPure, benchRot
  , benchMap, benchMapId, benchMapCoerce, benchMap2
  , benchSum, benchSumMap
  , benchFoldr, benchFoldr1, benchFoldr', benchFoldl, benchFoldl1, benchFoldl'
  , benchAppend, benchAppendMap
  , benchTraverseIO
  , benchLiftA2
  , benchConvolve
  , benchMapWithPos
  , benchMapToList, benchMapToListMap, benchSumToListMap
  , benchEq_true, benchEq_false
  , benchTake, benchMapTake, benchDrop, benchMapDrop
  , benchSplit
  :: G.Benchmark

benchForce_DeepSeq = G.bench "force_DeepSeq" $ G.whnf force theAnswer
benchPure = G.bench "pure" $ G.whnf (pure :: Int -> Vec 64 Int) 42
benchMap = G.bench "map" $ G.whnf (map' (+2)) theAnswer
benchMapId = G.bench "mapId" $ G.whnf (fmap id) theAnswer
benchMapCoerce = G.bench "mapCoerce" $ G.whnf (fmap Sum) theAnswer
benchMap2 = G.bench "map2" $ G.whnf (map' (+2) . fmap (+2)) theAnswer
benchRot = G.bench "rot" $ G.whnf (rot (fin 7)) theAnswer
benchSum = G.bench "sum" $ G.whnf sum theAnswer
benchSumMap = G.bench "sumMap" $ G.whnf (sum . fmap (+7)) theAnswer
benchFoldr = G.bench "foldr" $ G.whnf (foldr (+) 0) theAnswer
benchFoldr1 = G.bench "foldr1" $ G.whnf (foldr1 (+)) theAnswer
benchFoldr' = G.bench "foldr'" $ G.whnf (foldr' (+) 0) theAnswer
benchFoldl = G.bench "foldl" $ G.whnf (foldl (+) 0) theAnswer
benchFoldl1 = G.bench "foldl1" $ G.whnf (foldl1 (+)) theAnswer
benchFoldl' = G.bench "foldl'" $ G.whnf (foldl' (+) 0) theAnswer
benchAppend = G.bench "append" $ G.whnf (\x -> x ++ x) theAnswer
benchAppendMap = G.bench "appendMap" $ G.whnf (\x -> x ++ fmap (+2) x) theAnswer

benchTraverseIO = G.bench "traverseIO" $
  G.whnfAppIO (traverse evaluate) theAnswer

benchLiftA2 = G.bench "liftA2" $
  G.whnf (liftA2 (+) (pure 2 :: Vec 64 Int)) theAnswer

benchConvolve = G.bench "convolve" $ G.nf
  (\x -> liftA3
    (\a b c -> a + b + c)
    (rot (fin 1) x)
    x
    (rot (modNegate (fin 1)) x))
  theAnswer

benchMapWithPos = G.bench "mapWithPos'" $
  G.whnf (imap (\i -> (+) (finToInt i))) theAnswer

benchMapToList = G.bench "mapToList" $ G.nf (map (+2) . toList) theAnswer
benchMapToListMap = G.bench "mapToListMap" $
  G.nf (map (+2) . toList . fmap (+2)) theAnswer

benchSumToListMap = G.bench "sumToListMap" $
  G.nf (sum . toList . fmap (+2)) theAnswer

benchEq_true = G.bench "eq_true" $ G.whnf (\x -> x == x) theAnswer

benchEq_false = G.bench "eq_false" $
  G.whnf (\ (x, y) -> x == y) (theAnswer, (+1) <$> theAnswer)

benchTake = G.bench "take" $ G.whnf (fst . split @50) theAnswer
benchMapTake = G.bench "mapTake" $
  G.whnf (fst . split @50 . fmap (+2)) theAnswer

benchDrop = G.bench "drop" $ G.whnf (snd . split @50) theAnswer
benchMapDrop = G.bench "mapDrop" $
  G.whnf (snd . split @50 . fmap (+2)) theAnswer

benchSplit = G.bench "split" $
  G.whnf (\x -> let (l, r) = split @50 x in l `seq` r `seq` (l, r)) theAnswer

main :: IO ()
main = G.defaultMainWith (G.defaultConfig { G.minSamples = Just 5 }) $
  [ benchForce_DeepSeq
  , benchPure
  , benchMap, benchMap2, benchMapCoerce, benchMapId
  , benchTraverseIO
  , benchLiftA2
  , benchConvolve
  , benchMapWithPos
  , benchRot
  , benchSum, benchSumMap
  , benchFoldr, benchFoldr1, benchFoldr', benchFoldl, benchFoldl1, benchFoldl'
  , benchAppend, benchAppendMap
  , benchMapToList, benchMapToListMap, benchSumToListMap
  , benchEq_true, benchEq_false
  , benchTake, benchMapTake, benchDrop, benchMapDrop
  , benchSplit
  ]
