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
{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import Prelude hiding ((++))

import Test.Framework (defaultMain)
import Test.Framework.Providers.QuickCheck2 (testProperty)
import Test.QuickCheck (Property, (===), counterexample)

import Data.Vec.Short ((++), Vec, split, vec2, vec3)

main :: IO ()
main = defaultMain
  [ testProperty "vec" $ readInvertsShow $
      vec2 (3 :: Int) 5
  , testProperty "vec of vec" $ readInvertsShow $
      vec3 (vec2 (2 :: Int) 4) (vec2 3 5) (vec2 4 6)
  , testProperty "append of split" $ \ (v :: Vec 8 Int) ->
      let (l, r) = split @5 v
      in  v === l ++ r
  ]
  where
    readInvertsShow :: (Eq a, Read a, Show a) => a -> Property
    readInvertsShow a =
      let astr = show a
      in counterexample astr $ a === read astr
