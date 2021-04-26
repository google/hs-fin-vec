-- Copyright 2021 Google LLC
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

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}

module Main where

import Data.Int (Int8)
import Data.Word (Word8)
import GHC.Generics (Generic)

import Data.Wrapped (Wrapped(..))
import Test.Framework (defaultMain, testGroup)
import Test.Framework.Providers.QuickCheck2 (testProperty)
import Test.QuickCheck ((===), Property, forAll, arbitraryBoundedEnum)

import Data.Fin.Int (Fin)
import Data.Finite

data EnumType = Cyan | Magenta | Yellow | Key
  deriving (Eq, Show, Generic)
  deriving Finite via Wrapped Generic EnumType
  deriving (Bounded, Enum) via Wrapped Finite EnumType

data ProductType = ProductType EnumType EnumType
  deriving (Eq, Show, Generic)
  deriving Finite via Wrapped Generic ProductType
  deriving (Bounded, Enum) via Wrapped Finite ProductType

data SumType = SumL EnumType | SumR EnumType
  deriving (Eq, Show, Generic)
  deriving Finite via Wrapped Generic SumType
  deriving (Bounded, Enum) via Wrapped Finite SumType

testToFrom :: forall a. (Eq a, Show a, Finite a, Bounded a, Enum a) => Property
testToFrom = forAll arbitraryBoundedEnum $ \x -> x === fromFin (toFin @a x)

testFromTo :: forall a. Finite a => Fin (Cardinality a) -> Property
testFromTo x = x === toFin (fromFin @a x)

main :: IO ()
main = defaultMain
  [ testGroup "toFin . fromFin" $
      [ testProperty "EnumType"    $ testFromTo @EnumType
      , testProperty "ProductType" $ testFromTo @ProductType
      , testProperty "SumType"     $ testFromTo @SumType
      , testProperty "Int8"        $ testFromTo @Int8
      , testProperty "Word8"       $ testFromTo @Word8
      , testProperty "()"          $ testFromTo @()
      ]

  , testGroup "fromFin . toFin" $
      [ testProperty "EnumType"    $ testToFrom @EnumType
      , testProperty "ProductType" $ testToFrom @ProductType
      , testProperty "SumType"     $ testToFrom @SumType
      , testProperty "Int8"        $ testToFrom @Int8
      , testProperty "Word8"       $ testToFrom @Word8
      , testProperty "()"          $ testToFrom @()
      ]
  ]
