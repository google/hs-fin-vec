-- Copyright 2019-2021 Google LLC
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
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Provides a class of types isomorphic to some statically-known @'Fin' n@.

module Data.Finite
         ( -- * Finite Enumerations
           Finite(..), enumerate, asFin
         ) where

import Data.Bifunctor (bimap)
import Data.Coerce (coerce)
import Data.Functor.Identity (Identity)
import Data.Int (Int8, Int16)
import Data.Proxy (Proxy(..))
import Data.Semigroup (WrappedMonoid, Min, Max, First, Last)
import Data.Void (Void, absurd)
import Data.Word (Word8, Word16)
import GHC.TypeNats (type (+), type (*), KnownNat, Nat, natVal)

import Control.Lens (Iso', iso)
import Data.Constraint (withDict, (\\))
import Data.Constraint.Nat
         ( plusMonotone1, plusMonotone2
         , zeroLe
         )
import Data.SInt (SInt, sintVal, addSInt, mulSInt)

import Data.Fin.Int.Explicit
         ( maxFin, enumFin, shiftFin, tryUnshiftFin
         , embed, splitFin, crossFin, divModFin
         )
import Data.Fin.Int (Fin, fin, finToInt, unsafeFin)

-- | A typeclass of finite enumerable types.
--
-- These allow constructing 'Representable' Functors using a simple 'Vec' as
-- the underlying storage, with constant-time lookup and efficient traversals.
--
-- Note that since 'Fin' is (currently) represented by 'Int', any type with
-- more values than 'Int' can't have an instance.  This means we can't have
-- instances for 32- and 64-bit arithmetic types, since 'Int' is only required
-- to have 30 bits of precision.
--
-- Annoyingly, we also can't have an instance for 'Int' and 'Word', because
-- 'Fin' wastes one bit of the 'Int' by forbidding negative values.  The
-- cardinality of 'Int' and 'Word' would need to be twice as large as we can
-- actually represent in a 'Fin'.  Another obstacle is that their cardinality
-- varies between implementations and architectures; it's possible to work
-- around this by making their Cardinality an irreducible type family
-- application, and using 'Data.SInt.SI#' to plug in a value at runtime, but
-- this makes the 'Fin's related to 'Int' and 'Word' annoying to work with,
-- since their bound is only known at runtime.
--
-- Fortunately, those instances are unlikely to be important, since a table of
-- 2^32 elements is moderately impractical (32GiB of pointers alone), and a
-- table of 2^64 elements is unrepresentable in current computer architectures.
--
-- 'toFin' and 'fromFin' shall be total functions and shall be the two sides of
-- an isomorphism.
class Finite a where
  type Cardinality a :: Nat
  -- | A witness that the cardinality is known at runtime.
  --
  -- This isn't part of the class context because we can only perform
  -- arithmetic on 'KnownNat' instances in expression context; that is, we
  -- can't convince GHC that an instance with
  -- @type Cardinality (Maybe a) = Cardinality a + 1@ is valid if the
  -- 'KnownNat' is in the class context.  Instead, we use 'SInt' to allow
  -- computing the cardinality at runtime.
  cardinality :: SInt (Cardinality a)
  default cardinality
    :: KnownNat (Cardinality a)
    => SInt (Cardinality a)
  cardinality = sintVal

  toFin :: a -> Fin (Cardinality a)
  fromFin :: Fin (Cardinality a) -> a

-- | Generate a list containing every value of @a@.
enumerate :: forall a. Finite a => [a]
enumerate = fromFin <$> enumFin (cardinality @a)

-- | Implement 'toFin' by 'fromEnum'.
--
-- This should only be used for types with 'fromEnum' range @0..Cardinality a@;
-- this is notably not the case for signed integer types, which have negative
-- 'fromEnum' values.
toFinEnum :: (KnownNat (Cardinality a), Enum a) => a -> Fin (Cardinality a)
toFinEnum = fin . fromEnum

-- | Implement 'fromFin' by 'toEnum'.
--
-- The same restrictions apply as for 'toFinEnum'.
fromFinEnum :: Enum a => Fin (Cardinality a) -> a
fromFinEnum = toEnum . finToInt

instance Finite () where
  type Cardinality () = 1
  toFin _ = fin 0
  fromFin _ = ()

instance Finite Bool where
  type Cardinality Bool = 2
  toFin = toFinEnum
  fromFin = fromFinEnum

instance Finite Char where
  type Cardinality Char = 1114112 -- According to 'minBound' and 'maxBound'
  toFin = toFinEnum
  fromFin = fromFinEnum

toFinExcessK
  :: forall n a. (KnownNat n, Integral a) => a -> Fin (Cardinality a)
toFinExcessK =
  unsafeFin . (+ (fromIntegral (natVal @n Proxy) :: Int)) . fromIntegral

fromFinExcessK
  :: forall n a. (KnownNat n, Integral a) => Fin (Cardinality a) -> a
fromFinExcessK =
  subtract (fromIntegral (natVal @n Proxy)) . fromIntegral . finToInt

instance Finite Int8 where
  type Cardinality Int8 = 256
  toFin = toFinExcessK @128
  fromFin = fromFinExcessK @128

instance Finite Int16 where
  type Cardinality Int16 = 65536
  toFin = toFinExcessK @32768
  fromFin = fromFinExcessK @32768

instance Finite Word8 where
  type Cardinality Word8 = 256
  toFin = unsafeFin . id @Int . fromIntegral
  fromFin = fromIntegral . finToInt

instance Finite Word16 where
  type Cardinality Word16 = 65536
  toFin = unsafeFin . id @Int . fromIntegral
  fromFin = fromIntegral . finToInt

instance Finite Ordering where
  type Cardinality Ordering = 3
  toFin = toFinEnum
  fromFin = fromFinEnum

instance KnownNat n => Finite (Fin n) where
  type Cardinality (Fin n) = n
  toFin = id
  fromFin = id

instance Finite a => Finite (Identity a) where
  type Cardinality (Identity a) = Cardinality a
  cardinality = cardinality @a
  toFin = coerce (toFin @(Identity a))
  fromFin = coerce (fromFin @(Identity a))

instance Finite a => Finite (WrappedMonoid a) where
  type Cardinality (WrappedMonoid a) = Cardinality a
  cardinality = cardinality @a
  toFin = coerce (toFin @(WrappedMonoid a))
  fromFin = coerce (fromFin @(WrappedMonoid a))

instance Finite a => Finite (Last a) where
  type Cardinality (Last a) = Cardinality a
  cardinality = cardinality @a
  toFin = coerce (toFin @(Last a))
  fromFin = coerce (fromFin @(Last a))

instance Finite a => Finite (First a) where
  type Cardinality (First a) = Cardinality a
  cardinality = cardinality @a
  toFin = coerce (toFin @(First a))
  fromFin = coerce (fromFin @(First a))

instance Finite a => Finite (Max a) where
  type Cardinality (Max a) = Cardinality a
  cardinality = cardinality @a
  toFin = coerce (toFin @(Max a))
  fromFin = coerce (fromFin @(Max a))

instance Finite a => Finite (Min a) where
  type Cardinality (Min a) = Cardinality a
  cardinality = cardinality @a
  toFin = coerce (toFin @(Min a))
  fromFin = coerce (fromFin @(Min a))

instance Finite a => Finite (Maybe a) where
  type Cardinality (Maybe a) = 1 + Cardinality a
  cardinality = sintVal `addSInt` cardinality @a
  toFin =
    withDict (zeroLe @(Cardinality a)) $
    maybe (maxFin (cardinality @(Maybe a))) (shiftFin sintVal . toFin)
    \\ plusMonotone2 @1 @0 @(Cardinality a)
  fromFin = fmap fromFin . tryUnshiftFin sintVal (cardinality @a)

instance (Finite a, Finite b) => Finite (Either a b) where
  type Cardinality (Either a b) = Cardinality a + Cardinality b
  cardinality = cardinality @a `addSInt` cardinality @b

  toFin =
    either (embed . toFin) (shiftFin (cardinality @a). toFin)
    \\ plusMonotone2 @(Cardinality a) @0 @(Cardinality b)
    \\ plusMonotone1 @0 @(Cardinality a) @(Cardinality b)

  fromFin = bimap fromFin fromFin . splitFin (cardinality @a)

instance (Finite a, Finite b) => Finite (a, b) where
  type Cardinality (a, b) = Cardinality a * Cardinality b
  cardinality = cardinality @a `mulSInt` cardinality @b

  toFin (a, b) = crossFin (cardinality @b) (toFin a) (toFin b)

  fromFin f =
    let (fa, fb) = divModFin (cardinality @b) f
    in  (fromFin fa, fromFin fb)

instance (Finite a, Finite b, Finite c) => Finite (a, b, c) where
  type Cardinality (a, b, c) = Cardinality a * Cardinality b * Cardinality c
  cardinality = cardinality @((a, b), c)
  toFin (a, b, c) = toFin ((a, b), c)
  fromFin f = let ((a, b), c) = fromFin f in (a, b, c)

instance Finite Void where
  type Cardinality Void = 0
  toFin = absurd
  fromFin !_ = error "Unreachable: x :: Fin 0 must have been bottom."

-- | An 'Iso' between @a@ and the corresponding 'Fin' type, as per 'Finite'.
asFin :: Finite a => Iso' a (Fin (Cardinality a))
asFin = iso toFin fromFin
