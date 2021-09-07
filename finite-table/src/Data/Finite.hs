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
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Provides a class of types isomorphic to some statically-known @'Fin' n@.
--
-- This comes with Generics-based generated instances, and can be used to
-- generate instances of 'Enum' and 'Bounded' (for which the stock deriving
-- only supports sum types with no fields).
--
-- Since this is all still represented by 'Int' internally, things will start
-- raising 'error's if your type has more values than can fit in positive
-- 'Int's.  It's not recommended to use this on large types, and there's not
-- much reason to want to anyway, as its main uses are to derive 'Enum' (which
-- is also based on 'Int') and to make the type compatible with
-- 'Data.Finite.Table.Table' (which would be impractically large for a key type
-- with too many values to represent as 'Int').
--
-- The most common way to get a 'Finite' instance for a type is to tack on a
-- @deriving Finite via 'Wrapped' 'Generic' MyType@ clause, which results in an
-- automatically-generated instance based on the type's ADT structure.
--
-- This also provides instances @'Enum' (Wrapped Finite a)@ and
-- @'Bounded' (Wrapped Finite a)@, so some types that would otherwise not be
-- compatible with derived 'Enum' instances can get them by adding a
-- @deriving (Enum, Bounded) via Wrapped Finite MyType@ clause.

module Data.Finite
         ( -- * Finite Enumerations
           Finite(..), cardinality, enumerate, asFin
           -- * Implementation Details
         , SC, GFinite(..), GCardinality
         ) where

import Data.Functor.Identity (Identity)
import Data.Int (Int8, Int16)
import Data.Proxy (Proxy(..))
import Data.Semigroup (WrappedMonoid, Min, Max, First, Last)
import Data.Void (Void)
import Data.Word (Word8, Word16)
import GHC.Generics
         ( Generic(..), V1, U1(..), M1(..), K1(..), (:+:)(..), (:*:)(..)
         )
import GHC.TypeNats (type (+), type (*), type (<=), KnownNat, Nat, natVal)

import Control.Lens (Iso', iso)
import Data.SInt (SInt, sintVal, addSInt, mulSInt, staticSIntVal, reifySInt)

import Data.Fin.Int.Explicit
         ( enumFin, concatFin, splitFin, crossFin, divModFin, minFin, maxFin
         , fin
         )
import Data.Fin.Int (Fin, finToInt, unsafeFin)
import qualified Data.Vec.Short as V
import Data.Wrapped (Wrapped(..))

-- | A typeclass of finite enumerable types.
--
-- These allow constructing 'Data.Functor.Rep.Representable' Functors using a
-- simple 'Data.Vec.Short.Vec' as the underlying storage, with constant-time
-- lookup and efficient traversals.
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
  cardinality' :: SC a (Cardinality a)

  toFin :: a -> Fin (Cardinality a)
  fromFin :: Fin (Cardinality a) -> a

-- | A wrapper type around @'Cardinality' a@ to support DerivingVia on GHC 8.6.
--
-- Instance methods that don't mention the instance head outside of type
-- families / aliases don't work with DerivingVia on GHC 8.6 because it uses
-- type signatures rather than TypeApplications to choose the instance to call
-- into.
newtype SC a n = SC { getSC :: SInt n }

-- | A witness that the cardinality of @a@ is known at runtime.
cardinality :: forall a. Finite a => SInt (Cardinality a)
cardinality = getSC (cardinality' @a)

-- | Generate a list containing every value of @a@.
enumerate :: forall a. Finite a => [a]
enumerate = fromFin <$> enumFin (cardinality @a)

-- | Implement 'toFin' by 'fromEnum'.
--
-- This should only be used for types with 'fromEnum' range @0..Cardinality a@;
-- this is notably not the case for signed integer types, which have negative
-- 'fromEnum' values.
toFinEnum :: Enum a => SInt (Cardinality a) -> a -> Fin (Cardinality a)
toFinEnum sn = fin sn . fromEnum

-- | Implement 'fromFin' by 'toEnum'.
--
-- The same restrictions apply as for 'toFinEnum'.
fromFinEnum :: Enum a => Fin (Cardinality a) -> a
fromFinEnum = toEnum . finToInt

instance Finite Char where
  type Cardinality Char = 1114112 -- According to 'minBound' and 'maxBound'
  cardinality' = SC staticSIntVal
  toFin = toFinEnum staticSIntVal
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
  cardinality' = SC staticSIntVal
  toFin = toFinExcessK @128
  fromFin = fromFinExcessK @128

instance Finite Int16 where
  type Cardinality Int16 = 65536
  cardinality' = SC staticSIntVal
  toFin = toFinExcessK @32768
  fromFin = fromFinExcessK @32768

instance Finite Word8 where
  type Cardinality Word8 = 256
  cardinality' = SC staticSIntVal
  toFin = unsafeFin . id @Int . fromIntegral
  fromFin = fromIntegral . finToInt

instance Finite Word16 where
  type Cardinality Word16 = 65536
  cardinality' = SC staticSIntVal
  toFin = unsafeFin . id @Int . fromIntegral
  fromFin = fromIntegral . finToInt

instance KnownNat n => Finite (Fin n) where
  type Cardinality (Fin n) = n
  cardinality' = SC sintVal
  toFin = id
  fromFin = id

-- Aesthetics: make more derived instances fit on one line.
type G = Wrapped Generic

deriving via G () instance Finite ()
deriving via G Bool instance Finite Bool
deriving via G Ordering instance Finite Ordering
deriving via G Void instance Finite Void
deriving via G (Identity a) instance Finite a => Finite (Identity a)
deriving via G (WrappedMonoid a) instance Finite a => Finite (WrappedMonoid a)
deriving via G (Last a) instance Finite a => Finite (Last a)
deriving via G (First a) instance Finite a => Finite (First a)
deriving via G (Max a) instance Finite a => Finite (Max a)
deriving via G (Min a) instance Finite a => Finite (Min a)
deriving via G (Maybe a) instance Finite a => Finite (Maybe a)
deriving via G (Either a b) instance (Finite a, Finite b) => Finite (Either a b)

deriving via G (a, b) instance (Finite a, Finite b) => Finite (a, b)
deriving via G (a, b, c)
  instance (Finite a, Finite b, Finite c) => Finite (a, b, c)

deriving via G (a, b, c, d)
  instance (Finite a, Finite b, Finite c, Finite d) => Finite (a, b, c, d)
deriving via G (a, b, c, d, e)
  instance (Finite a, Finite b, Finite c, Finite d, Finite e)
        => Finite (a, b, c, d, e)

instance (Generic a, GFinite (Rep a)) => Finite (Wrapped Generic a) where
  type Cardinality (Wrapped Generic a) = GCardinality (Rep a)
  cardinality' = SC $ gcardinality @(Rep a)
  toFin = gtoFin . from . unWrapped
  fromFin = Wrapped . to . gfromFin

-- | The derived cardinality of a generic representation type.
type family GCardinality a where
  GCardinality V1         = 0
  GCardinality U1         = 1
  GCardinality (K1 i a)   = Cardinality a
  GCardinality (M1 i c f) = GCardinality f
  GCardinality (f :+: g)  = GCardinality f + GCardinality g
  GCardinality (f :*: g)  = GCardinality f * GCardinality g

-- | The derived 'Finite' implementation of a generic representation type.
class GFinite a where
  gcardinality :: SInt (GCardinality a)
  gtoFin :: a p -> Fin (GCardinality a)
  gfromFin :: Fin (GCardinality a) -> a p

instance GFinite V1 where
  gcardinality = staticSIntVal
  gtoFin x = case x of {}
  gfromFin x = V.nil V.! x

instance GFinite U1 where
  gcardinality = staticSIntVal
  gtoFin U1 = minFin
  gfromFin !_ = U1

instance Finite a => GFinite (K1 i a) where
  gcardinality = cardinality @a
  gtoFin = toFin . unK1
  gfromFin = K1 . fromFin

instance GFinite f => GFinite (M1 i c f) where
  gcardinality = gcardinality @f
  gtoFin = gtoFin . unM1
  gfromFin = M1 . gfromFin

instance (GFinite f, GFinite g) => GFinite (f :+: g) where
  gcardinality = gcardinality @f `addSInt` gcardinality @g
  gtoFin x = concatFin (gcardinality @f) $ case x of
    L1 f -> Left $ gtoFin f
    R1 g -> Right $ gtoFin g
  gfromFin =
    either (L1 . gfromFin) (R1 . gfromFin) . splitFin (gcardinality @f)
  {-# INLINE gtoFin #-}
  {-# INLINE gfromFin #-}

instance (GFinite f, GFinite g) => GFinite (f :*: g) where
  gcardinality = gcardinality @f `mulSInt` gcardinality @g
  gtoFin (f :*: g) = crossFin (gcardinality @g) (gtoFin f) (gtoFin g)
  gfromFin x =
    let (f, g) = divModFin (gcardinality @g) x
    in  gfromFin f :*: gfromFin g
  {-# INLINE gtoFin #-}
  {-# INLINE gfromFin #-}

-- | An 'Control.Lens.Iso' between @a@ and the corresponding 'Fin' type.
asFin :: Finite a => Iso' a (Fin (Cardinality a))
asFin = iso toFin fromFin

instance Finite a => Enum (Wrapped Finite a) where
  toEnum = Wrapped . fromFin . fin (cardinality @a)
  fromEnum = finToInt . toFin . unWrapped
  enumFrom = reifySInt (cardinality @a) $
    fmap (Wrapped . fromFin) . enumFrom . toFin . unWrapped
  enumFromThen (Wrapped x) = reifySInt (cardinality @a) $
    fmap (Wrapped . fromFin) . enumFromThen (toFin x) . toFin . unWrapped
  enumFromTo (Wrapped x) = reifySInt (cardinality @a) $
    fmap (Wrapped . fromFin) . enumFromTo (toFin x) . toFin . unWrapped
  enumFromThenTo (Wrapped x) (Wrapped y) = reifySInt (cardinality @a) $
    fmap (Wrapped . fromFin) . enumFromThenTo (toFin x) (toFin y) .
    toFin . unWrapped

instance (Finite a, 1 <= Cardinality a) => Bounded (Wrapped Finite a) where
  minBound = Wrapped $ fromFin minFin
  maxBound = Wrapped $ fromFin (maxFin (cardinality @a))
