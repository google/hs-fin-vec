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
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Provides a class of finite enumerations, and enum-indexed tables.

module Data.Finite
         ( -- * Finite Enumerations
           Finite(..), enumerate, asFin
           -- * Tables
         , Table(..), (!), ix, idTable, mkTable, lmapTable, composeTable
           -- * Function Utilities
         , memoize, traverseRep
           -- * Representable Utilities
         , tabulateA, retabulated
         ) where

import Prelude hiding ((.), id)

import Data.Coerce (coerce)
import Data.Default.Class (Default(..))
import Data.Foldable (traverse_)
import Data.Foldable.WithIndex (FoldableWithIndex(..))
import Data.Functor.Identity (Identity)
import Data.Functor.WithIndex (FunctorWithIndex(..))
import Data.Int (Int8, Int16)
import Data.Proxy (Proxy(..))
import Data.Semigroup (WrappedMonoid, Min, Max, First, Last)
import Data.Traversable.WithIndex (TraversableWithIndex(..))
import Data.Void (Void, absurd)
import Data.Word (Word8, Word16)
import Control.Category (Category(..))
import Control.DeepSeq (NFData(..))
import GHC.Generics (Generic)
import GHC.TypeNats (type (+), type (*), KnownNat, Nat, natVal)

import Control.Lens
         ( Iso, Iso', Lens', from, lens, iso, (&)
         , (.~)
         )
import qualified Control.Lens as L
import Data.Constraint (withDict, (\\))
import Data.Constraint.Nat
         ( plusMonotone1, plusMonotone2
         , zeroLe
         )
import Data.Distributive (Distributive(..))
import Data.Functor.Rep
         ( Representable(..), ifoldMapRep, imapRep, itraverseRep
         , tabulated
         )
import Data.Serialize (Serialize(..))
import Data.SNumber
         ( SNumber, KnownSNumber, snumberVal, unSNumber
         , chkAdd, chkMul, reifySNumberAsNat
         )
import Kinds.Integer (pattern Pos)

import Data.Vec.Short (Vec)
import qualified Data.Vec.Short as V
import qualified Data.Vec.Short.Lens as V (ix)
import Data.Fin.Int
         ( Fin, embed, fin, finToInt, unsafeFin, weaken, strengthen
         , crossFin, unembed, tryUnembed, divModFin, enumFin
         )

-- | A typeclass of finite enumerable types.
--
-- These allow constructing 'Representable' Functors out using a simple 'Vec'
-- as the underlying storage, with constant-time lookup and efficient
-- traversals.
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
-- application, and using 'unsafeMkSNat' to plug in a value at runtime, but
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
  -- 'KnownNat' is in the class context.  Instead, we use 'Dict' to allow
  -- computing the cardinality at runtime.
  cardinality :: SNumber Int ('Pos (Cardinality a))
  default cardinality
    :: KnownSNumber Int ('Pos (Cardinality a))
    => SNumber Int ('Pos (Cardinality a))
  cardinality = snumberVal

  toFin :: a -> Fin (Cardinality a)
  fromFin :: Fin (Cardinality a) -> a

enumerate :: forall a. Finite a => [a]
enumerate = reifySNumberAsNat (cardinality @a) (fromFin <$> enumFin)

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
  toFin _ = 0
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
  toFin = unsafeFin . id @_ @Int . fromIntegral
  fromFin = fromIntegral

instance Finite Word16 where
  type Cardinality Word16 = 65536
  toFin = unsafeFin . id @_ @Int . fromIntegral
  fromFin = fromIntegral

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
  type Cardinality (Maybe a) = Cardinality a + 1
  cardinality = cardinality @a `chkAdd` snumberVal @('Pos 1)
  toFin =
    reifySNumberAsNat (cardinality @(Maybe a)) $
    withDict (zeroLe @(Cardinality a)) $
    maybe maxBound (weaken . toFin)
    \\ plusMonotone1 @0 @(Cardinality a) @1
  fromFin = reifySNumberAsNat (cardinality @a) $ fmap fromFin . strengthen

instance (Finite a, Finite b) => Finite (Either a b) where
  type Cardinality (Either a b) = Cardinality a + Cardinality b
  cardinality = cardinality @a `chkAdd` cardinality @b

  toFin =
    reifySNumberAsNat (cardinality @a) $
    reifySNumberAsNat (cardinality @(Either a b)) $
    either
      (embed . toFin)
      ((+ fromIntegral (natVal @(Cardinality a) Proxy)) . embed . toFin)
    \\ plusMonotone2 @(Cardinality a) @0 @(Cardinality b)
    \\ plusMonotone1 @0 @(Cardinality a) @(Cardinality b)

  fromFin x =
    reifySNumberAsNat (cardinality @a) $
    reifySNumberAsNat (cardinality @b) $
    reifySNumberAsNat (cardinality @(Either a b)) $
    case tryUnembed x of
      Just xl -> Left $ fromFin xl
      Nothing -> Right $ fromFin $ unembed $
        x - fromIntegral (unSNumber (cardinality @a))

instance (Finite a, Finite b) => Finite (a, b) where
  type Cardinality (a, b) = Cardinality a * Cardinality b
  cardinality = cardinality @a `chkMul` cardinality @b

  toFin (a, b) =
    reifySNumberAsNat (cardinality @(a, b)) $
    reifySNumberAsNat (cardinality @b) $
    crossFin (toFin a) (toFin b)

  fromFin f =
    reifySNumberAsNat (cardinality @a) $
    reifySNumberAsNat (cardinality @b) $
    let (fa, fb) = divModFin f
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

asFin :: Finite a => Iso' a (Fin (Cardinality a))
asFin = iso toFin fromFin

-- | A total table indexed by @a@, containing @b@s.
newtype Table a b = Table (Vec (Cardinality a) b)
  deriving (Eq, Ord, Show, Functor, Foldable, Generic)

instance NFData a => NFData (Table k a) where
  rnf (Table vec) = rnf vec

instance (Finite k, Serialize a) => Serialize (Table k a) where
  get = reifySNumberAsNat (cardinality @k) $ sequenceA $ tabulate (const get)
  put = traverse_ put

deriving instance KnownNat (Cardinality a) => Applicative (Table a)

instance (KnownNat (Cardinality a), Default b) => Default (Table a b) where
  def = Table (pure def)

-- | 'lmap' for a constrained 'Profunctor' on 'Table'.
lmapTable :: (Finite b, Finite c) => (b -> c) -> Table c a -> Table b a
lmapTable f t = tabulate $ \x -> t `index` f x

instance Finite a => Traversable (Table a) where
  traverse f (Table vec) = Table <$> traverse f vec

instance Finite a => Distributive (Table a) where
  collect f fa =
    reifySNumberAsNat (cardinality @a) $
    let fgb = f <$> fa
    in  Table $ V.mkVec (\i -> flip index (fromFin i) <$> fgb)

instance Finite a => Representable (Table a) where
  type Rep (Table a) = a
  tabulate f = reifySNumberAsNat (cardinality @a) $ Table $ V.mkVec (f . fromFin)
  index (Table vec) i = vec V.! toFin i

instance Finite a => FunctorWithIndex a (Table a) where imap = imapRep
instance Finite a => FoldableWithIndex a (Table a) where ifoldMap = ifoldMapRep
instance Finite a => TraversableWithIndex a (Table a) where
  itraverse = itraverseRep

#if !MIN_VERSION_lens(5,0,0)
instance Finite a => L.FunctorWithIndex a (Table a) where imap = imapRep
instance Finite a => L.FoldableWithIndex a (Table a) where ifoldMap = ifoldMapRep
instance Finite a => L.TraversableWithIndex a (Table a) where
  itraverse = itraverseRep
#endif

-- | The identity morphism of a constrained category of 'Table's.
idTable :: Finite a => Table a a
idTable = tabulate id

-- | The composition of a constrained category of 'Table's.
composeTable :: (Finite a, Finite b) => Table b c -> Table a b -> Table a c
composeTable tbc tab = tabulate $ index tbc . index tab

-- | 'traverse' a function whose argument is a finite enumerable type.
traverseRep
  :: forall x a b f
   . (Finite x, Applicative f)
  => (a -> f b) -> (x -> a) -> f (x -> b)
traverseRep f = reifySNumberAsNat (cardinality @x) $
  fmap index . traverse f . tabulate @(Table _)

-- | Memoize a function by using a 'Vec' as a lazy lookup table.
--
-- Given a function whose argument is a 'Finite' type, return a new function
-- that looks up the argument in a table constructed by applying the original
-- function to every possible value.  Since 'Vec' stores its elements boxed,
-- none of the applications of 'f' in the table are forced until they're forced
-- by calling the memoized function and forcing the result.
memoize :: Finite a => (a -> b) -> a -> b
memoize = index . tabulate @(Table _)

-- | An 'Iso' between two 'Representable' Functors with the same 'Rep' type.
retabulated
  :: (Representable f, Representable g, Rep f ~ Rep g)
  => Iso (f a) (f b) (g a) (g b)
retabulated = from tabulated . tabulated

-- | Infix 'index', monomorphized.
(!) :: Finite a => Table a b -> a -> b
(!) = index

-- | Lens on a single element.
ix :: (KnownNat (Cardinality a), Finite a) => a -> Lens' (Table a b) b
ix a = a `seq` lens (! a) (\(Table vec) b -> Table (vec & V.ix (toFin a) .~ b))

-- | Monomorphized 'tabulate'.  Can be useful for type ambiguity reasons.
mkTable :: Finite a => (a -> b) -> Table a b
mkTable = tabulate

-- | Convenience function for building any 'Representable' as if by 'traverse'.
--
-- > tabulateA f = sequenceA (tabulate f) = traverse f (tabulate id)
tabulateA
  :: (Traversable t, Representable t, Applicative f)
  => (Rep t -> f b) -> f (t b)
tabulateA = sequenceA . tabulate
