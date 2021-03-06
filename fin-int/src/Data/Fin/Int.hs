-- Copyright 2017-2021 Google LLC
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

{-# LANGUAGE AllowAmbiguousTypes #-} -- for knownFin
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

-- | Finite natural numbers, with upper bound as part of the type.
--
-- A value of type @'Fin' n@ ranges from @0@ to @n - 1@.
--
-- Operations that can cause numbers to be out-of-range come with variants that
-- throw runtime errors, return 'Maybe', or return results modulo the bound.
--
-- In contrast to "Data.Fin.Int.Explicit", this module provides an API that
-- accepts the bounds values implicitly via 'KnownNat'.  This can be more
-- convenient when there's no arithmetic involved in the bounds, but may cost
-- more runtime 'Numeric.Natural.Natural'-to-'Int' conversions.
--
-- When type-level arithmetic is involved, the
-- [ghc-typelits-knownnat](https://hackage.haskell.org/package/ghc-typelits-knownnat)
-- plugin may be useful to derive 'KnownNat' instances for bounds automatically.

module Data.Fin.Int
         ( -- * Finite Natural Numbers
           Fin, FinSize
           -- * Conversion
         , fin, finFromIntegral, knownFin, tryFin, finMod, finDivMod, finToInt
           -- * Bound Manipulation
         , embed, unembed, tryUnembed
         , shiftFin, unshiftFin, tryUnshiftFin, splitFin, concatFin
         , weaken, strengthen
         -- * Enumeration
         , minFin, maxFin
         , enumFin, enumFinDown, enumDownFrom, enumDownTo, enumDownFromTo
           -- * Arithmetic
           -- ** In 'Maybe'
         , tryAdd, trySub, tryMul
         , (+?), (-?), (*?)
           -- ** Checked
         , chkAdd, chkSub, chkMul
         , (+!), (-!), (*!)
           -- ** Modular arithmetic
         , modAdd, modSub, modMul, modNegate
         , (+%), (-%), (*%)
           -- ** Miscellaneous
         , divModFin
         , complementFin, twice, half, quarter
         , crossFin
           -- * Attenuations
         , attLT, attPlus, attMinus, attInt
           -- * Unsafe, fast
         , unsafeFin, unsafePred, unsafeSucc, unsafeCoFin, unsafeCoInt
         ) where

import Data.SInt (sintVal)
import GHC.Stack (HasCallStack)
import GHC.TypeNats (type (*), type (+), type (-), type (<=), KnownNat)

import Data.Fin.Int.Explicit
         ( Fin, FinSize, unsafeFin, unsafeSucc, unsafePred
         , unsafeCoFin, unsafeCoInt
         , attInt, attMinus, attPlus, attLT
         , half, quarter
         , embed, weaken, finToInt
         , modSub, trySub, minFin
         )
import qualified Data.Fin.Int.Explicit as E

-- | Construct a 'Fin' from an 'Int', with bounds checks.
{-# INLINE fin #-}
fin :: forall n. (HasCallStack, KnownNat n) => Int -> Fin n
fin = E.fin sintVal

-- | Generalized 'fin' that works on any 'Integral' type.
{-# INLINE finFromIntegral #-}
finFromIntegral
  :: forall n a
   . (HasCallStack, KnownNat n, Integral a, Show a)
  => a -> Fin n
finFromIntegral = E.finFromIntegral sintVal

-- | Construct a 'Fin' from a 'GHC.TypeNats.Nat' known to be in-bounds.
knownFin :: forall i n. (KnownNat i, i <= n - 1) => Fin n
knownFin = E.knownFin (sintVal @i)
{-# INLINE knownFin #-}

-- | Convert a number to a @Fin@, or @Nothing@ if out of range.
tryFin :: forall n a. (Integral a, KnownNat n) => a -> Maybe (Fin n)
tryFin = E.tryFin sintVal

-- | @finMod \@n x@ is equivalent to @fin \@n (x `mod` (valueOf \@n))@
--
-- This raises an exception iff @n ~ 0@.  It could have been written with a
-- @0 < n@ constraint instead, but that would be annoying to prove repeatedly.
finMod :: forall n a . (HasCallStack, Integral a, KnownNat n) => a -> Fin n
finMod = E.finMod sintVal

-- | Decompose a number into a component modulo @n@ and the rest.
--
-- This raises an exception iff @n ~ 0@.  See 'finMod'.
finDivMod
  :: forall n a
   . (HasCallStack, Integral a, KnownNat n)
  => a -> (a, Fin n)
finDivMod = E.finDivMod sintVal

-- | Reverse the order of the values of a 'Fin' type.
complementFin :: forall n. (KnownNat n) => Fin n -> Fin n
complementFin  = E.complementFin sintVal

-- | (*2), but works even if 2 is out-of-bounds.
twice :: KnownNat n => Fin n -> Fin n
twice = E.twice sintVal

-- | The maximal value of the given inhabited 'Fin' type (i.e @n - 1@).
maxFin :: (1 <= n, KnownNat n) => Fin n
maxFin = E.maxFin sintVal
{-# INLINE maxFin #-}

-- | Enumerate the entire domain in ascending order. This is equivalent
-- to @enumFrom 0@ or @enumFrom minBound@, but without introducing a
-- spurious @(1 <= n)@ constraint.
enumFin :: forall n. KnownNat n => [Fin n]
enumFin = E.enumFin sintVal
{-# INLINE enumFin #-}

-- | Enumerate the entire domain in descending order. This is equivalent
-- to @reverse enumFin@, but without introducing a spurious @(1 <= n)@
-- constraint or breaking list-fusion.
enumFinDown :: forall n. KnownNat n => [Fin n]
enumFinDown = E.enumFinDown sintVal
{-# INLINE enumFinDown #-}

-- | Equivalent to @reverse (enumFromTo 0 x)@ but without introducing
-- a spurious @(1 <= n)@ constraint or breaking list-fusion.
enumDownFrom :: forall n. KnownNat n => Fin n -> [Fin n]
enumDownFrom = E.enumDownFrom sintVal
{-# INLINE enumDownFrom #-}

-- | Equivalent to @reverse (enumFromTo x maxBound)@ but without
-- introducing a spurious @(1 <= n)@ constraint or breaking list-fusion.
enumDownTo :: forall n. KnownNat n => Fin n -> [Fin n]
enumDownTo = E.enumDownTo sintVal
{-# INLINE enumDownTo #-}

-- | Equivalent to @reverse (enumFromTo y x)@ but without introducing
-- a spurious @(1 <= n)@ constraint or breaking list-fusion.
enumDownFromTo :: forall n. KnownNat n => Fin n -> Fin n -> [Fin n]
enumDownFromTo = E.enumDownFromTo sintVal
{-# INLINE enumDownFromTo #-}

-- TODO(awpr): it's possible to implement 'modAdd' and 'modSub' without
-- partiality, but it'd be slower.  We should probably improve this somehow.

-- | Add modulo /n/.
--
-- Raises error when intermediate results overflow Int.
--
-- 'modAdd' and ('+%') are different names for the same function.
modAdd, (+%) :: forall n. (HasCallStack, KnownNat n) => Fin n -> Fin n -> Fin n
modAdd = E.modAdd sintVal
(+%) = E.modAdd sintVal
{-# INLINEABLE modAdd #-}
{-# INLINEABLE (+%) #-}

-- | Subtract modulo /n/.
--
-- 'modSub' and ('-%') are different names for the same function.
(-%) :: forall n. KnownNat n => Fin n -> Fin n -> Fin n
(-%) = E.modSub sintVal
{-# INLINEABLE (-%) #-}

-- | Multiply modulo /n/.
--
-- Raises error when intermediate results overflow Int.
--
-- 'modMul' and ('*%') are different names for the same function.
modMul, (*%) :: forall n. (HasCallStack, KnownNat n) => Fin n -> Fin n -> Fin n
modMul = E.modMul sintVal
(*%) = E.modMul sintVal
{-# INLINEABLE modMul #-}
{-# INLINEABLE (*%) #-}

-- | Negate modulo /n/.
--
-- Compared to 'complementFin', this is shifted by 1:
-- @complementFin 0 :: Fin n = n - 1@, while @modNegate 0 :: Fin n = 0@.
modNegate :: forall n. KnownNat n => Fin n -> Fin n
modNegate = E.modNegate sintVal

-- | Add, returning Nothing for out-of-range results.
tryAdd, (+?) :: KnownNat n => Fin n -> Fin n -> Maybe (Fin n)
tryAdd = E.tryAdd sintVal
(+?) = E.tryAdd sintVal
{-# INLINEABLE tryAdd #-}
{-# INLINEABLE (+?) #-}

-- | Subtract, returning Nothing for out-of-range results.
(-?) :: KnownNat n => Fin n -> Fin n -> Maybe (Fin n)
(-?) = E.trySub
{-# INLINEABLE (-?) #-}

-- | Multiply, returning Nothing for out-of-range results.
tryMul, (*?) :: KnownNat n => Fin n -> Fin n -> Maybe (Fin n)
tryMul = E.tryMul sintVal
(*?) = E.tryMul sintVal
{-# INLINEABLE tryMul #-}
{-# INLINEABLE (*?) #-}

-- | Split a 'Fin' of the form @d*x + y@ into @(x, y)@.
divModFin :: forall m d. KnownNat m => Fin (d * m) -> (Fin d, Fin m)
divModFin = E.divModFin sintVal

-- | Add and assert the result is in-range.
--
-- 'chkAdd' and ('+!') are different names for the same function.
chkAdd, (+!) :: (HasCallStack, KnownNat n) => Fin n -> Fin n -> Fin n
chkAdd = E.chkAdd sintVal
(+!) = E.chkAdd sintVal
{-# INLINEABLE chkAdd #-}
{-# INLINEABLE (+!) #-}

-- | Subtract and assert the result is in-range.
--
-- 'chkSub' and ('-!') are different names for the same function.
chkSub, (-!) :: (HasCallStack, KnownNat n) => Fin n -> Fin n -> Fin n
chkSub = E.chkSub sintVal
(-!) = E.chkSub sintVal
{-# INLINEABLE chkSub #-}
{-# INLINEABLE (-!) #-}

-- | Multiply and assert the result is in-range.
--
-- 'chkMul' and ('*!') are different names for the same function.
chkMul, (*!) :: (HasCallStack, KnownNat n) => Fin n -> Fin n -> Fin n
chkMul = E.chkMul sintVal
(*!) = E.chkMul sintVal
{-# INLINEABLE chkMul #-}
{-# INLINEABLE (*!) #-}

-- | Shrink the bound by one if possible.
strengthen :: forall n. KnownNat n => Fin (n+1) -> Maybe (Fin n)
strengthen = E.strengthen sintVal

-- | 'shiftFin' increases the value and bound of a Fin both by @m@.
shiftFin :: forall m n. KnownNat m => Fin n -> Fin (m+n)
shiftFin = E.shiftFin sintVal

-- | 'unshiftFin' decreases the value and bound of a Fin both by @m@.
--
-- Raises an exception if the result would be negative.
unshiftFin
  :: forall m n
   . (HasCallStack, KnownNat m, KnownNat n)
  => Fin (m+n) -> Fin n
unshiftFin = E.unshiftFin sintVal sintVal

-- | 'tryUnshiftFin' decreases the value and bound of a Fin both by @m@.
tryUnshiftFin
  :: forall m n
   . (KnownNat m, KnownNat n)
  => Fin (m+n) -> Maybe (Fin n)
tryUnshiftFin = E.tryUnshiftFin sintVal sintVal

-- | Deconstructs the given Fin into one of two cases depending where it lies
-- in the given range.
splitFin :: forall m n. KnownNat m => Fin (m + n) -> Either (Fin m) (Fin n)
splitFin = E.splitFin sintVal

-- | The inverse of 'splitFin'.
concatFin :: forall m n. KnownNat m => Either (Fin m) (Fin n) -> Fin (m + n)
concatFin = E.concatFin sintVal

-- | Convert to a 'Fin' with a (potentially) smaller bound.
--
-- This function throws an exception if the number is out of range of the
-- target type.
{-# INLINE unembed #-}
unembed :: (HasCallStack, KnownNat n) => Fin m -> Fin n
unembed = E.unembed sintVal

-- | Convert to a 'Fin' with a (potentially) smaller bound.
--
-- Returns 'Nothing' if the number is out of range of the target type.
{-# INLINE tryUnembed #-}
tryUnembed :: KnownNat n => Fin m -> Maybe (Fin n)
tryUnembed = E.tryUnembed sintVal

-- | Given two 'Fin's, returns one the size of the inputs' cartesian product.
--
-- The second argument is the lower-order one, i.e.
--
-- > crossFin @_ @n (x+1) y = n + crossFin @_ @n x y
-- > crossFin @_ @n x (y+1) = 1 + crossFin @_ @n x y
crossFin :: forall m n. KnownNat n => Fin m -> Fin n -> Fin (m * n)
crossFin = E.crossFin sintVal
