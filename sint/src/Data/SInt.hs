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

-- | Provides a singleton type for a subset of 'Nat's, represented by 'Int'.
--
-- This is particularly useful when working with length-indexed array types,
-- since the array primitives generally expect lengths and indices to be
-- 'Int's.  Thus, there's no need to pay the runtime cost of lugging around
-- 'Natural's to handle greater-than-maxInt-length arrays, since the underlying
-- primitives don't handle them either.
--
-- An @'SInt' n@ is trusted absolutely by downstream code to contain an 'Int'
-- @n'@ s.t. @fromIntegral n' == natVal' \@n Proxy#@.  In particular, this
-- trust extends to a willingness to use two runtime-equal 'SInt's as proof
-- that their type parameters are equal, or to use GHC primitives in a way
-- that's only memory-safe if this property holds.  This means it should be
-- considered /unsafe/ to construct an 'SInt' in any way that's not statically
-- guaranteed to produce the correct runtime value, and to construct one with
-- an incorrect runtime value is equivalent to using 'unsafeCoerce'
-- incorrectly.
--
-- 'SInt' should be seen as a more efficient implementation of
-- @data SNat n = KnownNat n => SNat@, so that constructing an incorrect 'SInt'
-- would be equivalent to producing an incorrect 'KnownNat' instance.
--
-- 'SInt's are constructed safely by 'staticSIntVal' with no overhead,
-- by 'sintVal' with runtime bounds checks based on a 'KnownNat' instance, or
-- by various arithmetic functions.

{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UnboxedTuples #-}

#include "MachDeps.h"

module Data.SInt
         ( SInt(SI#, SI, unSInt), trySIntVal, sintVal, reifySInt, withSInt
         , addSInt, subSInt, subSIntLE, subSIntL, mulSInt, divSIntL, divSIntR
         , staticSIntVal
           -- * Internal
         , IntMaxP1
         ) where

import Data.Proxy (Proxy(..))
import GHC.Exts (Int(I#), addIntC#, mulIntMayOflo#, proxy#)
import GHC.Stack (HasCallStack)
import GHC.TypeNats
         ( type (<=), type (+), type (-), type (*), type (^), CmpNat
         , KnownNat, Nat, natVal', SomeNat(..), someNatVal
         )
import Numeric.Natural (Natural)

import Data.Portray (Portray)
import Data.Portray.Diff (Diff)

#if MIN_VERSION_base(4,15,0)
import Unsafe.Coerce (unsafeEqualityProof, UnsafeEquality(..))
#else
import Data.Type.Equality ((:~:)(..))
import Unsafe.Coerce (unsafeCoerce)
#endif

-- | A singleton type linking a runtime 'Int' and a type-level 'Nat'.
newtype SInt (n :: Nat) = MkSInt Int
  deriving newtype (Show, Portray, Diff)

-- We must take care to prevent 'SInt's from being coerced across @n@.
type role SInt nominal

-- | Construct an 'SInt' unsafely.  Incorrect uses cause undefined behavior.
--
-- See the module intro for more details; prefer to use safe methods to
-- construct 'SInt's, and treat this constructor equivalently to
-- 'unsafeCoerce'.
pattern SI# :: Int -> SInt n
pattern SI# x = MkSInt x
{-# COMPLETE SI# #-}

-- | A unidirectional pattern for safely deconstructing 'SInt's.
--
-- This lets us export 'unSInt' as if it were a field selector, without making
-- it legal to use in record updates (because this pattern is unidirectional).
pattern SI :: Int -> SInt n
pattern SI {unSInt} <- MkSInt unSInt
{-# COMPLETE SI #-}

-- | Use an 'Int' as an existentially-quantified 'SInt'.
withSInt :: HasCallStack => Int -> (forall n. SInt n -> r) -> r
withSInt n f
  | n < 0     = error "withSInt: negative value"
  | otherwise = f (SI# n)

maxInt :: Natural
maxInt = fromIntegral (maxBound :: Int)

-- | Produce an 'SInt' for a given 'KnownNat', or 'Nothing' if out of range.
trySIntVal :: forall n. KnownNat n => Maybe (SInt n)
trySIntVal =
  let n = natVal' @n proxy#
  in  if n <= maxInt then Just (MkSInt (fromIntegral n)) else Nothing
{-# INLINE trySIntVal #-}

-- | Produce an 'SInt' for a given 'KnownNat', or 'error' if out of range.
sintVal :: forall n. (HasCallStack, KnownNat n) => SInt n
sintVal = case trySIntVal of
  Just n -> n
  Nothing -> error $
    "Nat " ++ show (natVal' @n proxy#) ++ " out of range for Int."
{-# INLINE sintVal #-}

-- | One more than the maximum representable 'Int' on the current platform.
type IntMaxP1 = 2 ^ (WORD_SIZE_IN_BITS - 1)

-- | Like 'sintVal', but with static proof that it's in-bounds.
--
-- This optimizes down to an actual primitive literal wrapped in the
-- appropriate constructors, unlike 'sintVal', where the bounds checking gets
-- in the way.  If you're constructing a statically-known 'SInt', use
-- 'staticSIntVal'; while if you're constructing an 'SInt' from a runtime
-- 'KnownNat' instance, you'll have to use 'sintVal'.
staticSIntVal :: forall n. (CmpNat n IntMaxP1 ~ 'LT, KnownNat n) => SInt n
staticSIntVal = MkSInt (fromIntegral (natVal' @n proxy#))
{-# INLINE staticSIntVal #-}

-- | Add two 'SInt's with bounds checks; 'error' if the result overflows.
addSInt :: HasCallStack => SInt m -> SInt n -> SInt (m + n)
addSInt (SI# (I# m)) (SI# (I# n)) =
  case addIntC# m n of
    (# mn, ovf #)
      | I# ovf == 0 -> SI# (I# mn)
      | otherwise   -> error $
          "Nat " ++
          show (fromIntegral (I# m) + fromIntegral (I# n) :: Natural) ++
          " out of range for Int."

-- | Multiply two 'SInt's with bounds checks; 'error' if the result overflows.
mulSInt :: HasCallStack => SInt m -> SInt n -> SInt (m * n)
mulSInt (SI# m@(I# m')) (SI# n@(I# n')) =
   case mulIntMayOflo# m' n' of
     ovf
       | I# ovf == 0 -> SI# mn
       | mn > 0 && fromIntegral mn == mnNat -> SI# mn
       | otherwise -> error $ "Nat " ++ show mnNat ++ " out of range for Int."
 where
  mn = m * n
  mnNat = fromIntegral m * fromIntegral n :: Natural

-- | Subtract two 'SInt's with bounds checks; 'error' if the result is negative.
subSInt :: HasCallStack => SInt m -> SInt n -> SInt (m - n)
subSInt (SI# m) (SI# n)
  | n > m = error $ "Nat " ++ show (m - n) ++ " out of range."
  | otherwise = SI# (m - n)

-- | Subtract two 'SInt's, using an inequality constraint to rule out overflow.
subSIntLE :: n <= m => SInt m -> SInt n -> SInt (m - n)
subSIntLE (SI# m) (SI# n) = SI# (m - n)

-- | "Un-add" an 'SInt' from another 'SInt', on the left.
--
-- This form of 'subSInt' is more convenient in certain cases when a type
-- signature ensures a particular 'SInt' is of the form @m + n@.
subSIntL :: SInt (m + n) -> SInt m -> SInt n
subSIntL (SI# mn) (SI# m) = SI# (mn - m)

-- | "Un-multiply" an 'SInt' by another 'SInt', on the left.
--
-- This form of @divSInt@ is more convenient in certain cases when a type
-- signature ensures a particular 'SInt' is of the form @m * n@.
divSIntL :: SInt (m * n) -> SInt m -> SInt n
divSIntL (SI# mn) (SI# m) = SI# (mn `div` m)

-- | "Un-multiply" an 'SInt' by another 'SInt', on the right.
--
-- This form of @divSInt@ is more convenient in certain cases when a type
-- signature ensures a particular 'SInt' is of the form @m * n@.
divSIntR :: SInt (m * n) -> SInt n -> SInt m
divSIntR (SI# mn) (SI# n) = SI# (mn `div` n)

-- | Bring an 'SInt' back into the type level as a 'KnownNat' instance.
reifySInt :: forall n r. SInt n -> (KnownNat n => r) -> r
reifySInt (SI# n) r =
  case someNatVal (fromIntegral n) of
    SomeNat (Proxy :: Proxy m) ->
#if MIN_VERSION_base(4,15,0)
      case unsafeEqualityProof @m @n of UnsafeRefl -> r
#else
      case unsafeCoerce Refl :: m :~: n of Refl -> r
#endif
