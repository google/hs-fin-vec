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

{-# OPTIONS_GHC -Wno-redundant-constraints #-}
{-# OPTIONS_GHC -Wno-orphans #-}

{-# LANGUAGE AllowAmbiguousTypes #-} -- for valueOf etc
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

-- | Finite natural numbers, with maximum value as part of the type.
-- A value of type @'Fin' n@ ranges from @0@ to @n - 1@.
-- Operations that cause numbers to be out-of-range throw runtime errors.
module Data.Fin.Int
         ( -- * Finite Natural Numbers
           Fin, FinSize
           -- * Conversion
         , fin, finFromIntegral, knownFin, tryFin, finMod, finDivMod, finToInt
           -- * Bound Manipulation
         , embed, unembed, tryUnembed
         , shiftFin, unshiftFin, splitFin
         , weaken, strengthen
         -- * Enumeration
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

import Control.Arrow (first)
import Control.DeepSeq (NFData(rnf))
import Data.Coerce (coerce)
import Data.Data (Data)
import Data.Default.Class (Default(..))
import Data.Kind (Type)
import Data.Portray (Portray)
import Data.Type.Attenuation (Attenuation, coercible)
import Data.Type.Coercion (Coercion(..))
import GHC.Stack (HasCallStack, withFrozenCallStack)
import GHC.TypeNats
         ( type (*), type (+), type (-), type (<=)
         , Nat, KnownNat, natVal'
         )
import GHC.Exts (Proxy#, proxy#)
import Test.QuickCheck (Arbitrary(..), arbitraryBoundedEnum)

#if !MIN_VERSION_base(4,15,0)
import GHC.Natural (naturalToInt)
#endif

-- We could use representation type Integer.
-- We use Int since this is likely to be the most efficient type,
-- partly because it's the natural word size for the machine, but also
-- because it's the type used to index into containers such as Data.Vector.
type FinRep = Int

-- | Naturals bounded above by @n@.
newtype Fin (n :: Nat) = Fin FinRep
  deriving (Eq, Ord, Data)
  -- Fin Read/Show behave like other numeric newtypes: drop the \"Fin\".
  deriving newtype (Show, Portray)

-- | Constraint synonym for naturals @n@ s.t. @'Fin' n@ is inhabited.
type FinSize n = (KnownNat n, 1 <= n)

instance KnownNat n => Read (Fin n) where
  readsPrec p s = first finFromIntegral <$> readsPrec @Integer p s

instance FinSize n => Arbitrary (Fin n) where
    arbitrary = arbitraryBoundedEnum

instance NFData (Fin n) where rnf (Fin x) = rnf x

fin :: forall n. (HasCallStack, KnownNat n) => Int -> Fin n
fin i
  | i <  0 = error $ "Fin: number out of range " ++ show i ++ " < 0"
  | i >= n = error $ "Fin: number out of range " ++ show i ++ " >= " ++ show n
  | otherwise = Fin i
 where
  !n = valueOf @n

-- | This is similar to 'fromInteger', but you get a stack trace on error.
{-# INLINE fin #-}
finFromIntegral
  :: forall n a. (HasCallStack, KnownNat n, Integral a, Show a) => a -> Fin n
finFromIntegral =
  -- We make sure to do the comparisons in a large integer type (namely FinRep)
  -- rather than something like Fin. Otherwise we'd always fail in the
  -- conversion @fin :: Fin 3 -> Fin 4@.
  fin . fromIntegral

{-# INLINE ufin #-}
ufin :: forall n . (HasCallStack, KnownNat n) => FinRep -> Fin n
ufin i | i >= n = error $ "Fin: number out of range " ++ show i ++ " >= "
                            ++ show n
       | otherwise = Fin i
 where
  !n = valueOf @n

-- | Like 'fin', but doesn't do any bounds checks. However, unlike
-- 'unsafeFin', this is safe (by virtue of the type constraints).
knownFin :: forall i n. (KnownNat i, i <= n - 1) => Fin n
knownFin = unsafeFin (valueOf @i :: FinRep)
{-# INLINE knownFin #-}

-- | Like 'fin', but doesn't do any bounds checks.
{-# INLINE unsafeFin #-}
unsafeFin :: Integral a => a -> Fin n
unsafeFin = Fin . fromIntegral

-- | Convert a number to a @Fin@, or @Nothing@ if out of range.
tryFin :: forall n a. (Integral a, KnownNat n) => a -> Maybe (Fin n)
tryFin x = if x >= 0 && x < valueOf @n
           then Just (Fin (fromIntegral x))
           else Nothing

-- | @finMod \@n x@ is equivalent to @fin \@n (x `mod` (valueOf \@n))@
--
-- This raises an exception iff @n ~ 0@.  It could have been written with a
-- @0 < n@ constraint instead, but that would be annoying to prove repeatedly.
finMod :: forall n a . (HasCallStack, Integral a, KnownNat n) => a -> Fin n
finMod = snd . finDivMod

-- | Decompose a number into a component modulo @n@ and the rest.
--
-- This raises an exception iff @n ~ 0@.  See 'finMod'.
finDivMod
  :: forall n a
   . (HasCallStack, Integral a, KnownNat n)
  => a -> (a, Fin n)
finDivMod x
  | n == 0 = error "finDivMod: zero modulus."
  | otherwise = (fromIntegral d, Fin (fromIntegral m))
 where
  -- Do arithmetic in Integer because some types we could get for @a@ can't
  -- represent @valueOf @n@ (specifically, @Fin m@ with m <= n).  We don't use
  -- @FinRep@ because that could make this incorrect for types larger than
  -- @FinRep@.
  (d, m) = divMod (fromIntegral x :: Integer) n
  n = valueOf @n

-- | Reverse the order of the values of a 'Fin' type.
complementFin :: forall n. (KnownNat n) => Fin n -> Fin n
-- Cannot use (maxBound - x) because it would introduce a spurious (1 <= n)
-- constraint. We're not concerned about the n=0 case here because Fin 0 is
-- uninhabited so x can only ever be bottom. In this case, unsafeFin will
-- briefly create an invalid Fin, but evaluating the subtraction will end up
-- raising the error inside of x, so an invalid Fin can never be returned.
complementFin x = unsafeFin (valueOf @n - 1 - finToInt x :: FinRep)

-- | This is like 'fromIntegral', but without the annoying context.
finToInt :: Fin n -> Int
finToInt (Fin i) = i
{-# INLINE finToInt #-}

-- | (*2), but works even if 2 is out-of-bounds.
twice :: KnownNat n => Fin n -> Fin n
twice (Fin i) = ufin $ i * 2

-- | Divide by 2, rounding down.
half :: Fin n -> Fin n
half (Fin n) = Fin (n `quot` 2)

-- | Divide by 4, rounding down.
quarter :: Fin n -> Fin n
quarter (Fin n) = Fin (n `quot` 4)

-- | Decrement by 1, without the validity checks of 'pred'.
unsafePred :: Fin n -> Fin n
unsafePred (Fin x) = Fin (x - 1)
{-# INLINE unsafePred #-}

-- | Increment by 1, without the validity checks of 'succ'.
unsafeSucc :: Fin n -> Fin n
unsafeSucc (Fin x) = Fin (x + 1)
{-# INLINE unsafeSucc #-}

-- Note [Enumerations of Fins]
--
-- Enumerating lists of Fins is implemented by making the corresponding list of
-- Ints and coercing them via @map coerce@. This ensures that these functions
-- are "good list producers" (in the build/foldr fusion sense), by reusing the
-- same property of the Enum instance for Int. Using Fins directly doesn't work
-- (because 0 might be out of range), and coercing the whole list doesn't work
-- either because it interferes with fusion.

-- | Enumerate the entire domain in ascending order. This is equivalent
-- to @enumFrom 0@ or @enumFrom minBound@, but without introducing a
-- spurious @(1 <= n)@ constraint.
enumFin :: forall n. KnownNat n => [Fin n]
-- See Note [Enumerations of Fins]
enumFin = map coerce [(0 :: FinRep) .. valueOf @n - 1]
{-# INLINE enumFin #-}

-- | Enumerate the entire domain in descending order. This is equivalent
-- to @reverse enumFin@, but without introducing a spurious @(1 <= n)@
-- constraint or breaking list-fusion.
enumFinDown :: forall n. KnownNat n => [Fin n]
-- See Note [Enumerations of Fins]
enumFinDown = map coerce [(valueOf @n - 1 :: FinRep), valueOf @n - 2 .. 0]
{-# INLINE enumFinDown #-}

-- | Equivalent to @reverse (enumFromTo 0 x)@ but without introducing
-- a spurious @(1 <= n)@ constraint or breaking list-fusion.
enumDownFrom :: forall n. KnownNat n => Fin n -> [Fin n]
-- See Note [Enumerations of Fins]
enumDownFrom (Fin x) = map coerce [x, x - 1 .. 0]
{-# INLINE enumDownFrom #-}

-- | Equivalent to @reverse (enumFromTo x maxBound)@ but without
-- introducing a spurious @(1 <= n)@ constraint or breaking list-fusion.
enumDownTo :: forall n. KnownNat n => Fin n -> [Fin n]
-- See Note [Enumerations of Fins]
enumDownTo (Fin x) = map coerce [valueOf @n - 1, valueOf @n - 2 .. x]
{-# INLINE enumDownTo #-}

-- | Equivalent to @reverse (enumFromTo y x)@ but without introducing
-- a spurious @(1 <= n)@ constraint or breaking list-fusion.
enumDownFromTo :: forall n. KnownNat n => Fin n -> Fin n -> [Fin n]
-- See Note [Enumerations of Fins]
enumDownFromTo (Fin x) (Fin y) = map coerce [x, x - 1 .. y]
{-# INLINE enumDownFromTo #-}

instance forall n . (KnownNat n) => Enum (Fin n) where
    pred (Fin x)
        | x > 0     = Fin (x - 1)
        | otherwise = error $ "pred @(Fin " ++ show (valueOf @n :: FinRep) ++ "): no predecessor of 0"
    succ (Fin x)
        | x < n - 1 = Fin (x + 1)
        | otherwise = error $ "succ @(Fin " ++ show n ++ "): no successor of " ++ show n
        where !n = valueOf @n
    toEnum   = fin
    fromEnum = finToInt
    -- See Note [Enumerations of Fins]
    enumFrom       (Fin x)                 = map coerce [x .. valueOf @n - 1]
    enumFromThen   (Fin x) (Fin y)         = map coerce [x, y .. valueOf @n - 1]
    enumFromTo     (Fin x)         (Fin z) = map coerce [x .. z]
    enumFromThenTo (Fin x) (Fin y) (Fin z) = map coerce [x, y .. z]
    {-# INLINE pred #-}
    {-# INLINE succ #-}
    {-# INLINE toEnum #-}
    {-# INLINE fromEnum #-}
    {-# INLINE enumFrom #-}
    {-# INLINE enumFromThen #-}
    {-# INLINE enumFromTo #-}
    {-# INLINE enumFromThenTo #-}

-- XXX This should have context 1<=n, but that stops deriving from
-- working for types containing a Fin.
instance (FinSize n) => Bounded (Fin n) where
    minBound = fin (0 :: FinRep)
    maxBound = fin (valueOf @n - 1 :: FinRep)
    {-# INLINE minBound #-}
    {-# INLINE maxBound #-}

-- XXX This should have context 1<=n, but that stops deriving from
-- working for types containing a Fin.
instance (KnownNat n) => Default (Fin n) where
  def = fin (0 :: FinRep)

overflowedError
  :: forall n a
   . (HasCallStack, KnownNat n)
  => String -> Fin n -> Fin n -> a
overflowedError nm x y = error $
  showString nm .
  showString " @" .
  shows (valueOf @n :: FinRep) .
  showString " " .
  shows x .
  showString " " .
  shows y $
  " overflowed FinRep."

outOfRangeError
  :: forall n a
   . (HasCallStack, KnownNat n)
  => String -> Fin n -> Fin n -> FinRep -> a
outOfRangeError nm x y r = error $
  showString nm .
  showString " @" .
  shows (valueOf @n :: FinRep) .
  showString " " .
  shows x .
  showString " " .
  shows y .
  showString " = " .
  shows r $
  " out of range."

add_ :: forall n. KnownNat n => Fin n -> Fin n -> Maybe (Bool, FinRep)
add_ = \ (Fin x) (Fin y) ->
  let z = x + y
  in  if z < x
        then Nothing -- Overflowed Int.
        else Just (z < valueOf @n, z)
{-# INLINE add_ #-}

sub_ :: Fin n -> Fin n -> Maybe (Bool, FinRep)
sub_ = \ (Fin x) (Fin y) -> let z = x - y in Just (z >= 0, z)
{-# INLINE sub_ #-}

mul_ :: forall n. KnownNat n => Fin n -> Fin n -> Maybe (Bool, FinRep)
mul_ = \ (Fin x) (Fin y) ->
  let z = x * y
  in  if x /= 0 && z `div` x /= y
        then Nothing -- Overflowed Int.
        else Just (z < valueOf @n, z)
{-# INLINE mul_ #-}

mkMod
  :: (HasCallStack, KnownNat n)
  => String
  -> (Fin n -> Fin n -> Maybe (Bool, FinRep)) -> Fin n -> Fin n -> Fin n
mkMod nm op = \ x y -> case x `op` y of
  Just (_ok, z) -> finMod z
  Nothing       -> overflowedError nm x y
{-# INLINE mkMod #-}

-- TODO(awpr): it's possible to implement 'modAdd' and 'modSub' without
-- partiality, but it'd be slower.  We should probably improve this somehow.

-- | Add modulo /n/.
--
-- Raises error when intermediate results overflow Int.
--
-- 'modAdd' and ('+%') are different names for the same function.
modAdd, (+%) :: forall n. (HasCallStack, KnownNat n) => Fin n -> Fin n -> Fin n
modAdd = withFrozenCallStack mkMod "modAdd" add_
(+%) = withFrozenCallStack mkMod "(+%)" add_
{-# INLINEABLE modAdd #-}
{-# INLINEABLE (+%) #-}

-- | Subtract modulo /n/.
--
-- 'modSub' and ('-%') are different names for the same function.
modSub, (-%) :: forall n. KnownNat n => Fin n -> Fin n -> Fin n
-- Cannot fail, so no HasCallStack.
modSub = mkMod "modSub" sub_
(-%) = mkMod "(-%)" sub_
{-# INLINEABLE modSub #-}
{-# INLINEABLE (-%) #-}

-- | Multiply modulo /n/.
--
-- Raises error when intermediate results overflow Int.
--
-- 'modMul' and ('*%') are different names for the same function.
modMul, (*%) :: forall n. (HasCallStack, KnownNat n) => Fin n -> Fin n -> Fin n
modMul = withFrozenCallStack mkMod "modMul" mul_
(*%) = withFrozenCallStack mkMod "(*%)" mul_
{-# INLINEABLE modMul #-}
{-# INLINEABLE (*%) #-}

-- | Negate modulo /n/.
--
-- Compared to 'complementFin', this is shifted by 1:
-- @complementFin 0 :: Fin n = n - 1@, while @modNegate 0 :: Fin n = 0@.
modNegate :: forall n. KnownNat n => Fin n -> Fin n
modNegate x@(Fin 0) = x
modNegate (Fin x) = Fin (n - x)
  where n = valueOf @n

mkTry
  :: (Fin n -> Fin n -> Maybe (Bool, FinRep))
  -> Fin n -> Fin n -> Maybe (Fin n)
mkTry op = \x y -> case op x y of
  Just (True, z) -> Just (Fin z)
  _              -> Nothing
{-# INLINE mkTry #-}

-- | Add, returning Nothing for out-of-range results.
tryAdd, (+?) :: KnownNat n => Fin n -> Fin n -> Maybe (Fin n)
tryAdd = mkTry add_
(+?) = tryAdd
{-# INLINEABLE tryAdd #-}
{-# INLINEABLE (+?) #-}

-- | Subtract, returning Nothing for out-of-range results.
trySub, (-?) :: KnownNat n => Fin n -> Fin n -> Maybe (Fin n)
trySub = mkTry sub_
(-?) = trySub
{-# INLINEABLE trySub #-}
{-# INLINEABLE (-?) #-}

-- | Multiply, returning Nothing for out-of-range results.
tryMul, (*?) :: KnownNat n => Fin n -> Fin n -> Maybe (Fin n)
tryMul = mkTry mul_
(*?) = tryMul
{-# INLINEABLE tryMul #-}
{-# INLINEABLE (*?) #-}

-- | Split a 'Fin' of the form @d*x + y@ into @(x, y)@.
divModFin
  :: forall m d. (KnownNat d, KnownNat m) => Fin (d * m) -> (Fin d, Fin m)
divModFin (Fin x) = (Fin d, Fin m)
 where
  (d, m) = divMod x (valueOf @m)

mkChk
  :: (HasCallStack, KnownNat n)
  => String
  -> (Fin n -> Fin n -> Maybe (Bool, FinRep))
  -> Fin n -> Fin n -> Fin n
mkChk nm op = \x y -> case op x y of
  Just (ok, z) -> if ok then Fin z else outOfRangeError nm x y z
  Nothing -> overflowedError nm x y
{-# INLINE mkChk #-}

-- | Add and assert the result is in-range.
--
-- 'chkAdd' and ('+!') are different names for the same function.
chkAdd, (+!) :: (HasCallStack, KnownNat n) => Fin n -> Fin n -> Fin n
chkAdd = withFrozenCallStack mkChk "chkAdd" add_
(+!) = withFrozenCallStack mkChk "(+!)" add_
{-# INLINEABLE chkAdd #-}
{-# INLINEABLE (+!) #-}

-- | Subtract and assert the result is in-range.
--
-- 'chkSub' and ('-!') are different names for the same function.
chkSub, (-!) :: (HasCallStack, KnownNat n) => Fin n -> Fin n -> Fin n
chkSub = withFrozenCallStack mkChk "chkSub" sub_
(-!) = withFrozenCallStack mkChk "(-!)" sub_
{-# INLINEABLE chkSub #-}
{-# INLINEABLE (-!) #-}

-- | Multiply and assert the result is in-range.
--
-- 'chkMul' and ('*!') are different names for the same function.
chkMul, (*!) :: (HasCallStack, KnownNat n) => Fin n -> Fin n -> Fin n
chkMul = withFrozenCallStack mkChk "chkMul" mul_
(*!) = withFrozenCallStack mkChk "(*!)" mul_
{-# INLINEABLE chkMul #-}
{-# INLINEABLE (*!) #-}

-- | Restricted coercion to larger Fin types.
attLT :: (n <= m) => Attenuation (Fin n) (Fin m)
attLT = coercible

-- | Restricted coercion to larger Fin types.
attPlus :: Attenuation (Fin n) (Fin (n + k))
attPlus = coercible

-- | Restricted coercion to larger Fin types.
attMinus :: Attenuation (Fin (n - k)) (Fin n)
attMinus = coercible

-- | Restricted coercion to Int.
attInt :: Attenuation (Fin n) Int
attInt = coercible

-- | Unsafe coercion between any Fin types.
unsafeCoFin :: Coercion (Fin n) (Fin m)
unsafeCoFin = Coercion

-- | Unsafe coercion to and from Int.
unsafeCoInt :: Coercion (Fin n) Int
unsafeCoInt = Coercion

-- | 'embed' increasing the bound by exactly one.
weaken :: Fin n -> Fin (n+1)
weaken (Fin x) = Fin x

-- | Shrink the bound by one if possible.
strengthen :: forall n. KnownNat n => Fin (n+1) -> Maybe (Fin n)
strengthen (Fin x) = if x == valueOf @n then Nothing else Just (Fin x)

-- | 'shiftFin' increases the value and bound of a Fin argument both by @m@.
shiftFin :: forall m n. KnownNat m => Fin n -> Fin (m+n)
shiftFin (Fin x) = Fin (valueOf @m + x)

-- | 'unshiftFin' decreases the value and bound of a Fin argument both by @m@.
unshiftFin :: forall m n. (KnownNat m, KnownNat n) => Fin (m+n) -> Fin n
unshiftFin (Fin x) = fin (x - valueOf @m)

-- | Deconstructs the given Fin into one of two cases depending where it lies
-- in the given range.
splitFin :: forall m n. KnownNat m => Fin (m + n) -> Either (Fin m) (Fin n)
splitFin i = case tryUnembed @m i of
  Just loI -> Left loI
  Nothing -> Right $ unsafeFin $ finToInt i - valueOf @m

-- | Convert to a bigger type.
{-# INLINE embed #-}
embed :: (m <= n) => Fin m -> Fin n
embed (Fin i) = Fin i

-- | Convert to a possibly smaller type.
-- This function fails if the number is too big.
{-# INLINE unembed #-}
unembed :: (HasCallStack, KnownNat n) => Fin m -> Fin n
unembed (Fin i) = ufin i

-- | Convert to a possibly smaller type or return Nothing if out of bounds.
tryUnembed :: KnownNat n => Fin m -> Maybe (Fin n)
tryUnembed (Fin i) = tryFin i

-- | Given two 'Fin's, returns one the size of the inputs' cartesian product.
--
-- The second argument is the lower-order one, i.e.
--
-- > crossFin @_ @n (x+1) y = n + crossFin @_ @n x y
-- > crossFin @_ @n x (y+1) = 1 + crossFin @_ @n x y
crossFin
  :: forall m n
   . (KnownNat n, KnownNat (m * n)) => Fin m -> Fin n -> Fin (m * n)
crossFin (Fin x) (Fin y) = fin (x * valueOf @n + y)

-- | Get the value a statically known natural number.
{-# INLINE valueOf #-}
valueOf :: forall (n :: Nat) (i :: Type) . (KnownNat n, Num i) => i
valueOf = fromIntegral $ natVal' (proxy# :: Proxy# n)

#if !MIN_VERSION_base(4,15,0)
{-# RULES "fromIntegral/Natural->Int" fromIntegral = naturalToInt #-}
#endif
