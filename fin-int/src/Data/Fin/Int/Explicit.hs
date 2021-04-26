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
{-# LANGUAGE ViewPatterns #-}

-- | Finite natural numbers, with maximum value as part of the type.
-- A value of type @'Fin' n@ ranges from @0@ to @n - 1@.
-- Operations that cause numbers to be out-of-range throw runtime errors.

module Data.Fin.Int.Explicit
         ( -- * Finite Natural Numbers
           Fin, FinSize
           -- * Conversion
         , fin, finFromIntegral, knownFin, tryFin, finMod, finDivMod, finToInt
           -- * Bound Manipulation
         , embed, unembed, tryUnembed
         , shiftFin, unshiftFin, tryUnshiftFin, splitFin
         , weaken, strengthen
         -- * Enumeration
         , minFin, maxFin
         , enumFin, enumFinDown, enumDownFrom, enumDownTo, enumDownFromTo
           -- * Arithmetic
           -- ** In 'Maybe'
         , tryAdd, trySub, tryMul
           -- ** Checked
         , chkAdd, chkSub, chkMul
           -- ** Modular arithmetic
         , modAdd, modSub, modMul, modNegate
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
import Data.Type.Coercion (Coercion(..))
import GHC.Stack (HasCallStack, withFrozenCallStack)
import GHC.TypeNats
         ( type (*), type (+), type (-), type (<=)
         , Nat, KnownNat
         )

import Data.Default.Class (Default(..))
import Data.Portray (Portray)
import Data.Portray.Diff (Diff)
import Data.Type.Attenuation (Attenuation, coercible)
import Test.QuickCheck (Arbitrary(..), arbitraryBoundedEnum)

import Data.SInt (SInt, unSInt, sintVal)

-- We could use representation type Integer.
-- We use Int since this is likely to be the most efficient type,
-- partly because it's the natural word size for the machine, but also
-- because it's the type used to index into containers such as Data.Vector.
type FinRep = Int

-- | Naturals bounded above by @n@.
newtype Fin (n :: Nat) = Fin FinRep
  deriving (Eq, Ord, Data)
  -- Fin Read/Show behave like other numeric newtypes: drop the \"Fin\".
  deriving newtype (Show, Portray, Diff)

-- | Constraint synonym for naturals @n@ s.t. @'Fin' n@ is inhabited.
type FinSize n = (KnownNat n, 1 <= n)

instance KnownNat n => Read (Fin n) where
  readsPrec p s = first (finFromIntegral sintVal) <$> readsPrec @Integer p s

instance FinSize n => Arbitrary (Fin n) where
  arbitrary = arbitraryBoundedEnum

instance NFData (Fin n) where rnf (Fin x) = rnf x

fin :: HasCallStack => SInt n -> Int -> Fin n
fin (unSInt -> !n) i
  | i <  0 = error $ "Fin: number out of range " ++ show i ++ " < 0"
  | i >= n = error $ "Fin: number out of range " ++ show i ++ " >= " ++ show n
  | otherwise = Fin i

-- | This is similar to 'fromInteger', but you get a stack trace on error.
{-# INLINE fin #-}
finFromIntegral
  :: (HasCallStack, Integral a, Show a)
  => SInt n -> a -> Fin n
finFromIntegral n =
  -- We make sure to do the comparisons in a large integer type (namely FinRep)
  -- rather than something like Fin. Otherwise we'd always fail in the
  -- conversion @fin :: Fin 3 -> Fin 4@.
  fin n . fromIntegral

{-# INLINE ufin #-}
ufin :: HasCallStack => SInt n -> FinRep -> Fin n
ufin sn i
  | i >= n = error $ "Fin: number out of range " ++ show i ++ " >= " ++ show n
  | otherwise = Fin i
 where
  n = unSInt sn

-- | Like 'fin', but doesn't do any bounds checks. However, unlike
-- 'unsafeFin', this is safe (by virtue of the type constraints).
knownFin :: (i <= n - 1) => SInt i -> Fin n
knownFin = unsafeFin . unSInt
{-# INLINE knownFin #-}

-- | Like 'fin', but doesn't do any bounds checks.
{-# INLINE unsafeFin #-}
unsafeFin :: Integral a => a -> Fin n
unsafeFin = Fin . fromIntegral

-- | Convert a number to a @Fin@, or @Nothing@ if out of range.
tryFin :: Integral a => SInt n -> a -> Maybe (Fin n)
tryFin n x =
  if x >= 0 && x < fromIntegral (unSInt n)
    then Just (Fin (fromIntegral x))
    else Nothing

-- | @finMod \@n x@ is equivalent to @fin \@n (x `mod` (valueOf \@n))@
--
-- This raises an exception iff @n ~ 0@.  It could have been written with a
-- @0 < n@ constraint instead, but that would be annoying to prove repeatedly.
finMod :: forall n a . (HasCallStack, Integral a) => SInt n -> a -> Fin n
finMod n = snd . finDivMod n

-- | Decompose a number into a component modulo @n@ and the rest.
--
-- This raises an exception iff @n ~ 0@.  See 'finMod'.
finDivMod
  :: forall n a
   . (HasCallStack, Integral a)
  => SInt n -> a -> (a, Fin n)
finDivMod sn x
  | n == 0 = error "finDivMod: zero modulus."
  | otherwise = (fromIntegral d, Fin (fromIntegral m))
 where
  -- Do arithmetic in Integer because some types we could get for @a@ can't
  -- represent @valueOf @n@ (specifically, @Fin m@ with m <= n).  We don't use
  -- @FinRep@ because that could make this incorrect for types larger than
  -- @FinRep@.
  (d, m) = divMod (fromIntegral x :: Integer) n
  n = toInteger $ unSInt sn

-- | Reverse the order of the values of a 'Fin' type.
complementFin :: SInt n -> Fin n -> Fin n
-- Cannot use (maxBound - x) because it would introduce a spurious (1 <= n)
-- constraint. We're not concerned about the n=0 case here because Fin 0 is
-- uninhabited so x can only ever be bottom. In this case, unsafeFin will
-- briefly create an invalid Fin, but evaluating the subtraction will end up
-- raising the error inside of x, so an invalid Fin can never be returned.
complementFin sn x = unsafeFin (unSInt sn - 1 - finToInt x)

-- | This is like 'fromIntegral', but without the annoying context.
finToInt :: Fin n -> Int
finToInt (Fin i) = i
{-# INLINE finToInt #-}

-- | (*2), but works even if 2 is out-of-bounds.
twice :: SInt n -> Fin n -> Fin n
twice sn (Fin i) = ufin sn $ i * 2

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
enumFin :: SInt n -> [Fin n]
-- See Note [Enumerations of Fins]
enumFin sn = map coerce [0 .. unSInt sn - 1]
{-# INLINE enumFin #-}

-- | Enumerate the entire domain in descending order. This is equivalent
-- to @reverse enumFin@, but without introducing a spurious @(1 <= n)@
-- constraint or breaking list-fusion.
enumFinDown :: SInt n -> [Fin n]
-- See Note [Enumerations of Fins]
enumFinDown sn = map coerce [unSInt sn - 1, unSInt sn - 2 .. 0]
{-# INLINE enumFinDown #-}

-- | Equivalent to @reverse (enumFromTo 0 x)@ but without introducing
-- a spurious @(1 <= n)@ constraint or breaking list-fusion.
enumDownFrom :: SInt n -> Fin n -> [Fin n]
-- See Note [Enumerations of Fins]
enumDownFrom _sn (Fin x) = map coerce [x, x - 1 .. 0]
{-# INLINE enumDownFrom #-}

-- | Equivalent to @reverse (enumFromTo x maxBound)@ but without
-- introducing a spurious @(1 <= n)@ constraint or breaking list-fusion.
enumDownTo :: SInt n -> Fin n -> [Fin n]
-- See Note [Enumerations of Fins]
enumDownTo sn (Fin x) = map coerce [unSInt sn - 1, unSInt sn - 2 .. x]
{-# INLINE enumDownTo #-}

-- | Equivalent to @reverse (enumFromTo y x)@ but without introducing
-- a spurious @(1 <= n)@ constraint or breaking list-fusion.
enumDownFromTo :: SInt n -> Fin n -> Fin n -> [Fin n]
-- See Note [Enumerations of Fins]
enumDownFromTo _sn (Fin x) (Fin y) = map coerce [x, x - 1 .. y]
{-# INLINE enumDownFromTo #-}

instance KnownNat n => Enum (Fin n) where
    pred (Fin x)
        | x > 0     = Fin (x - 1)
        | otherwise = error $
            "pred @(Fin " ++ show (unSInt @n sintVal) ++
            "): no predecessor of 0"
    succ (Fin x)
        | x < n - 1 = Fin (x + 1)
        | otherwise = error $
            "succ @(Fin " ++ show n ++ "): no successor of " ++ show n
        where !n = unSInt @n sintVal
    toEnum   = fin sintVal
    fromEnum = finToInt
    -- See Note [Enumerations of Fins]
    enumFrom       (Fin x)                 =
      map coerce [x .. unSInt @n sintVal - 1]
    enumFromThen   (Fin x) (Fin y)         =
      map coerce [x, y .. unSInt @n sintVal - 1]
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

-- | The minimal value of the given inhabited 'Fin' type (i.e. @0@).
minFin :: 1 <= n => Fin n
minFin = Fin 0

-- | The maximal value of the given inhabited 'Fin' type (i.e @n - 1@).
maxFin :: 1 <= n => SInt n -> Fin n
maxFin sn = Fin (unSInt sn - 1)

instance FinSize n => Bounded (Fin n) where
    minBound = minFin
    maxBound = maxFin sintVal
    {-# INLINE minBound #-}
    {-# INLINE maxBound #-}

-- XXX This should have context 1<=n, but that stops deriving from
-- working for types containing a Fin.
instance KnownNat n => Default (Fin n) where
  def = fin sintVal (0 :: FinRep)

overflowedError
  :: forall n a
   . HasCallStack
  => SInt n -> String -> Fin n -> Fin n -> a
overflowedError sn nm x y = error $
  showString nm .
  showString " @" .
  shows (unSInt sn) .
  showString " " .
  shows x .
  showString " " .
  shows y $
  " overflowed FinRep."

outOfRangeError
  :: forall n a
   . HasCallStack
  => SInt n -> String -> Fin n -> Fin n -> FinRep -> a
outOfRangeError sn nm x y r = error $
  showString nm .
  showString " @" .
  shows (unSInt sn) .
  showString " " .
  shows x .
  showString " " .
  shows y .
  showString " = " .
  shows r $
  " out of range."

add_ :: SInt n -> Fin n -> Fin n -> Maybe (Bool, FinRep)
add_ sn = \ (Fin x) (Fin y) ->
  let z = x + y
  in  if z < x
        then Nothing -- Overflowed Int.
        else Just (z < unSInt sn, z)
{-# INLINE add_ #-}

sub_ :: Fin n -> Fin n -> Maybe (Bool, FinRep)
sub_ = \ (Fin x) (Fin y) -> let z = x - y in Just (z >= 0, z)
{-# INLINE sub_ #-}

mul_ :: SInt n -> Fin n -> Fin n -> Maybe (Bool, FinRep)
mul_ sn = \ (Fin x) (Fin y) ->
  let z = x * y
  in  if x /= 0 && z `div` x /= y
        then Nothing -- Overflowed Int.
        else Just (z < unSInt sn, z)
{-# INLINE mul_ #-}

mkMod
  :: HasCallStack
  => SInt n
  -> String
  -> (Fin n -> Fin n -> Maybe (Bool, FinRep)) -> Fin n -> Fin n -> Fin n
mkMod sn nm op = \ x y -> case x `op` y of
  Just (_ok, z) -> finMod sn z
  Nothing       -> overflowedError sn nm x y
{-# INLINE mkMod #-}

-- TODO(awpr): it's possible to implement 'modAdd' and 'modSub' without
-- partiality, but it'd be slower.  We should probably improve this somehow.

-- | Add modulo /n/.
--
-- Raises error when intermediate results overflow Int.
modAdd :: HasCallStack => SInt n -> Fin n -> Fin n -> Fin n
modAdd sn = withFrozenCallStack mkMod sn "modAdd" (add_ sn)
{-# INLINEABLE modAdd #-}

-- | Subtract modulo /n/.
modSub :: SInt n -> Fin n -> Fin n -> Fin n
-- Cannot fail, so no HasCallStack.
modSub sn = mkMod sn "modSub" sub_
{-# INLINEABLE modSub #-}

-- | Multiply modulo /n/.
--
-- Raises error when intermediate results overflow Int.
modMul :: HasCallStack => SInt n -> Fin n -> Fin n -> Fin n
modMul sn = withFrozenCallStack mkMod sn "modMul" (mul_ sn)
{-# INLINEABLE modMul #-}

-- | Negate modulo /n/.
--
-- Compared to 'complementFin', this is shifted by 1:
-- @complementFin 0 :: Fin n = n - 1@, while @modNegate 0 :: Fin n = 0@.
modNegate :: SInt n -> Fin n -> Fin n
modNegate _  (Fin 0) = Fin 0
modNegate sn (Fin x) = Fin (unSInt sn - x)

mkTry
  :: (Fin n -> Fin n -> Maybe (Bool, FinRep))
  -> Fin n -> Fin n -> Maybe (Fin n)
mkTry op = \x y -> case op x y of
  Just (True, z) -> Just (Fin z)
  _              -> Nothing
{-# INLINE mkTry #-}

-- | Add, returning Nothing for out-of-range results.
tryAdd :: SInt n -> Fin n -> Fin n -> Maybe (Fin n)
tryAdd = mkTry . add_
{-# INLINEABLE tryAdd #-}

-- | Subtract, returning Nothing for out-of-range results.
trySub :: Fin n -> Fin n -> Maybe (Fin n)
trySub = mkTry sub_
{-# INLINEABLE trySub #-}

-- | Multiply, returning Nothing for out-of-range results.
tryMul :: SInt n -> Fin n -> Fin n -> Maybe (Fin n)
tryMul = mkTry . mul_
{-# INLINEABLE tryMul #-}

-- | Split a 'Fin' of the form @d*x + y@ into @(x, y)@.
divModFin :: SInt m -> Fin (d * m) -> (Fin d, Fin m)
divModFin sm (Fin x) = (Fin d, Fin r)
 where
  (d, r) = divMod x (unSInt sm)

mkChk
  :: HasCallStack
  => SInt n
  -> String
  -> (Fin n -> Fin n -> Maybe (Bool, FinRep))
  -> Fin n -> Fin n -> Fin n
mkChk sn nm op = \x y -> case op x y of
  Just (ok, z) -> if ok then Fin z else outOfRangeError sn nm x y z
  Nothing -> overflowedError sn nm x y
{-# INLINE mkChk #-}

-- | Add and assert the result is in-range.
chkAdd :: HasCallStack => SInt n -> Fin n -> Fin n -> Fin n
chkAdd sn = withFrozenCallStack mkChk sn "chkAdd" (add_ sn)
{-# INLINEABLE chkAdd #-}

-- | Subtract and assert the result is in-range.
chkSub :: HasCallStack => SInt n -> Fin n -> Fin n -> Fin n
chkSub sn = withFrozenCallStack mkChk sn "chkSub" sub_
{-# INLINEABLE chkSub #-}

-- | Multiply and assert the result is in-range.
chkMul :: HasCallStack => SInt n -> Fin n -> Fin n -> Fin n
chkMul sn = withFrozenCallStack mkChk sn "chkMul" (mul_ sn)
{-# INLINEABLE chkMul #-}

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
strengthen :: SInt n -> Fin (n+1) -> Maybe (Fin n)
strengthen sn (Fin x) = if x == unSInt sn then Nothing else Just (Fin x)

-- | 'shiftFin' increases the value and bound of a Fin both by @m@.
shiftFin :: SInt m -> Fin n -> Fin (m+n)
shiftFin sm (Fin x) = Fin (unSInt sm + x)

-- | 'tryUnshiftFin' decreases the value and bound of a Fin both by @m@.
tryUnshiftFin :: SInt m -> SInt n -> Fin (m+n) -> Maybe (Fin n)
tryUnshiftFin sm sn (Fin x) = tryFin sn (x - unSInt sm)

-- | 'unshiftFin' decreases the value and bound of a Fin both by @m@.
unshiftFin :: HasCallStack => SInt m -> SInt n -> Fin (m+n) -> Fin n
unshiftFin sm sn (Fin x) = fin sn (x - unSInt sm)

-- | Deconstructs the given Fin into one of two cases depending where it lies
-- in the given range.
splitFin :: SInt m -> Fin (m + n) -> Either (Fin m) (Fin n)
splitFin sm i = case tryUnembed sm i of
  Just loI -> Left loI
  Nothing -> Right $ unsafeFin $ finToInt i - unSInt sm

-- | Convert to a bigger type.
{-# INLINE embed #-}
embed :: (m <= n) => Fin m -> Fin n
embed (Fin i) = Fin i

-- | Convert to a possibly smaller type.
-- This function fails if the number is too big.
{-# INLINE unembed #-}
unembed :: HasCallStack => SInt n -> Fin m -> Fin n
unembed sn (Fin i) = ufin sn i

-- | Convert to a possibly smaller type or return Nothing if out of bounds.
tryUnembed :: SInt n -> Fin m -> Maybe (Fin n)
tryUnembed sn (Fin i) = tryFin sn i

-- | Given two 'Fin's, returns one the size of the inputs' cartesian product.
--
-- The second argument is the lower-order one, i.e.
--
-- > crossFin @_ @n (x+1) y = n + crossFin @_ @n x y
-- > crossFin @_ @n x (y+1) = 1 + crossFin @_ @n x y
crossFin :: SInt n -> Fin m -> Fin n -> Fin (m * n)
crossFin sn (Fin x) (Fin y) = Fin (x * unSInt sn + y)
