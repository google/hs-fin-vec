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

-- Work around <https://ghc.haskell.org/trac/ghc/ticket/14511>
{-# OPTIONS_GHC -fno-float-in #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- Make Haddock prefer to link to Data.Vec.Short rather than here, and not
-- complain about missing docs for package-internal functions.
{-# OPTIONS_HADDOCK not-home, prune #-}

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE ViewPatterns #-}

-- | An implementation of short vectors.
--
-- The underlying implementation uses the 'SmallArray#' primitive,
-- which lacks the \"card marking\" of 'GHC.Exts.Array#': the upside being
-- that it avoids the overhead of maintaining the card state, the downside
-- being that the garbage collector must scan through the entire array
-- rather than just the parts marked as having changed since the last GC.
-- Using 'SmallArray#' is typically a win for arrays with fewer than 128
-- elements.

-- TODO(b/109667526): add rewrite rules, and maybe builder and view
-- interfaces along the way.
--
-- TODO(b/109668556): revisit all the inline pragmas.
module Data.Vec.Short.Internal where

import Prelude hiding ((++), concat, iterate)

import Control.Applicative (Applicative(..))
import Control.DeepSeq (NFData(rnf))
import Control.Exception(assert)
import qualified Data.Data as D
import Data.Default.Class (Default(..))
import Data.Distributive (Distributive(..))
import Data.Fin.Int (Fin, finToInt, unsafeFin)
import qualified Data.Foldable as F
import Data.Foldable.WithIndex (FoldableWithIndex(..))
import Data.Functor.Apply (Apply(..))
import Data.Functor.Bind (Bind(..))
import Data.Functor.Rep (Representable(..), ifoldMapRep, itraverseRep)
import Data.Functor.WithIndex (FunctorWithIndex(..))
import Data.Traversable.WithIndex (TraversableWithIndex(..))

import Data.Kind (Type)
import qualified Data.List as L (sort, sortBy, sortOn, findIndex)
import Data.Portray (Portray(..), Portrayal(..), strAtom)
import Data.Proxy (Proxy)
import Data.Semigroup (All(..), Any(..), Sum(..), Product(..))
import Data.SInt (SInt(SI#, unSInt), reifySInt, sintVal, subSIntL, divSIntR)
import GHC.Exts (Int(I#), Proxy#, State#, SmallMutableArray#, SmallArray#,
    cloneSmallArray#, copySmallArray#, indexSmallArray#, newSmallArray#,
    sizeofSmallArray#, thawSmallArray#, unsafeFreezeSmallArray#,
    writeSmallArray#, proxy#, coerce)
import qualified GHC.Exts as GHC (IsList(..))
import GHC.Stack (HasCallStack)
import GHC.ST (ST(..), runST)
import GHC.TypeNats
    ( Nat, KnownNat, type (+), type (*)
    , SomeNat(..), natVal', someNatVal
    )
import qualified Test.QuickCheck as QC

#if !MIN_VERSION_base(4,15,0)
import GHC.Natural (naturalToInteger, naturalToInt)
import GHC.Integer (integerToInt)
#endif

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

foldrEnumFin :: SInt n -> (Fin n -> a -> a) -> a -> a
foldrEnumFin (SI# x) c n = go 0
 where
   go i
     | i == x = n
     | otherwise = c (unsafeFin i) (go (i + 1))
{-# INLINE [0] foldrEnumFin #-}

forMFin_ :: Applicative f => SInt n -> (Fin n -> f a) -> f ()
forMFin_ n f = foldrEnumFin n (\i rest -> f i *> rest) (pure ())
{-# INLINE forMFin_ #-}

foldMapFin :: Monoid m => SInt n -> (Fin n -> (# m #)) -> m
foldMapFin (SI# n) f = go 0 mempty
 where
  go i acc
    | i == n = acc
    | otherwise = case f (unsafeFin i) of (# x #) -> go (i + 1) (acc <> x)
{-# INLINE foldMapFin #-}

foldMFin_
  :: Monad m
  => SInt n -> (a -> Fin n -> m a) -> a -> m ()
foldMFin_ n f z = foldrEnumFin n (\i rest a -> f a i >>= rest) (\_ -> pure ()) z
{-# INLINE foldMFin_ #-}

forMFin
  :: Applicative f => SInt n -> (Fin n -> (# f a #)) -> f [a]
forMFin n f = foldrEnumFin n
  (\i -> case f i of (# fx #) -> liftA2 (:) fx)
  (pure [])
{-# INLINE forMFin #-}

-- | Wrap stateful primops which don't return a value.
prim_ :: (State# s -> State# s) -> ST s ()
prim_ f = ST $ \s0 -> case f s0 of s1 -> (# s1, () #)
{-# INLINE prim_ #-}

-- Alas, due to a confluence of problems, we cannot define the combinator:
--
-- > ($#) :: forall (a :: #) (b :: Type) (s :: Type)
-- >      .  (a -> b) -> (State# s -> (# State# s, a #)) -> ST s b
-- > ($#) f p = ST $ \s0 -> case p s0 of (# s1, x #) -> (# s1, f x #)
--
-- While we can hack around most of those problems, and get a version
-- that works for all our use cases, for both ghc-8.0.2 and ghc-8.2.1;
-- the final straw is if we want to keep the code lint clean, HLint-2.1
-- cannot parse the necessary combination of DataKinds and KindSignatures.
-- Thus, we're forced to inline this combinator everywhere we want it.


-- [Note TypeUnsafe]: If the type-unsafe primitives are used without
-- validating their implicit premises, then the 'Nat' type-indices
-- of 'Vec'\/'MutableVec' will become out of sync with the actual
-- 'sizeofSmallArray#'; which in turn invalidates all the safety and
-- correctness guarantees we assumed we could rely on those type-indices
-- to provide.
--
-- [Note MemoryUnsafe]: There are two sorts of memory unsafety introduced
-- by GHC's primops. First is the usual index-out-of-bounds unsafety.
-- In the functions defined here, this sort of unsafety only leaks out as
-- a result of type-safety having been violated. Second is the impurity
-- introduced by 'unsafeFreezeSmallArray#' and 'unsafeThawSmallArray#'
-- if references are used non-linearly; that is, because these primops
-- freeze\/thaw arrays in place, they allow a term which holds the
-- 'MutableVec' view to make mutations which are then visible to terms
-- holding the 'Vec' view, thereby violating the purity of Haskell.


-- | The particular instance of 'GHC.TypeNats.natVal' or 'valueOf' that we want
-- pretty much everywhere.
--
-- TODO(b/109668374): 'valueOf' ends up calling 'fromIntegral' in ways
-- that can overflow 'Int' and lead to /memory-unsafety/. For now,
-- we make sure to use 'nat2int' everywhere (in lieu of 'valueOf'),
-- just in case we end up wanting to fix 'nat2int' or change its type
-- without doing the same to 'valueOf' (for some strange reason).
nat2int :: forall n. KnownNat n => Int
nat2int = valueOf @n
{-# INLINE nat2int #-}
-- /Developer's Note/: We don't use the more obvious\/direct
-- @nat2int = fromInteger . natVal@ definition, because GHC-8.2.1
-- introduces a regression over GHC-8.0.2 whereby 'natVal' calls aren't
-- simplified. <https://ghc.haskell.org/trac/ghc/ticket/14532>  Thus,
-- 'valueOf' goes through an intermediate newtype in order to be able to
-- state a bunch of rewrite rules to manually force 'natVal' to simplify
-- (for an enumerated set of small @n@s).


-- Without these annotations GHC will infer that the @n@ parameter is
-- phantom, which opens the door to bugs by allowing folks to coerce it
-- to a different 'Nat'.
type role Vec nominal representational

-- | @'Vec' n a@ is an element-lazy array of @n@ values of type @a@.
--
-- This comes with a fusion framework, so many intermediate vectors are
-- optimized away, and generally the only Vecs that correspond to actual arrays
-- are those stored in data constructors, accessed multiple times, or appearing
-- as inputs or outputs of non-inlinable functions.  Additionally, some
-- operations that rely on building up a vector incrementally (as opposed to
-- computing each index independently of the others) cannot be fused; notably
-- 'fromList', 'traverse', 'iterate', and 'vscanl'; these will always construct
-- real arrays for their results.
--
-- Most operations are access-strict unless otherwise noted, which means that
-- forcing the result (usually a Vec, but possibly something else, like with
-- 'foldMap') eagerly performs all indexing and drops references to any input
-- arrays.
data Vec (n :: Nat) (a :: Type) = V# (SmallArray# a)
    -- Alas, cannot derive a 'Generic' instance:
    -- \"\"V# must not have exotic unlifted or polymorphic arguments\"\"
    -- Nor can we derive 'Data', but at least that one we can give our
    -- own instance for.

type role MutableVec nominal nominal representational
data MutableVec (s :: Type) (n :: Nat) (a :: Type)
    = MV# (SmallMutableArray# s a)

newMV :: SInt n -> a -> ST s (MutableVec s n a)
newMV (SI# n) = unsafeNewMV n
{-# INLINE newMV #-}

-- TODO(b/109668129): We should be able to replace most of the remaining
-- calls to this function with 'newMV' if we made use of the various
-- combinators in "Utils.NatMath". Would be nice to get that extra
-- type-safety, supposing it doesn't introduce significant performance
-- regressions.

-- | This function is /type-unsafe/: because it assumes the 'Int'
-- argument is in fact the reflection of @n@.
unsafeNewMV :: Int -> a -> ST s (MutableVec s n a)
unsafeNewMV (I# n) x =
    ST $ \s0 ->
    case newSmallArray# n x s0 of { (# s1, sma #) ->
    (# s1, MV# sma #) }
{-# INLINE unsafeNewMV #-}

-- Unsafe version of writeMV, using Int.
-- Each use should be vetted for being in bounds.
unsafeWriteMV :: MutableVec s n a -> Int -> a -> ST s ()
unsafeWriteMV (MV# sma) (I# i) x = prim_ (writeSmallArray# sma i x)
{-# INLINE unsafeWriteMV #-}

writeMV :: MutableVec s n a -> Fin n -> a -> ST s ()
writeMV mv i = unsafeWriteMV mv (finToInt i)
{-# INLINE writeMV #-}

-- | This function is /memory-unsafe/: because it freezes the 'MutableVec'
-- in place. See [Note MemoryUnsafe].
unsafeFreezeMV :: MutableVec s n a -> ST s (Vec n a)
unsafeFreezeMV (MV# sma) =
    ST $ \s0 ->
    case unsafeFreezeSmallArray# sma s0 of { (# s1, sa #) ->
    (# s1, V# sa #) }
{-# INLINE unsafeFreezeMV #-}

-- | Safely thaw a vector, by allocating a new array and copying the
-- elements over. This is both type-safe and memory-safe.
safeThawMV :: Vec n a -> ST s (MutableVec s n a)
safeThawMV (V# sa) =
    ST $ \s0 ->
    case thawSmallArray# sa 0# (sizeofSmallArray# sa) s0 of { (# s1, sma #) ->
    (# s1, MV# sma #) }
{-# INLINE safeThawMV #-}

-- | This function is /type-unsafe/: because it assumes all the integers
-- are in bounds for their respective arrays. It is also /memory-unsafe/,
-- because we don't do any dynamic checks on those integers. We could
-- add such, but have avoided doing so for performance reasons.
-- See [Note TypeUnsafe] and [Note MemoryUnsafe].
--
-- TODO(b/109671227): would assertions /really/ affect the performance
-- significantly?
unsafeCopyVec :: Vec n a -> Int -> MutableVec s m a -> Int -> Int -> ST s ()
unsafeCopyVec (V# src) (I# srcOff) (MV# dst) (I# dstOff) (I# len) =
    prim_ (copySmallArray# src srcOff dst dstOff len)
{-# INLINE[1] unsafeCopyVec #-}

-- Avoid 0 length copies.
{-# RULES "unsafeCopyVec/0" forall v s m d . unsafeCopyVec v s m d 0 = return () #-}

-- | Return a known-length slice of a given vector.
--
-- Since the type is insufficiently specific to ensure memory-safety on its own
-- (because the offset argument is just 'Int'), this needs to perform runtime
-- bounds checks to ensure memory safety.
sliceVec :: Vec n a -> Int -> SInt m -> Vec m a
sliceVec xs@(V# sa) off@(I# o) (SI# len@(I# l)) =
    assert (0 <= off && 0 <= len && len <= vSize xs - off) $
    V# (cloneSmallArray# sa o l)
{-# INLINE sliceVec #-}

{-
-- If we define a @i :<: n@ type whose witnesses are isomorphic to @i@
-- itself, then we can implement these safely by rephrasing the Pi-type
-- @(i :: Fin n) -> t@ as the non-Pi @forall i. i :<: n -> t@. Otherwise
-- we can only do unsafe implementations, like the 'unsafeCopyVec' and
-- 'sliceVec' above. All the ones that use 'Min' will want to add
-- {-# OPTIONS_GHC -fplugin=GHC.TypeLits.Extra.Solver #-} to infer well.

sliceVec
    :: Vec n a
    -> (o :: Fin n)
    -> (m :: Fin (n - o))
    -> ST s (Vec m a)
sliceVec (V# sa) (finToInt -> I# off) (finToInt -> I# len) =
    V# (cloneSmallArray# sa off len)

copyVec
    :: Vec n a
    -> (srcOff :: Fin n)
    -> MutableVec s m a
    -> (dstOff :: Fin m)
    -> (len :: Fin (m - dstOff `Min` n - srcOff))
    -> ST s ()
copyVec (V# src) (finToInt -> I# srcOff) (MV# dst) (finToInt -> I# dstOff) (finToInt -> I# len) =
    prim_ (copySmallArray# src srcOff dst dstOff len)

-- And similarly for 'copySmallMutableArray#', 'cloneSmallArray#',
-- 'cloneSmallMutableArray#', 'freezeSmallArray#', 'thawSmallArray#'.
-}


--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

fetch :: Vec n a -> Fin n -> (# a #)
fetch (V# arr) (finToInt -> I# i) = indexSmallArray# arr i
{-# INLINE fetch #-}

fusibleFetch :: Vec n a -> Fin n -> (# a #)
fusibleFetch = _aIndex . access
{-# INLINE fusibleFetch #-}

-- | Extract the given index from a 'Vec'.
--
-- This is subject to fusion if this is the only use of its input, so code like
-- @fmap f v ! i@ (which might arise due to inlining) will optimize to
-- @f (v ! i)@.
(!) :: Vec n a -> Fin n -> a
(!) xs i = case fusibleFetch xs i of (# x #) -> x
{-# INLINE (!) #-}

-- | Eagerly look up the value at a given position, without forcing the
-- value itself.
--
-- One of the problems with @(!)@ is that it will hold onto the underlying
-- array until the @xs!i@ expression is forced; which is a source of
-- space leaks. However, forcing the @xs!i@ expression will force
-- not only the array lookup but also the value itself; which can be
-- undesirably strict, thereby ruining the compositionality benefits
-- of laziness. The 'indexK' function is designed to overcome those
-- limitations. That is, forcing the expression @indexK xs i k@ will
-- force the array lookup and the @r@ value; thereby leaving it up to
-- @k@ to decide whether or not to force the @a@ before returning @r@.
-- So, for example, if we force @indexK xs i Just@ this will force the
-- array lookup, and wrap the unforced element in the 'Just' constructor.
{- HLINT ignore indexK "Eta reduce" -}
indexK :: Vec n a -> Fin n -> (a -> r) -> r
indexK v i k = case fetch v i of (# x #) -> k x
{-# INLINE indexK #-}

-- | Statically determine the (purported) size\/length of the vector.
-- If you'd rather not require the 'KnownNat' constraint, see 'vSize'.
vLength :: forall n a. KnownNat n => Vec n a -> Int
vLength _ = nat2int @n
{-# INLINE vLength #-}

-- | Return the size of a vector as 'SInt'.
svSize :: Vec n a -> SInt n
-- Note this strongly relies on @n@ matching the actual size of the array: if
-- it didn't, we'd be constructing an invalid 'SInt', which manifests
-- unsafety.  So, it's unsafe for a Vec to have the wrong length.
svSize (V# sa) = SI# (I# (sizeofSmallArray# sa))
{-# INLINE svSize #-}

-- | Dynamically determine the (actual) size\/length of the vector,
-- as a standard term-level 'Int'. If you'd rather obtain @n@ at the
-- type-level, and\/or to prove that the returned value is indeed the
-- @n@ of the input, see 'svSize' and 'withSize' instead. If you'd rather
-- obtain @n@ statically, see 'vLength'.
vSize :: Vec n a -> Int
vSize = unSInt . svSize
{-# INLINE vSize #-}


--------------------------------------------------------------------------------

-- | Dynamically determine the (actual) size\/length of the vector,
-- returning evidence that @n@ is \"known\". If you'd rather obtain @n@
-- as a standard 'Int', see 'vSize'.
withSize :: forall n a r . Vec n a -> (KnownNat n => r) -> r
withSize !xs f = reifySInt (svSize xs) f
{-# INLINE withSize #-}

--------------------------------------------------------------------------------
uninitialized :: a
uninitialized = error "Vec: uninitialized"
{-# NOINLINE uninitialized #-}

-- Unsafe version of createVec, with Int instead of SInt.  Each use
-- should be vetted for size == valueOf @n.  Using this rather than writing out
-- 'SI# at each call site means we have a place to insert assertions more
-- easily.
unsafeCreateVec :: Int -> (forall s. MutableVec s n a -> ST s ()) -> Vec n a
unsafeCreateVec n = createVec (SI# n)
{-# INLINE unsafeCreateVec #-}

createVec
  :: SInt n
  -> (forall s. MutableVec s n a -> ST s ()) -> Vec n a
createVec n action = runST $ do
    mv <- newMV n uninitialized
    action mv
    unsafeFreezeMV mv
{-# INLINE createVec #-}

--------------------------------------------------------------------------------
-- Fusion Internals
--------------------------------------------------------------------------------

-- Fusion framework overview:
--
-- Like with list fusion, the goal is to replace actual intermediate Vec
-- objects with a non-materialized representation.  In this case, that's a
-- function for accessing vector elements by their Fin index, paired with a
-- runtime representation of the Vec length; this representation is called
-- 'Accessor'.  Also like with list fusion, we arrange to rewrite the
-- user-facing API functions to a "fusion form", which converts any input Vecs
-- into Accessors (with 'access'), implements the actual logic in terms of the
-- non-materialized representation, and converts any results into actual Vecs
-- with 'materialize'.  Then a rewrite rule deletes opposing
-- 'access'/'materialize' pairs, eliminating the intermediate allocations
-- wherever this happens.
--
-- To avoid duplicating work computing the Vec elements, we have a soft
-- requirement that a particular call to 'access' must not be used to fetch any
-- index more than once.  Violating this would mean the access/materialize rule
-- can reduce sharing.  No current functions break this rule, but we could
-- imagine adding cases where it's the client's responsibility to make sure
-- elements aren't used multiple times, like a "linear" variant of
-- 'backpermute'.
--
-- Since some Vec functions admit more efficient implementations than you'd get
-- by materializing an Accessor of their contents (e.g. implementing 'take_' by
-- 'unsafeCopyVec'), we adapt another trick from the list fusion library: keep
-- relevant operations on 'Accessor's in symbolic form for one extra simplifier
-- phase, and detect when these operations are still left alone and un-fused,
-- to rewrite them back to specialized implementations.  When we need to do
-- this, we have the specialized implementation under a different name from the
-- user-facing function, write the fusion form as the implementation of the
-- user-facing one with an INLINE pragma, and have an extra rule to bring back
-- the specialized form starting in phase 1.  When we don't need to rewrite
-- back to a specialized implementation (e.g. with 'fmap'), there's simply no
-- specialized implementation provided.
--
-- Why the difference from how list fusion does it (namely, by writing the
-- specialized implementation as the user-facing function and rewriting fusion
-- forms back to the original with phase-controlled RULES)?  I've seen GHC's
-- specialization pass do bad things with that approach, seemingly re-applying
-- rules in the wrong order to the output of specialization, resulting in using
-- element-by-element implementations instead of specialized ones.  By having
-- totally different functions for things like 'append_' and 'pureVec_', we
-- can't accidentally mess them up post-specialization with RULES.
--
-- Here's what happens in each of the GHC simplifier phases:
--
-- Phase [gentle]: GHC isn't willing to inline worker-wrapper'd function bodies
-- yet, so if we tried to use this phase to make real progress, we'd miss
-- things that didn't get exposed to RULES until phase 2.  So, we just bide our
-- time.  Some of our rules are enabled, but we don't change anything after
-- [gentle].
--
-- Phase 2: expand ops into their fusion form with RULES or INLINEs, and do the
-- actual fusion of adjacent ops with the "materialize/access" rule.  Also, do
-- some limited single-op fusion by explicitly merging the fusible form of
-- map-of-map with RULES.  This allows more cases to get rewritten back to
-- specialized implementations in phase 1.
--
-- Phase 1: detect cases that are still just a single op with a specialized
-- implementation available, and rewrite them to use it.  That is, when no
-- fusion actually happened, go back into non-fusion land.
--
-- Phase 0: inline everything and let GHC optimize the things that did get
-- subjected to nontrivial fusion.

data Accessor n a = Accessor
  { _aSize :: SInt n
  , _aIndex :: Fin n -> (# a #)
  }

-- | Convert a 'Vec' into its size and an indexing function.
access :: Vec n a -> Accessor n a
access v = Accessor (svSize v) (fetch v)
{-# INLINE CONLIKE [0] access #-}

-- | Construct an actual 'Vec' from an 'Accessor'.
--
-- Strictness properties: forcing the resulting Vec forces all of the unboxed
-- tuple accesses, so you can make Vecs that are strict in whatever you want by
-- controlling what work goes inside/outside the unboxed tuple construction.
-- Generally this is used to force all of the array accessing so that input
-- 'Vec's are no longer retained after the result is forced; but it's also used
-- to implement element-strict variants of some functions.
materialize :: Accessor n a -> Vec n a
materialize (Accessor n get) = createVec n $ \mv -> forMFin_ n $ \i ->
  case get i of (# x #) -> writeMV mv i x
{-# INLINE [0] materialize #-}

{-# RULES

-- Fuses adjacent Vec ops, keeping everything in Accessor form.
"access/materialize" forall va. access (materialize va) = va

-- Transports coercions out from between access/materialize pairs so they can
-- fuse.
"access/coerce/materialize"
  forall v. access (coerce v) = mapVA coerce (access v)

-- Eliminates no-op copies of a vector.
"materialize/access" forall v. materialize (access v) = v

  #-}

pureVA :: SInt n -> a -> Accessor n a
pureVA n x = Accessor n $ \_ -> (# x #)
{-# INLINE [0] pureVA #-}

mapVA :: (a -> b) -> Accessor n a -> Accessor n b
mapVA f (Accessor n get) = Accessor n $ \i -> case get i of (# x #) -> (# f x #)
{-# INLINE [0] mapVA #-}

mapWithPosVA :: (Fin n -> a -> b) -> Accessor n a -> Accessor n b
mapWithPosVA f (Accessor n get) = Accessor n $
  \i -> case get i of (# x #) -> (# f i x #)
{-# INLINE [0] mapWithPosVA #-}

-- Make an 'Accessor' force its elements before returning them.
seqVA :: Accessor n a -> Accessor n a
seqVA (Accessor n get) = Accessor n $
  \i -> case get i of (# x #) -> x `seq` (# x #)
{-# INLINE [0] seqVA #-}

takeVA
  :: SInt m -> Accessor (m + n) a -> Accessor m a
takeVA m (Accessor _ get) = Accessor m (\i -> get (embedPlus i))
 where
  embedPlus :: Fin m -> Fin (m + n)
  embedPlus = unsafeFin . finToInt
{-# INLINE [0] takeVA #-}

dropVA :: SInt m -> Accessor (m + n) a -> Accessor n a
dropVA m (Accessor mn get) = Accessor (SI# (unSInt mn - unSInt m)) $
  \i -> get (unsafeFin (finToInt i + unSInt m))
{-# INLINE [0] dropVA #-}

revVA :: Accessor n a -> Accessor n a
revVA (Accessor n get) = Accessor n $ \i -> get (complementIt i)
 where
  !nMinus1 = unSInt n - 1

  complementIt :: Fin n -> Fin n
  complementIt = unsafeFin . (nMinus1 -) . finToInt
{-# INLINE [0] revVA #-}

rotVA :: Fin n -> Accessor n a -> Accessor n a
rotVA (finToInt -> !o) (Accessor n get) = Accessor n $
  \(finToInt -> !i) -> get $ unsafeFin $ if i >= o then i - o else nmo + i
 where
  !nmo = unSInt n - o
{-# INLINE [0] rotVA #-}

liftA2VA :: (a -> b -> c) -> Accessor n a -> Accessor n b -> Accessor n c
liftA2VA f (Accessor n getA) (Accessor _ getB) = Accessor n $
  \i -> case getA i of (# a #) -> case getB i of (# b #) -> (# f a b #)
{-# INLINE [0] liftA2VA #-}

foldMapVA :: Monoid m => (a -> m) -> Accessor n a -> m
foldMapVA f (Accessor n get) =
  foldMapFin n (\i -> case get i of (# x #) -> (# f x #))
{-# INLINE [0] foldMapVA #-}

sequenceVA :: Applicative f => Accessor n (f a) -> f (Vec n a)
sequenceVA (Accessor n get) = listVec n <$> forMFin n get
{-# INLINE [0] sequenceVA #-}

-- SInt version of 'splitFin'.  Maybe I'll change the Fin library to provide
-- an SInt API at some point?
splitFinS :: SInt n -> Fin (n + m) -> Either (Fin n) (Fin m)
splitFinS (SI# n) (finToInt -> i)
  | i < n     = Left (unsafeFin i)
  | otherwise = Right (unsafeFin (i - n))

addPosSInt :: SInt n -> SInt m -> SInt (n + m)
addPosSInt (SI# n) (SI# m) =
  let nm = n + m
  in  if nm < 0
        then error "addPosSInt: Int overflow"
        else SI# (n + m)
{-# INLINE addPosSInt #-}

appendVA :: Accessor n a -> Accessor m a -> Accessor (n + m) a
appendVA (Accessor n getN) (Accessor m getM) = Accessor
  (addPosSInt n m)
  (\i -> case splitFinS n i of
    Left i' -> getN i'
    Right i' -> getM i')
{-# INLINE [0] appendVA #-}

--------------------------------------------------------------------------------
-- User-facing API with fusion rules
--------------------------------------------------------------------------------

-- Unsafe version of mkVec, with Int instead of SInt.  Each use should be
-- vetted for s == valueOf @n.  Using this rather than writing out 'SI# and
-- 'unsafeFin' at each call site means we have a place to insert assertions
-- more easily.
unsafeMkVec :: Int -> (Int -> a) -> Vec n a
unsafeMkVec n f = mkVec (SI# n) $ \i -> f (finToInt i)
{-# INLINE unsafeMkVec #-}

-- | Create a known-length vector using a pure function.
--
-- Note if you already have a 'Vec' of the desired length, you can use 'svSize'
-- to get the 'SInt' parameter.
tabulateVec, mkVec :: SInt n -> (Fin n -> a) -> Vec n a
tabulateVec n f = materialize $ Accessor n $ \i -> (# f i #)
mkVec = tabulateVec
{-# INLINE tabulateVec #-}
{-# INLINE mkVec #-}

-- | Element-strict form of 'mkVec': elements are forced when forcing the Vec.
tabulateVec', mkVec' :: SInt n -> (Fin n -> a) -> Vec n a
tabulateVec' n f = materialize $
  Accessor n $ \i -> let x = f i in x `seq` (# x #)
mkVec' = tabulateVec'
{-# INLINE tabulateVec' #-}
{-# INLINE mkVec' #-}

-- Take care: backpermute can reference the same index of the input vector
-- multiple times, so if we subjected the input side to fusion, we'd
-- potentially duplicate work.  It might make sense to make a variant of
-- 'backpermute' that assumes either indices are not duplicated or the
-- computation behind each value is cheap enough to duplicate, but we can't
-- just blindly fuse things into all 'backpermute's.
backpermute :: SInt m -> (Fin m -> Fin n) -> Vec n a -> Vec m a
backpermute m f xs = materialize $ Accessor m $ \i -> fetch xs (f i)
{-# INLINE backpermute #-}

--------------------------------------------------------------------------------
-- N.B., since the same @KnownNat n@ instance is passed to both 'createVecP'
-- and 'enumFinP', this will be memory-safe even if the @KnownNat n@
-- instance is illegitimate (e.g., by using 'blackMagic' unsafely).
-- An illegitimate 'KnownNat' instance would only compromise type-safety:
-- since it'd mean that the actual length of the resulting 'SmallArray#'
-- differs from the @n@ the 'Vec' claims it has.

-- | Create a vector of the specified length from a list. If @n < length xs@
-- then the suffix of the vector will be filled with 'uninitialized'
-- values. If @n > length xs@ then the suffix of @xs@ won't be included
-- in the vector. Either way, this function is both type-safe and memory-safe.
listVec :: SInt n -> [a] -> Vec n a
listVec n xs = createVec n $ \mv -> ($ xs) $ foldrEnumFin n
  (\i rest xs' -> case xs' of
      [] -> writeMV mv i uninitialized >> rest []
      (x:xs'') -> writeMV mv i x >> rest xs'')
  (\_ -> return ())
{-# INLINE listVec #-}


-- | Convert a list to a vector of the same length.
withVec :: [a] -> (forall n. KnownNat n => Vec n a -> r) -> r
withVec xs f = case someNatVal . fromIntegral $ length xs of
    SomeNat (_ :: Proxy n) -> f (listVec (sintVal @n) xs)
{-# INLINABLE withVec #-}


-- | Convert a list to a vector, given a hint for the length of the list.
-- If the hint does not match the actual length of the list, then the
-- behavior of this function is left unspecified. If the hint does not
-- match the desired @n@, then we throw an error just like 'fromList'.
-- For a non-errorful version, see 'withVec' instead.
fromListN :: forall n a. (HasCallStack, KnownNat n) => Int -> [a] -> Vec n a
fromListN l xs
    | l == n    = listVec sn xs
    | otherwise = error $ "Vec.fromListN: " <> show l <> " /= " <> show n
    where
    !sn@(SI# n) = sintVal
{-# INLINABLE fromListN #-}


-- | Convert a list to a vector, throwing an error if the list has the
-- wrong length.
-- Note: Because this walks @xs@ to check its length, this cannot be
-- used with the list fusion optimization rules.
fromList :: forall n a. (HasCallStack, KnownNat n) => [a] -> Vec n a
fromList xs
    | n `eqLength` xs = listVec sn xs
    | otherwise       = error $ "Vec.fromList: length /= " <> show n
    where
    !sn@(SI# n) = sintVal
{-# INLINABLE fromList #-}


-- TODO(b/109757264): move this out of library into @ListUtils.hs@
-- | An implementation of @n == length xs@ which short-circuits
-- once it can determine the answer, rather than necessarily recursing
-- through the entire list to compute its length.
eqLength :: Int -> [a] -> Bool
eqLength 0 []     = True
eqLength 0 (_:_)  = False -- too long
eqLength _ []     = False -- too short
eqLength n (_:xs) = eqLength (n - 1) xs


-- To support -XOverloadedLists
instance KnownNat n => GHC.IsList (Vec n a) where
    type Item (Vec n a) = a
    fromListN = fromListN
    fromList  = fromList  -- Not subject to list fusion optimizations
    toList    = F.toList

--------------------------------------------------------------------------------
-- | Claim that 'vecConstr' is the only data-constructor of 'Vec'.
vecDataType :: D.DataType
vecDataType = D.mkDataType "Vec.Vec" [vecConstr]

-- | Treat the 'fromList' function as a data-constructor for 'Vec'.
vecConstr :: D.Constr
vecConstr = D.mkConstr vecDataType "fromList" [] D.Prefix

-- The 'KnownNat' constraint is necessary for 'fromList'.
instance (KnownNat n, D.Data a) => D.Data (Vec n a) where
    toConstr   _ = vecConstr
    dataTypeOf _ = vecDataType
    gfoldl  app pur v = pur fromList `app` F.toList v
    gunfold app pur c
        | D.constrIndex c == 1 = app (pur fromList)
        | otherwise            = error "gunfold@Vec: invalid constrIndex"

--------------------------------------------------------------------------------
instance Show a => Show (Vec n a) where
    showsPrec p xs = showParen (p >= precedence)
        $ showString "fromListN "
        . shows (vSize xs)
        . showString " "
        . shows (F.toList xs)

instance (KnownNat n, Read a) => Read (Vec n a) where
    readsPrec p = readParen (p >= precedence) $ \s ->
        [ assertSize (length ls) (fromListN n ls, s''')
        | ("fromListN", s') <- lex s
        , (n, s'') <- readsPrec precedence s'
        , (ls, s''') <- assertSize n readsPrec precedence s''
        ]
        where
            assertSize :: Int -> b -> b
            assertSize n x = if n /= nat2int @n
                then error $ "Can't read a Vec with " <> show n <>
                    " elements into a type `Vec " <> show (nat2int @n) <>
                    "`"
                else x

-- Vec is being shown as a function application which has precedence 10. Thus,
-- if we are already in function application context or one that binds even
-- tightlier (i.e. with higher precedence) we need to wrap the expression in
-- parantheses.
precedence :: Int
precedence = 10

instance Portray a => Portray (Vec n a) where
  portray xs = Apply (strAtom "fromListN")
    [portray (vSize xs), portray $ F.toList xs]

instance NFData a => NFData (Vec n a) where
    rnf !xs = foldMapFin (svSize xs) $
        \i -> case indexK xs i rnf of () -> (# () #)
    {-# INLINE rnf #-}

-- | Point-wise @(<>)@.
instance Semigroup a => Semigroup (Vec n a) where
    (<>) = liftF2 (<>)

-- | Point-wise @mempty@.
instance (KnownNat n, Monoid a) => Monoid (Vec n a) where
    mempty = pure mempty

instance forall a n. (QC.Arbitrary a, KnownNat n) => QC.Arbitrary (Vec n a)
    where
    -- While we could get rid of the intermediate list by digging into
    -- how 'Gen' works under the hood, the benefit doesn't seem worth it.
    arbitrary = listVec sn <$> QC.vectorOf n QC.arbitrary
      where
        !sn@(SI# n) = sintVal

    -- If @a@ admits too many ways to shrink, we might prefer to
    -- interleave the @shrink(xs!i)@ lists, rather than concatenating
    -- them as list comprehension will.
    shrink xs =
        [ upd i xs x'
        | i <- foldrEnumFin sn (:) [], x' <- indexK xs i QC.shrink
        ]
      where
        !sn = svSize xs

-- | Safely construct a new vector that differs only in one element.
-- This is inefficient, and only intended for internal use.
upd :: Fin n -> Vec n a -> a -> Vec n a
upd i xs x = runST $ do
    mv <- safeThawMV xs
    writeMV mv i x
    unsafeFreezeMV mv
{-# INLINE upd #-}

instance (Show a) => QC.CoArbitrary (Vec n a) where
    coarbitrary = QC.coarbitraryShow

instance (KnownNat n, Num a) => Num (Vec n a) where
    (+) = liftA2 (+)
    (*) = liftA2 (*)
    (-) = liftA2 (-)
    abs = fmap abs
    signum = fmap signum
    negate = fmap negate
    fromInteger = pure . fromInteger

instance (KnownNat n, Default a) => Default (Vec n a) where
    def = pure def

instance Eq a => Eq (Vec n a) where
    xs == ys = getAll $ foldMap All $ liftF2 (==) xs ys
    xs /= ys = getAny $ foldMap Any $ liftF2 (/=) xs ys

instance Ord a => Ord (Vec n a) where
    compare xs ys = F.fold $ liftF2 compare xs ys

mapVec :: (a -> b) -> Vec n a -> Vec n b
mapVec f = materialize . mapVA f . access
{-# INLINE mapVec #-}

{-# RULES

"mapVec/merge" forall f g va. mapVA f (mapVA g va) = mapVA (f . g) va
"mapVec/coerce" [1]  forall v. materialize (mapVA coerce (access v)) = coerce v
"mapVec/id" mapVA (\x -> x) = id

  #-}

instance Functor (Vec n) where
    fmap = mapVec

    -- This is just 'pureVec' getting its size from an existing 'Vec'.  Since
    -- the output is independent of the values in the input, we can tie into
    -- the fusion framework to get the size of the input Vec, and still
    -- potentially use the specialized form of 'pureVec'.
    x <$ v = pureVec (_aSize (access v)) x
    {-# INLINE (<$) #-}

-- TODO: Implement these instances via more efficient built-in functions.

instance FunctorWithIndex (Fin n) (Vec n) where imap = mapWithPos

instance KnownNat n => FoldableWithIndex (Fin n) (Vec n) where
  ifoldMap = ifoldMapRep

instance KnownNat n => TraversableWithIndex (Fin n) (Vec n) where
  itraverse = itraverseRep

-- | An element-strict version of 'fmap'.
map' :: (a -> b) -> Vec n a -> Vec n b
map' f = materialize . seqVA . mapVA f . access
{-# INLINE map' #-}

-- | A variant of 'fmap' that provides the index in addition to the element.
mapWithPos :: (Fin n -> a -> b) -> Vec n a -> Vec n b
mapWithPos f = materialize . mapWithPosVA f . access
{-# INLINE mapWithPos #-}

-- | Pair each element of a 'Vec' with its index.
--
-- You can also use 'mapWithPos', but there should be no harm in using this
-- because the fusion framework should optimize away the intermediate Vec.
withPos :: Vec n a -> Vec n (Fin n, a)
withPos = mapWithPos (,)
{-# INLINE withPos #-}

-- | An element-strict version of 'mapWithPos'.
mapWithPos' :: (Fin n -> a -> b) -> Vec n a -> Vec n b
mapWithPos' f = materialize . seqVA . mapWithPosVA f . access
{-# INLINE mapWithPos' #-}

pureVec_, pureVec :: SInt n -> a -> Vec n a
pureVec_ n x = runST $ newMV n x >>= unsafeFreezeMV
{-# NOINLINE pureVec_ #-}

pureVec = \n x -> materialize (pureVA n x)
{-# INLINE pureVec #-}

{-# RULES

"pureVec/spec" [1] forall n x. materialize (pureVA n x) = pureVec_ n x

"mapVA/pureVA" forall f n x. mapVA f (pureVA n x) = pureVA n (f x)

  #-}

liftA2Vec :: (a -> b -> c) -> Vec n a -> Vec n b -> Vec n c
liftA2Vec f as bs = materialize (liftA2VA f (access as) (access bs))
{-# INLINE liftA2Vec #-}

instance Apply (Vec n) where
  liftF2 = liftA2Vec
  {-# INLINE liftF2 #-}

instance KnownNat n => Applicative (Vec n) where
  pure = pureVec sintVal
  {-# INLINE pure #-}

  liftA2 = liftA2Vec
  {-# INLINE liftA2 #-}

  (<*>) = liftA2Vec ($)
  {-# INLINE (<*>) #-}

  _  *> ys = ys
  {-# INLINE (*>) #-}

  xs <* _  = xs
  {-# INLINE (<*) #-}

instance Bind (Vec n) where
  xs >>- f = materialize (case access xs of
    Accessor n get -> Accessor n (\i -> case get i of
      (# x #) -> f x `fusibleFetch` i))
  {-# INLINE (>>-) #-}

instance KnownNat n => Monad (Vec n) where (>>=) = (>>-)

-- | A truly lazy version of @liftA2@.
--
-- As opposed to the actual @liftA2@ it does not inspect the arguments which
-- makes it possible it to use in code that has lazy knot-tying.
liftA2Lazy :: KnownNat n => (a -> b -> c) -> Vec n a -> Vec n b -> Vec n c
liftA2Lazy f xs ys = tabulate $ \i ->
    indexK xs i $ \x ->
    indexK ys i $ \y ->
      f x y

--------------------------------------------------------------------------------
-- | > unsafeIndexK xs i === indexK xs (unsafeFin i)
--
-- TODO(b/109672429): try to get rid of all the uses of this function,
-- and other uses of 'unsafeFin' as well.
unsafeIndexK :: Vec n a -> Int -> (a -> r) -> r
unsafeIndexK (V# sa) (I# i) k = case indexSmallArray# sa i of (# x #) -> k x
{-# INLINE unsafeIndexK #-}

instance Foldable (Vec n) where
    length = vSize
    {-# INLINE length #-}

    null = (0 ==) . length
    {-# INLINE null #-}

    foldMap f = foldMapVA f . access
    {-# INLINE foldMap #-}

    fold = foldMapVA id . access
    {-# INLINE fold #-}

    foldr f acc0 = \v ->
      let Accessor n get = access v
      in  foldrEnumFin n
            (\i acc -> case get i of (# x #) -> f x acc)
            acc0
    {-# INLINE foldr #-}

    foldr' f acc0 = \v ->
      let !(Accessor n get) = access v
          go !i !acc
            | i < 0 = acc
            | otherwise =
                case get (unsafeFin i) of (# x #) -> go (i - 1) (f x acc)
      in  go (unSInt n - 1) acc0
    {-# INLINE foldr' #-}

    foldl f acc0 = \v ->
      let !(Accessor n get) = access v
          go !i
            | i < 0 = acc0
            | otherwise = case get (unsafeFin i) of (# x #) -> f (go (i - 1)) x
      in  go (unSInt n - 1)
    {-# INLINE foldl #-}

    foldl' f acc0 = \v ->
      let !(Accessor (unSInt -> !n) get) = access v
          go !i !acc
            | i >= n = acc
            | otherwise =
                case get (unsafeFin i) of (# a #) -> go (i+1) (f acc a)
      in  go 0 acc0
    {-# INLINE foldl' #-}

    foldr1 f = \v ->
      case access v of
        Accessor (subtract 1 . unSInt -> lMinus1) get
          | lMinus1 < 0 -> error "foldr1@Vec: empty list"
          | otherwise ->
              let !(# z #) = get (unsafeFin lMinus1)
                  go !i | i >= lMinus1 = z
                        | otherwise =
                            let !(# x #) = get (unsafeFin i)
                            in  f x (go (i + 1))
              in  go 0
    {-# INLINE foldr1 #-}

    foldl1 f = \v ->
      case access v of
        Accessor (subtract 1 . unSInt -> lMinus1) get
          | lMinus1 < 0 -> error "foldl1@Vec: empty list"
          | otherwise ->
              let !(# z #) = get (unsafeFin (0 :: Int))
                  go !i | i <= 0 = z
                        | otherwise =
                            let !(# x #) = get (unsafeFin i)
                            in  f (go (i - 1)) x
              in  go lMinus1
    {-# INLINE foldl1 #-}

    -- The INLINE declarations here are important to fusion: without it, GHC
    -- fully optimizes the default implementation (which is identical to this
    -- one) when compiling this module, and exposes the post-optimized
    -- unfolding.  Then when we use 'sum', the thing that gets inlined is
    -- already post-fusion, and no fusion can happen.
    --
    -- With the INLINE, GHC exposes (the Core desugaring of) this exact term as
    -- the unfolding, and 'sum' can participate in fusion.

    sum = coerce . foldMap Sum
    {-# INLINE sum #-}

    product = coerce . foldMap Product
    {-# INLINE product #-}

    minimum = foldr1 min
    {-# INLINE minimum #-}

    maximum = foldr1 max
    {-# INLINE maximum #-}

    elem x = coerce . foldMap (Any . (== x))
    {-# INLINE elem #-}

-- | A fusion of 'F.toList' and 'withPos' to avoid allocating the
-- intermediate array. This is a \"good producer\" for list fusion.
--
-- TODO(awpr): this shouldn't be necessary with the fusion framework in place.
toListWithPos :: Vec n a -> [(Fin n, a)]
toListWithPos = F.toList . withPos
{-# INLINE toListWithPos #-}

-- | A fusion of 'foldr' and 'withPos', to avoid allocating the
-- intermediate array.
--
-- TODO(awpr): this shouldn't be necessary with the fusion framework in place.
foldrWithPos :: (Fin n -> a -> b -> b) -> b -> Vec n a -> b
foldrWithPos f z = foldr (uncurry f) z . withPos
{-# INLINE foldrWithPos #-}

-- | A variant of 'F.traverse_' which provides the positions of a vector,
-- rather than the elements in those positions.
traversePos_ :: Applicative m => (Fin n -> m ()) -> Vec n a -> m ()
traversePos_ f xs = F.traverse_ f (mkVec (_aSize (access xs)) id)
{-# INLINE traversePos_ #-}

-- | Flipped version of 'traversePos_'.
forPos_ :: Applicative m => Vec n a -> (Fin n -> m ()) -> m ()
forPos_ = flip traversePos_
{-# INLINE forPos_ #-}

-- | A variant of 'F.traverse_' which provides both the positions and the
-- elements at those positions.
traverseWithPos_ :: Applicative m => (Fin n -> a -> m ()) -> Vec n a -> m ()
traverseWithPos_ f = F.traverse_ (uncurry f) . withPos
{-# INLINE traverseWithPos_ #-}

-- TODO(b/109671009): better name for this.
-- | Flipped version of 'traverseWithPos_'.
forVecWithPos_ :: Applicative m => Vec n a -> (Fin n -> a -> m ()) -> m ()
forVecWithPos_ = flip traverseWithPos_
{-# INLINE forVecWithPos_ #-}

traverseVec :: Applicative f => (a -> f b) -> Vec n a -> f (Vec n b)
traverseVec f = sequenceVA . mapVA f . access
{-# INLINE traverseVec #-}

-- TODO(b/109674103): for linear-use applicatives ('IO', 'Maybe',...) we
-- can give a more efficient definition.
instance Traversable (Vec n) where
    traverse = traverseVec
    {-# INLINE traverse #-}

-- We don't bother defining 'collect', since anything other than the
-- default instance would be egregiously inefficient if the function
-- actually allocates vectors, since we'd end up allocating @n@ identical
-- copies of every vector in the @f@ structure! If, however, we were
-- to have a bunch of fusion rules for things like @mkVec f ! i = f i@;
-- then, it might be worth defining 'collect' directly, since we could
-- avoid allocating any of the intermediate arrays!
--
-- TODO(b/109674103): for linear-use functors ('IO', 'Maybe',...) we
-- can give a more efficient definition.
instance KnownNat n => Distributive (Vec n) where
    distribute fxs = tabulate $ \i -> fmap (! i) fxs
    {-# INLINE distribute #-}

instance KnownNat n => Representable (Vec n) where
    type Rep (Vec n) = Fin n

    tabulate = tabulateVec sintVal
    {-# INLINE tabulate #-}

    index = (!)
    {-# INLINE index #-}

-- | 'Prelude.scanl', for 'Vec'.
vscanl :: KnownNat (1 + n) => (b -> a -> b) -> b -> Vec n a -> Vec (1 + n) b
-- TODO(awpr): we can probably subject the input Vec to fusion here.
vscanl f b = listVec sintVal . scanl f b . F.toList


--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- List like ops and their isomorphisms.

-- | A zero-length 'Vec' of any element type.
nil :: Vec 0 a
-- Note: in the C-- code, this is a single global thunk with a polymorphic
-- type; we won't re-create it separately for different types.  The NOINLINE
-- serves to ensure we just reference the thunk rather than inlining the code
-- that builds it.  This blocks fusion, but we have another trick: rewrite any
-- materialize @0 to nil.  Then anything that would've fused with this will no
-- longer reference it at all.
nil = mkVec sintVal (\i -> i `seq` error "Vec.nil: the impossible happened")
{-# NOINLINE nil #-}

{-# RULES

-- Note this matches only zero-length vectors because the LHS type is unified
-- with the RHS type.
"materialize@0" forall va. materialize va = nil

  #-}

----------------

-- | Concatenate two 'Vec's.
infixr 5 ++
append_, (++) :: Vec n a -> Vec m a -> Vec (n + m) a
append_ xs ys = runST $ do
    let !n = vSize xs
        !m = vSize ys
    zs <- unsafeNewMV (n + m) uninitialized
    unsafeCopyVec xs 0 zs 0 n
    unsafeCopyVec ys 0 zs n m
    unsafeFreezeMV zs
{-# NOINLINE append_ #-}

(++) = \xs ys -> materialize (appendVA (access xs) (access ys))
{-# INLINE (++) #-}

{-# RULES

"++/spec" [1]
  forall xs ys. materialize (appendVA (access xs) (access ys)) = xs `append_` ys

  #-}

-- TODO(b/109675695): may want other variants of this operational-function
-- with different types.
-- TODO: might as well simply call the underlying
-- 'thawSmallArray#' directly, instead of passing through
-- 'sliceVec'... ne? (i.e., to avoid the dynamic bounds checks)
take_ :: SInt m -> Vec (m + n) a -> Vec m a
take_ m xs = sliceVec xs 0 m
{-# NOINLINE take_ #-}
-- TODO(awpr): fusion behaves poorly here because of Core-level casts arising
-- from unifying @m + n@ with some other Nat: we get
-- @materialize (takeVA m (access ((materialize _) `cast` <Co:1>)))@, which
-- can't match the access/materialize rule.  The @cast@ comes from converting
-- the equal-but-not-syntactically-identical types @Vec (m + n) a@ and
-- @Vec _something a@ using the coercion @_something ~N# (m + n)@.  If we
-- define this with inequality constraints instead,
-- @take_ :: (m <= n) => SInt m -> Vec n a -> Vec m a@, then there's no need
-- for a cast there; @n@ and @m@ are just unified away to be identical to the
-- sizes of the input and output vectors.

{-# RULES

"take_/spec" [1] forall m xs. materialize (takeVA m (access xs)) = take_ m xs

  #-}

-- TODO(b/109675695): may want other variants of this operational-function
-- with different types.
drop_ :: forall m n a. SInt m -> Vec (m + n) a -> Vec n a
drop_ m xs =
  sliceVec xs (unSInt m) $
  svSize xs `subSIntL` m
{-# NOINLINE drop_ #-}
-- TODO(awpr): as with 'take_', casts are causing trouble here.  Consider
-- messing with the type signature to avoid them.

{-# RULES

"drop_/spec" [1] forall m xs. materialize (dropVA m (access xs)) = drop_ m xs

  #-}

-- TODO(b/109675695): may want other variants of this operational-function
-- with different types.
split
  :: forall m n a. SInt m -> Vec (m + n) a -> (Vec m a, Vec n a)
split m xs =
  let va = access xs
  in  (materialize (takeVA m va), materialize (dropVA m va))
{-# INLINE split #-}

-- TODO(awpr): fusion for 'concat' and 'reshape'?

-- | Concatenate a nested 'Vec' into one longer 'Vec'.
concat :: forall m n a. Vec n (Vec m a) -> Vec (n * m) a
concat xs =
  let !n = vSize xs
  in  if n == 0 then
        -- Outer size is 0, return the empty array
        unsafeCreateVec 0 $ \ _ -> return ()
      else
          let !m = unsafeIndexK xs 0 vSize  -- We know the size is > 0.
          in  unsafeCreateVec (n * m) $ \ marr ->
                F.forM_ [0..n-1] $ \ i ->
                  unsafeIndexK xs i $ \ ys ->  -- i is [0..n-1], so in bounds.
                    unsafeCopyVec ys 0 marr (i * m) m
{-# INLINE concat #-}

-- | Turn a vector into a vector of vector by chunking it.
reshape :: SInt m -> Vec (n * m) a -> Vec n (Vec m a)
reshape m =
  let !m' = unSInt m
  in  \xs ->
        mkVec (svSize xs `divSIntR` m) (\i -> sliceVec xs (finToInt i * m') m)
{-# INLINE reshape #-}

-- | Map each element of a 'Vec' to a (same-sized) sub-'Vec' of the result.
concatMap :: forall m n a b. (a -> Vec m b) -> Vec n a -> Vec (n * m) b
concatMap f = concat . fmap f
{-# INLINE concatMap #-}


-- | Generate a Vec by repeated application of a function.
--
-- > toList (Vec.iterate @n f z) === take (valueOf @n) (Prelude.iterate f z)
iterate :: forall n a. KnownNat n => (a -> a) -> a -> Vec n a
iterate f z =
    createVec sintVal $ \mv ->
       foldMFin_ sintVal (\x i -> f x <$ writeMV mv i x) z
{-# INLINE iterate #-}


-- | A strict version of 'iterate'.
iterate' :: forall n a. KnownNat n => (a -> a) -> a -> Vec n a
iterate' f !z =
    createVec sintVal $ \mv ->
        foldMFin_ sintVal (\x i -> f x <$ (writeMV mv i $! x)) z
{-# INLINE iterate' #-}


-- | Return a copy of the array with elements in the reverse order.
rev :: Vec n a -> Vec n a
rev = materialize . revVA . access
{-# INLINE rev #-}


-- | Rotate a vector right by @i@ positions.
--
-- @rot 1 [x, y, z] = [z, x, y]@
rot, rot_ :: Fin n -> Vec n a -> Vec n a
rot_ o' xs = createVec (svSize xs) $ \mv -> do
  let o = finToInt o'
      nmo = vSize xs - o
  unsafeCopyVec xs nmo mv 0 o
  unsafeCopyVec xs 0   mv o nmo
{-# NOINLINE rot_ #-}

rot o = \v -> materialize (rotVA o (access v))
{-# INLINE rot #-}

{-# RULES

"rot/spec" [1] forall o v. materialize (rotVA o (access v)) = rot_ o v

  #-}

-- | Return a vector with all elements of the type in ascending order.
viota :: KnownNat n => Vec n (Fin n)
viota = mkVec sintVal id
{-# INLINE viota #-}

-- | One variant of the cross product of two vectors.
cross :: Vec m a -> Vec n b -> Vec n (Vec m (a, b))
cross xs = fmap (\y -> fmap (, y) xs)
{-# INLINE cross #-}

-- TODO: the concatenated version.
-- cross :: Vec m a -> Vec n b -> Vec (m * n) (a, b)
--
-- TODO: the transposed nested version.
-- cross :: Vec m a -> Vec n b -> Vec m (Vec n (a, b))

--------------------------------

-- Element insertion and removal.

-- TODO(awpr): fusion implementations of insert and remove?

-- Unsafe version of insert.  Assumes i < valueOf @(n+1)
-- Statically determined 0 length copies are removed by a RULE.
unsafeInsert :: Int -> a -> Vec n a -> Vec (n+1) a
unsafeInsert i xi xs =
  let !n = vSize xs
  in  unsafeCreateVec (n+1) $ \ mv -> do
        -- Explicitly: @mv[0..i-1] := xs[0..i-1]@
        unsafeCopyVec xs 0 mv 0 i
        -- Explicitly: @mv[i] := xi@
        unsafeWriteMV mv i xi
        -- Explicitly: @mv[i+1..n] := xs[i..n-1]@
        unsafeCopyVec xs i mv (i + 1) (n - i)

-- | Insert an element at the given position in a vector.
-- O(n)
insert :: Fin (n+1) -> a -> Vec n a -> Vec (n+1) a
insert i = unsafeInsert (finToInt i)

-- Unsafe version of remove.  Assumes i < valueOf @(n+1)
-- Statically determined 0 length copies are removed by a RULE.
unsafeRemove :: Int -> Vec (n+1) a -> Vec n a
unsafeRemove i xs =
  let !np1 = vSize xs
  in  unsafeCreateVec (np1 - 1) $ \ mv -> do
        -- Explicitly: @mv[0..i-1] := xs[0..i-1]@
        unsafeCopyVec xs 0 mv 0 i
        -- Explicitly: @mv[i..n-1] := xs[i+1..n]@
        unsafeCopyVec xs (i+1) mv i (np1 - 1 - i)

-- | Remove an element at the given position in a vector.
-- O(n)
remove :: Fin (n+1) -> Vec (n+1) a -> Vec n a
remove i = unsafeRemove (finToInt i)

--------------------------------

-- | Sort a 'Vec' according to its 'Ord' instance.
vsort :: Ord a => Vec n a -> Vec n a
vsort xs = listVec (svSize xs) . L.sort . F.toList $ xs

-- | Sort a 'Vec' with a given comparison function.
vsortBy :: (a -> a -> Ordering) -> Vec n a -> Vec n a
vsortBy f xs = listVec (svSize xs). L.sortBy f . F.toList $ xs

-- | Sort a 'Vec' with a given sort-key function.
vsortOn :: Ord b => (a -> b) -> Vec n a -> Vec n a
vsortOn f xs = listVec (svSize xs). L.sortOn f . F.toList $ xs


--------------------------------
-- | Transpose a vector of vectors.
vtranspose :: forall m n a
            . KnownNat m
           => Vec n (Vec m a) -> Vec m (Vec n a)
vtranspose xs =
  let !s = vSize xs
      !t = valueOf @m
  in  unsafeMkVec t $ \ i ->
        -- s is the size of the outer vector, i.e. valueOf @n
        unsafeMkVec s $ \ j ->
          unsafeIndexK xs j $ \ v -> unsafeIndexK v i id

--------------------------------

-- | Find the index of the first element, if any, that satisfies a predicate.
vfindIndex :: (a -> Bool) -> Vec n a -> Maybe (Fin n)
vfindIndex p = fmap unsafeFin . L.findIndex p . F.toList

--------------------------------

-- | Create a singleton 'Vec'.
vec1 :: a -> Vec 1 a
vec1 = pure
{-# INLINE vec1 #-}

-- | Create a 'Vec' from two elements.
vec2 :: a -> a -> Vec 2 a
vec2 x0 x1 = mkVec sintVal $ \i -> case finToInt i of
  0 -> x0
  1 -> x1
  _ -> error "Impossible: Fin out of range"
{-# INLINE vec2 #-}

-- | Create a 'Vec' from three elements.
vec3 :: a -> a -> a -> Vec 3 a
vec3 x0 x1 x2 = mkVec sintVal $ \i -> case finToInt i of
  0 -> x0
  1 -> x1
  2 -> x2
  _ -> error "Impossible: Fin out of range"
{-# INLINE vec3 #-}

-- | Create a 'Vec' from four elements.
vec4 :: a -> a -> a -> a -> Vec 4 a
vec4 x0 x1 x2 x3 = mkVec sintVal $ \i -> case finToInt i of
  0 -> x0
  1 -> x1
  2 -> x2
  3 -> x3
  _ -> error "Impossible: Fin out of range"
{-# INLINE vec4 #-}

-- | Create a 'Vec' from six elements.
vec6 :: a -> a -> a -> a -> a -> a ->Vec 6 a
vec6 x0 x1 x2 x3 x4 x5 = mkVec sintVal $ \i -> case finToInt i of
  0 -> x0
  1 -> x1
  2 -> x2
  3 -> x3
  4 -> x4
  5 -> x5
  _ -> error "Impossible: Fin out of range"
{-# INLINE vec6 #-}

-- | Create a 'Vec' from eight elements.
vec8 :: a -> a -> a -> a -> a -> a -> a -> a -> Vec 8 a
vec8 x0 x1 x2 x3 x4 x5 x6 x7 = mkVec sintVal $ \i -> case finToInt i of
  0 -> x0
  1 -> x1
  2 -> x2
  3 -> x3
  4 -> x4
  5 -> x5
  6 -> x6
  7 -> x7
  _ -> error "Impossible: Fin out of range"
{-# INLINE vec8 #-}

---------------------------

-- | Get the value of a statically known natural number.
{-# INLINE valueOf #-}
valueOf :: forall (n :: Nat) (i :: Type) . (KnownNat n, Num i) => i
valueOf = fromIntegral $ natVal' (proxy# :: Proxy# n)

#if !MIN_VERSION_base(4,15,0)
-- base-4.15.0.0 removed naturalToInt.
{-# RULES "integerToInt . naturalToInteger => naturalToInt"
  forall a. integerToInt (naturalToInteger a) =
      let !(I# i) = naturalToInt a
      in i
  #-}
#endif

-- | Modify the given index of a 'Vec'.
overIx :: Fin n -> (a -> a) -> Vec n a -> Vec n a
overIx i f v = runST $ do
  mv <- safeThawMV v
  indexK v i (writeMV mv i . f)
  unsafeFreezeMV mv
{-# INLINE overIx #-}
