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

-- | Lenses and related optics for 'Vec's.

-- Work around <https://ghc.haskell.org/trac/ghc/ticket/14511>
{-# OPTIONS_GHC -fno-float-in #-}
{-# OPTIONS_GHC -Wno-orphans #-}

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Vec.Short.Lens
    (
    -- ** List-based lenses
      list
    -- ** Arity-based lenses
    , paired

    -- * List-like operators
    -- ** Constructor views
    -- *** The cons view
    , consed
    -- *** The snoc view
    , snoced
    -- ** Operator views
    -- *** The append view
    , chopped
    -- *** The concat view
    , subVecs
    -- *** The reverse view
    , reversed
    -- *** The transposition view
    , vtransposed

    -- * Misc lenses
    , midElem, ixElem, ix
    , sliced
    , rotated
    , vdiagonal
    ) where

import Prelude hiding ((++), concat, concatMap, iterate)

import qualified Data.Foldable as F
import GHC.ST (runST)
import GHC.TypeLits (KnownNat, type (+), type (<=), type (-))
import qualified GHC.TypeLits

import Control.Lens (Iso, Lens', iso, lens, from, swapped)

import Data.Fin.Int.Explicit (Fin, complementFin, finToInt, unsafeFin)
import Data.SInt (sintVal, unSInt)
import Data.Vec.Short.Internal

#if !MIN_VERSION_lens(5,0,0)
import qualified Control.Lens as L
import Data.Foldable.WithIndex (FoldableWithIndex(..))
import Data.Traversable.WithIndex (TraversableWithIndex(..))
#endif

--------------------------------------------------------------------------------

-- | A list (of the right length) is isomorphic to a vector.
-- The list-to-vector direction is partial.
list :: (KnownNat n) => Iso (Vec n a) (Vec n b)
                            [a]       [b]
list = iso F.toList (fromList sintVal)

--------------------------------------------------------------------------------

-- | Lens on a single element.
ix :: Fin n -> Lens' (Vec n a) a
ix i = i `seq` lens (! i) (upd i)
{-# INLINE ix #-}

----------------

-- | An isomorphism with an element added at the beginning of a vector.
consed :: Iso (a, Vec n a)    (b, Vec m b)
              (Vec (n + 1) a) (Vec (m + 1) b)
consed = from (unsafeIxElem (const 0))

-- | An isomorphism with an element added at the end of a vector.
snoced :: Iso (Vec n a, a)    (Vec m b, b)
              (Vec (n + 1) a) (Vec (m + 1) b)
snoced = from (unsafeIxElem id . swapped)

-- | Isomorphism between a vector with and without its middle element.
midElem :: forall m n a b. Iso (Vec (n+1) a) (Vec (m+1) b)
                               (a, Vec n a)  (b, Vec m b)
midElem = unsafeIxElem (`quot` 2)

----------------

-- | An isomorphism with a 'split' vector.
chopped :: (KnownNat m) => Iso (Vec (m + n) a)    (Vec (o + p) b)
                               (Vec m a, Vec n a) (Vec o b, Vec p b)
chopped = iso (split sintVal) (uncurry (++))

-- | A vector can be split (isomorphically) into a vector of vectors.
subVecs :: (KnownNat m, (n GHC.TypeLits.* m) ~ nm, (p GHC.TypeLits.* o) ~ po)
        => Iso (Vec nm a)        (Vec po b)
               (Vec n (Vec m a)) (Vec p (Vec o b))
subVecs = iso (reshape sintVal) concat

-- | A vector is isomorphic to its reversal.
reversed :: Iso (Vec n a) (Vec m b)
                (Vec n a) (Vec m b)
reversed = iso rev rev

--------------------------------
-- Other misc lenses

-- Unsafe version of ixElem, but with a function computing the
-- index from @valueOf @n@.
-- This allows unsafeIxElem to be used easily for midElem and snoced.
unsafeIxElem :: (Int -> Int) -> Iso (Vec (n+1) a) (Vec (m+1) b)
                                    (a, Vec n a)  (b, Vec m b)
unsafeIxElem fi = iso getf setf
  where getf xs =
          let !i = fi (vSize xs - 1)
          in  unsafeIndexK xs i $ \ xi ->
                let !xs' = unsafeRemove i xs
                in  (xi, xs')
        setf (xi, xs) =
          let !i = fi (vSize xs)
          in  unsafeInsert i xi xs
{-# INLINE unsafeIxElem #-}

-- | Isomorphism between a vector with and without a single element at
-- the given index.
ixElem :: forall n a b. Fin (n+1) -> Iso (Vec (n+1) a) (Vec (n+1) b)
                                         (a, Vec n a)  (b, Vec n b)
ixElem i = unsafeIxElem (const (finToInt i))


-- | A lens to a slice of the vector.
sliced
    :: forall m n a
    .  (KnownNat m, KnownNat n, m <= n)
    => Fin (n - m + 1)
    -> Lens' (Vec n a) (Vec m a)
sliced (finToInt -> !start) = lens getf setf
    where
    !m    = unSInt @m sintVal
    !n    = unSInt @n sintVal
    !end  = start + m
    !rest = n - end -- the length of the post-slice portion of the vector

    getf xs    = sliceVec xs start sintVal
    setf xs ys =
        createVec sintVal $ \mv -> do
            unsafeCopyVec xs 0   mv 0     start
            unsafeCopyVec ys 0   mv start m
            unsafeCopyVec xs end mv end   rest


-- | A two-element vector is isomorphic to a pair.
paired :: Iso (Vec 2 a) (Vec 2 b) (a, a) (b, b)
paired = iso unvec2 (uncurry vec2)
    where
    unvec2 v =
      indexK v (unsafeFin @Int 0) $ \x ->
      indexK v (unsafeFin @Int 1) $ \y -> (x,y)

-- | Isomorphism between a vector and a vector rotated @i@ steps.
-- The element at index 0 in the first vector is at index @i@ in the second.
-- E.g., @view (rotated 1) (fromList "ABCD") == fromList "DABC"@
rotated :: forall n a b. Fin n -> Iso (Vec n a) (Vec n b) (Vec n a) (Vec n b)
rotated i = iso (rot i) (\v -> rot (complementFin (svSize v) i) v)
{-# INLINE rotated #-}

-- | Isomorphism of transposed vectors.
vtransposed :: (KnownNat m, KnownNat p)
            => Iso (Vec n (Vec m a)) (Vec p (Vec o b))
                   (Vec m (Vec n a)) (Vec o (Vec p b))
vtransposed = iso (vtranspose sintVal) (vtranspose sintVal)

-- TODO: KnownNat not needed.
-- | Lens on the main diagonal.
vdiagonal :: forall n a. KnownNat n => Lens' (Vec n (Vec n a)) (Vec n a)
vdiagonal = lens getf setf
    where
    getf :: Vec n (Vec n a) -> Vec n a
    getf = imap (flip (!))

    setf :: Vec n (Vec n a) -> Vec n a -> Vec n (Vec n a)
    setf m d =
        mkVec sintVal $ \i ->
            indexK m i $ \mi ->
            indexK d i $ \di ->
            runST $ do
                mi' <- safeThawMV mi
                writeMV mi' i di
                unsafeFreezeMV mi'

#if !MIN_VERSION_lens(5,0,0)
instance L.FunctorWithIndex (Fin n) (Vec n) where imap = imap
instance KnownNat n => L.FoldableWithIndex (Fin n) (Vec n) where
  ifoldMap = ifoldMap
instance KnownNat n => L.TraversableWithIndex (Fin n) (Vec n) where
  itraverse = itraverse
#endif
