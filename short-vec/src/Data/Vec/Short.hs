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

-- | An implementation of short vectors.
--
-- The underlying implementation uses the 'GHC.Exts.SmallArray#' primitive,
-- which is best-suited for short vectors (less than a few hundred elements).

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Data.Vec.Short
         ( Vec
         -- * Core constructors\/generators
         -- ** 'Fin'-based constructors
         , mkVec, mkVec'
         , backpermute
         -- ** List-based constructors
         , fromList, withVec
         -- ** Arity-based constructors
         , vec1, vec2, vec3, vec4, vec6, vec8
         -- ** 'Enum'-based constructors
         , viota

         -- * Core operators
         -- ** Size\/length
         , svSize, vLength, vSize, withSize
         -- ** Indexing
         , (!), indexK
         -- ** Add/remove element
         , insert, remove, overIx

         -- * List-like operators
         -- ** Constructor views
         -- *** The nil view
         , nil
         -- ** Operator views
         -- *** The append view
         , (++), split
         -- *** The concat view
         , concat, concatMap, reshape
         -- *** The reverse view
         , rev, rot
         -- *** The transposition view
         , vtranspose
         -- ** Misc list-like operators
         , iterate, iterate'
         , vsort, vsortBy, vsortOn
         , vfindIndex

         -- * Additional zips, maps, folds, etc.
         , map', imap', withPos
         , cross
         , vscanl
         , liftA2Lazy
         ) where

import Prelude hiding (concatMap, concat, iterate, (++))

import GHC.TypeNats (KnownNat, type (+), type (*))
import GHC.Stack (HasCallStack)

import Data.Fin.Int (Fin)
import Data.SInt (sintVal, unSInt, reifySInt)

import Data.Vec.Short.Internal hiding
         ( backpermute, mkVec, mkVec', split, reshape, vtranspose
         , iterate, iterate', fromList, viota, liftA2Lazy
         )
import qualified Data.Vec.Short.Internal as V

-- This module exposes API shims using KnownNat to quarantine SInt inside of
-- the data_vec package (for now; we may export both APIs in the future).

-- | Create a known-length vector using a pure function.
--
-- Note if you don't have the 'KnownNat' instance at hand, but you already have
-- a 'Vec' of the desired length, you can use 'withSize' to get the 'KnownNat'
-- instance.
mkVec :: KnownNat n => (Fin n -> a) -> Vec n a
mkVec = V.mkVec sintVal
{-# INLINE mkVec #-}

-- | Create a known-length vector using a pure function, strictly.
mkVec' :: KnownNat n => (Fin n -> a) -> Vec n a
mkVec' = V.mkVec' sintVal
{-# INLINE mkVec' #-}

-- | Create a 'Vec' by selecting indices of another 'Vec'.
backpermute :: KnownNat m => (Fin m -> Fin n) -> Vec n a -> Vec m a
backpermute = V.backpermute sintVal
{-# INLINE backpermute #-}

-- | Convert a list to a vector, throwing an error if the list has the
-- wrong length.
-- Note: Because this walks @xs@ to check its length, this cannot be
-- used with the list fusion optimization rules.
fromList :: (HasCallStack, KnownNat n) => [a] -> Vec n a
fromList = V.fromList sintVal
{-# INLINE fromList #-}

-- | Return a vector with all elements of the type in ascending order.
viota :: KnownNat n => Vec n (Fin n)
viota = V.viota sintVal
{-# INLINE viota #-}

-- | Split a 'Vec' into two at a given offset.
split :: KnownNat m => Vec (m + n) a -> (Vec m a, Vec n a)
split = V.split sintVal
{-# INLINE split #-}

-- | Split a 'Vec' into a 'Vec' of equal-sized chunks.
reshape :: KnownNat m => Vec (n * m) a -> Vec n (Vec m a)
reshape = V.reshape sintVal
{-# INLINE reshape #-}

-- | Transpose a vector of vectors.
vtranspose :: KnownNat m => Vec n (Vec m a) -> Vec m (Vec n a)
vtranspose = V.vtranspose sintVal
{-# INLINE vtranspose #-}

-- | Statically determine the (purported) size\/length of the vector.
-- If you'd rather not require the 'KnownNat' constraint, see 'vSize'.
vLength :: forall n a. KnownNat n => Vec n a -> Int
vLength _ = unSInt @n sintVal
{-# INLINE vLength #-}

-- | Generate a Vec by repeated application of a function.
--
-- > toList (Vec.iterate @n f z) === take (valueOf @n) (Prelude.iterate f z)
iterate :: KnownNat n => (a -> a) -> a -> Vec n a
iterate = V.iterate sintVal
{-# INLINE iterate #-}

-- | A strict version of 'iterate'.
iterate' :: KnownNat n => (a -> a) -> a -> Vec n a
iterate' = V.iterate' sintVal
{-# INLINE iterate' #-}

-- | A truly lazy version of @liftA2@.
--
-- As opposed to the actual @liftA2@ it does not inspect the arguments which
-- makes it possible it to use in code that has lazy knot-tying.
liftA2Lazy :: KnownNat n => (a -> b -> c) -> Vec n a -> Vec n b -> Vec n c
liftA2Lazy = V.liftA2Lazy sintVal
{-# INLINE liftA2Lazy #-}

-- | Dynamically determine the (actual) size\/length of the vector,
-- returning evidence that @n@ is \"known\". If you'd rather obtain @n@
-- as a standard 'Int', see 'vSize'.
withSize :: forall n a r . Vec n a -> (KnownNat n => r) -> r
withSize !xs f = reifySInt (svSize xs) f
{-# INLINE withSize #-}
