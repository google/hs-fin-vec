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

{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE TypeOperators #-}

module Data.Vec.Short
         ( Vec
         -- * Core constructors\/generators
         -- ** 'Fin'-based constructors
         , mkVec, mkVec'
         , backpermute
         -- ** List-based constructors
         , fromList, fromListN, withVec
         -- ** Arity-based constructors
         , vec1, vec2, vec3, vec4, vec6, vec8
         -- ** 'Enum'-based constructors
         , viota

         -- * Core operators
         -- ** Size\/length
         , vLength, vSize, withSize
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
         , map', mapWithPos, mapWithPos', withPos
         , cross
         , toListWithPos, foldrWithPos
         , traversePos_, forPos_
         , traverseWithPos_, forVecWithPos_
         , vscanl
         , liftA2Lazy
         ) where

import Prelude hiding (concatMap, concat, iterate, (++))

import GHC.TypeNats (KnownNat, type (+), type (*))

import Data.Fin.Int (Fin)
import Data.SInt (sintVal)

import Data.Vec.Short.Internal hiding
         ( backpermute, mkVec, mkVec', split, reshape
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

-- | Split a 'Vec' into two at a given offset.
split :: KnownNat m => Vec (m + n) a -> (Vec m a, Vec n a)
split = V.split sintVal
{-# INLINE split #-}

-- | Split a 'Vec' into a 'Vec' of equal-sized chunks.
reshape :: KnownNat m => Vec (n * m) a -> Vec n (Vec m a)
reshape = V.reshape sintVal
{-# INLINE reshape #-}
