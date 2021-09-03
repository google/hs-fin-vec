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

-- | An API for "Data.Vec.Short" with 'Data.SInt.SInt's for all size parameters.

module Data.Vec.Short.Explicit
         ( Vec
         -- * Core constructors\/generators
         -- ** 'Data.Fin.Int.Fin'-based constructors
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
         , svSize, vSize
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

import Data.Vec.Short.Internal
