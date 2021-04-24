-- | An API for "Data.Vec.Short" with 'SInt's for all size parameters.

module Data.Vec.Short.Explicit
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
