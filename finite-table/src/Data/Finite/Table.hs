-- Copyright 2019-2021 Google LLC
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

{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NoStarIsType #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

-- | Provides 'Vec'-backed tables indexed by 'Finite' types.
--
-- Combined with 'Data.Finite' and its Generics-based derivation, this can
-- effectively provide an array-backed container indexed by finite type.  This
-- is a low-syntactic-overhead way to create 'Representable' functors of any
-- desired shape: just define the index type, tack on the requisite @deriving@
-- clauses, and start using @'Table' MyType@.
--
-- @
--     data PrimaryColor = R | G | B
--       deriving Generic
--       deriving (Finite, Portray) via Wrapped Generic PrimaryColor
--
--     newtype Color = Color { getComponents :: Table PrimaryColor Int8 }
--
--     magenta :: Color
--     magenta = Color (Table $ Vec.fromList [255, 0, 255])
--
--     cyan :: Color
--     cyan = Color $ tabulate (\\case { R -> 0; G -> 255; B -> 255 })
--
--     main = pp $ getComponents magenta
--     -- "mkTable (\\case { R -> 255; G -> 0; B -> 255 })"
-- @

module Data.Finite.Table
         ( -- * Tables
           Table(..), (!), ix, idTable, mkTable, lmapTable, composeTable
           -- * Function Utilities
         , memoize, traverseRep
           -- * Representable Utilities
         , tabulateA, retabulated
         ) where

import Control.Applicative (Applicative(..))
import Data.Foldable (toList, traverse_)
import Data.Maybe (catMaybes, isJust)
import Data.Semigroup (Any(..), All(..))
import Control.DeepSeq (NFData(..))
import GHC.Generics (Generic)

import Control.Lens (Iso, Lens', from, lens, (&), (.~))
import Data.Default.Class (Default(..))
import Data.Distributive (Distributive(..))
import Data.Foldable.WithIndex (FoldableWithIndex(..))
import Data.Functor.Rep
         ( Representable(..), ifoldMapRep, imapRep, itraverseRep
         , tabulated
         )
import Data.Functor.WithIndex (FunctorWithIndex(..))
import Data.Portray (Portray(..), Portrayal(..))
import Data.Portray.Diff (Diff(..))
import Data.Serialize (Serialize(..))
import Data.Traversable.WithIndex (TraversableWithIndex(..))

import Data.Vec.Short (Vec)
import qualified Data.Vec.Short as V
import qualified Data.Vec.Short.Explicit as VE
import qualified Data.Vec.Short.Lens as V (ix)

import Data.Finite

#if !MIN_VERSION_lens(5,0,0)
import qualified Control.Lens as L
#endif

-- | A compact array of @b@s indexed by @a@, according to @'Finite' a@.
newtype Table a b = Table (Vec (Cardinality a) b)
  deriving (Eq, Ord, Show, Functor, Foldable, Generic)

-- | Pretty-print a Table as a 'mkTable' expression.
--
-- @
--     λ> pp $ (tabulate (even . finToInt) :: Table (Fin 3) Bool )
--     mkTable (\\case { 0 -> True; 1 -> False; 2 -> True })
-- @
instance (Finite a, Portray a, Portray b) => Portray (Table a b) where
  portray (Table xs) = Apply "mkTable" $ pure $ LambdaCase $
    zipWith (\a b -> (portray a, portray b)) (enumerate @a) (toList xs)

instance (Finite a, Portray a, Diff b) => Diff (Table a b) where
  diff (Table xs) (Table ys) =
    if hasDiff
      then Just $ Apply "mkTable" $ pure $ LambdaCase $
             (if allDiff then id else (++ [("_", "_")])) $
             catMaybes labeledDiffs
      else Nothing
   where
    (Any hasDiff, All allDiff) = foldMap
      (\x -> (Any (isJust x), All (isJust x)))
      labeledDiffs
    labeledDiffs = zipWith3
      (\a x y -> sequenceA (portray a, diff x y))
      (enumerate @a)
      (toList xs)
      (toList ys)

instance NFData a => NFData (Table k a) where
  rnf (Table vec) = rnf vec

instance (Finite k, Serialize a) => Serialize (Table k a) where
  get = sequenceA $ mkTable (const get)
  put = traverse_ put

instance Finite a => Applicative (Table a) where
  pure = tabulate . const
  liftA2 f x y = tabulate (liftA2 f (index x) (index y))
  f <*> x = tabulate (index f <*> index x)

instance (Finite a, Default b) => Default (Table a b) where
  def = pure def

-- | 'Data.Profunctor.lmap' for a constrained 'Data.Profunctor.Profunctor'.
lmapTable :: (Finite b, Finite c) => (b -> c) -> Table c a -> Table b a
lmapTable f t = tabulate $ \x -> t `index` f x

instance Finite a => Traversable (Table a) where
  traverse f (Table vec) = Table <$> traverse f vec

instance Finite a => Distributive (Table a) where
  collect f fa =
    let fgb = f <$> fa
    in  Table $ VE.mkVec (cardinality @a) (\i -> flip index (fromFin i) <$> fgb)

instance Finite a => Representable (Table a) where
  type Rep (Table a) = a
  tabulate f = Table $ VE.mkVec (cardinality @a) (f . fromFin)
  index (Table vec) i = vec V.! toFin i

instance Finite a => FunctorWithIndex a (Table a) where imap = imapRep
instance Finite a => FoldableWithIndex a (Table a) where ifoldMap = ifoldMapRep
instance Finite a => TraversableWithIndex a (Table a) where
  itraverse = itraverseRep

#if !MIN_VERSION_lens(5,0,0)
instance Finite a => L.FunctorWithIndex a (Table a) where imap = imapRep
instance Finite a => L.FoldableWithIndex a (Table a) where ifoldMap = ifoldMapRep
instance Finite a => L.TraversableWithIndex a (Table a) where
  itraverse = itraverseRep
#endif

-- | The identity morphism of a constrained category of 'Table's.
idTable :: Finite a => Table a a
idTable = tabulate id

-- | The composition of a constrained category of 'Table's.
composeTable :: (Finite a, Finite b) => Table b c -> Table a b -> Table a c
composeTable tbc tab = tabulate $ index tbc . index tab

-- | 'traverse' a function whose argument is a finite enumerable type.
traverseRep
  :: forall x a b f
   . (Finite x, Applicative f)
  => (a -> f b) -> (x -> a) -> f (x -> b)
traverseRep f = fmap index . traverse f . tabulate @(Table _)

-- | Memoize a function by using a 'Vec' as a lazy lookup table.
--
-- Given a function whose argument is a 'Finite' type, return a new function
-- that looks up the argument in a table constructed by applying the original
-- function to every possible value.  Since 'Vec' stores its elements boxed,
-- none of the applications of @f@ in the table are forced until they're forced
-- by calling the memoized function and forcing the result.
memoize :: Finite a => (a -> b) -> a -> b
memoize = index . tabulate @(Table _)

-- | An 'Iso' between two 'Representable' Functors with the same 'Rep' type.
retabulated
  :: (Representable f, Representable g, Rep f ~ Rep g)
  => Iso (f a) (f b) (g a) (g b)
retabulated = from tabulated . tabulated

-- | Infix 'index', monomorphized.
(!) :: Finite a => Table a b -> a -> b
(!) = index

-- | Lens on a single element.
ix :: Finite a => a -> Lens' (Table a b) b
ix a = a `seq` lens (! a) (\(Table vec) b -> Table (vec & V.ix (toFin a) .~ b))

-- | Monomorphized 'tabulate'.  Can be useful for type ambiguity reasons.
mkTable :: Finite a => (a -> b) -> Table a b
mkTable = tabulate

-- | Convenience function for building any 'Representable' as if by 'traverse'.
--
-- > tabulateA f = sequenceA (tabulate f) = traverse f (tabulate id)
tabulateA
  :: (Traversable t, Representable t, Applicative f)
  => (Rep t -> f b) -> f (t b)
tabulateA = sequenceA . tabulate
