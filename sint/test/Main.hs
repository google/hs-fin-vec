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

{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Main where

import Control.Exception (evaluate, try)
import Data.Bifunctor (first)
import Data.Functor (void)
import Data.Proxy (Proxy(..))
import GHC.Exception (ErrorCall)
import GHC.TypeNats (SomeNat(..), someNatVal, natVal)
import Numeric.Natural (Natural)

import Test.Framework (defaultMain)
import Test.Framework.Providers.QuickCheck2 (testProperty)
import Test.QuickCheck
         ( (===), (==>), forAll, Gen, arbitrary, ioProperty, scale
         , Positive(..), Negative(..), Property
         )

import Data.SInt

maxInt :: Natural
maxInt = fromIntegral (maxBound @Int)

naturals :: Gen Natural
naturals = fromInteger . getPositive <$> arbitrary

raisesError :: a -> Property
raisesError x = ioProperty $ do
  r <- try @ErrorCall $ evaluate x
  return $ void (first (const ()) r) === Left ()

main :: IO ()
main = defaultMain
  [ testProperty "trySIntVal in bounds" $ forAll naturals $
      \x -> x <= maxInt ==> case someNatVal x of
        SomeNat (Proxy :: Proxy n) ->
          fmap (fromIntegral . unSInt) (trySIntVal @n) === Just x

  , testProperty "trySIntVal out of bounds" $ forAll naturals $
      \x -> case someNatVal (maxInt + x) of
        SomeNat (Proxy :: Proxy n) ->
          void (trySIntVal @n) === Nothing

  , testProperty "withSInt negative raises" $ \ (Negative x) ->
      raisesError $ withSInt x $ const ()

  , testProperty "withSInt positive" $ \ (Positive x) ->
      withSInt x unSInt === x

  , testProperty "addSInt" $
      \ (Positive x) (Positive y) ->
        withSInt x $ \x' ->
        withSInt y $ \y' ->
          let xy = fromIntegral x + fromIntegral y :: Natural
          in  if xy > maxInt
                then raisesError $ addSInt x' y'
                else fromIntegral (unSInt (addSInt x' y')) === xy

  , testProperty "addSInt out of range" $
      raisesError $ withSInt maxBound $ \x -> withSInt 1 (unSInt . addSInt x)

  , testProperty "subSInt" $
      \ (Positive x) (Positive y) ->
        withSInt x $ \x' ->
        withSInt y $ \y' ->
          if x < y
            then raisesError $ subSInt x' y'
            else unSInt (subSInt x' y') === x - y

  , testProperty "mulSInt" $
      forAll (scale (*1000000000) arbitrary) $ \ (Positive x) ->
      forAll (scale (*1000000000) arbitrary) $ \ (Positive y) ->
        withSInt x $ \x' ->
        withSInt y $ \y' ->
          let xy = fromIntegral x * fromIntegral y :: Natural
          in  if xy > maxInt
                then raisesError $ mulSInt x' y'
                else fromIntegral (unSInt (mulSInt x' y')) === xy

  , testProperty "reifySInt" $
      \ (Positive x) ->
        withSInt x $ \ (x' :: SInt n) ->
          fromIntegral x === reifySInt x' (natVal @n Proxy)
  ]
