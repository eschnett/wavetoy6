{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module VectorSpec where

import Data.Complex

import Test.QuickCheck
import Test.QuickCheck.Poly

import Functor
import Unboxed
import Vector



prop_Vector_Functor_id :: Vector A -> Property
prop_Vector_Functor_id = law_Functor_id

prop_Vector_Functor_comp :: Fun B C -> Fun A B -> Vector A -> Property
prop_Vector_Functor_comp = law_Functor_comp

type UA = Int
type UB = Double
type UC = Complex Double

prop_UVector_Functor_id :: UVector UA -> Property
prop_UVector_Functor_id = law_Functor_id

prop_UVector_Functor_comp ::
    (UB -#> UC) -> (UA -#> UB) -> UVector UA -> Property
prop_UVector_Functor_comp = law_Functor_comp
