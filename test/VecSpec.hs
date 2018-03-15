{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module VecSpec where

import Data.Complex

import Test.QuickCheck
import Test.QuickCheck.Poly

import Vec
import Functor
import Unboxed



type N = 10

prop_Vec_Functor_id :: Vec3 N A -> Property
prop_Vec_Functor_id = law_Functor_id

prop_Vec_Functor_comp :: Fun B C -> Fun A B -> Vec3 N A -> Property
prop_Vec_Functor_comp = law_Functor_comp

type UA = Int
type UB = Double
type UC = Complex Double

prop_UVec3_Functor_id :: UVec3 N UA -> Property
prop_UVec3_Functor_id = law_Functor_id

prop_UVec3_Functor_comp ::
    (UB -#> UC) -> (UA -#> UB) -> UVec3 N UA -> Property
prop_UVec3_Functor_comp = law_Functor_comp
