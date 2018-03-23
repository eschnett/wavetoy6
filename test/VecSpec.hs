{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module VecSpec where

import Data.Complex

import Test.QuickCheck
import Test.QuickCheck.Poly

import Category
import Functor
import Unboxed
import Vec



type N = 10

prop_Vec_Functor_id :: FnProp (Vec3 N A)
prop_Vec_Functor_id = checkFnEqual law_Functor_id

prop_Vec_Functor_comp :: Fun B C -> Fun A B -> FnProp (Vec3 N A)
prop_Vec_Functor_comp f g = checkFnEqual (law_Functor_comp f g)



type UA = Int
type UB = Double
type UC = Complex Double

prop_UVec3_Functor_id :: FnProp (UVec3 N UA)
prop_UVec3_Functor_id = checkFnEqual law_Functor_id

prop_UVec3_Functor_comp ::
    (UB -#> UC) -> (UA -#> UB) -> FnProp (UVec3 N UA)
prop_UVec3_Functor_comp f g = checkFnEqual (law_Functor_comp f g)
