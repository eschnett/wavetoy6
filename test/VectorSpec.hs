{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module VectorSpec where

import Data.Complex

import Test.QuickCheck
import Test.QuickCheck.Poly

import Category
import Comonad
import Functor
import Unboxed
import Vector



prop_Vector_Functor_id :: FnProp (Vector A)
prop_Vector_Functor_id = checkFnEqual law_Functor_id

prop_Vector_Functor_comp :: Fun B C -> Fun A B -> FnProp (Vector A)
prop_Vector_Functor_comp f g = checkFnEqual (law_Functor_comp f g)

prop_Vector_Semicomonad_comm ::
    Fun (Vector B) C -> Fun (Vector A) B -> FnProp (Vector A)
prop_Vector_Semicomonad_comm f g = checkFnEqual (law_Semicomonad_comm f g)

prop_Vector_Semicomonad1_comm ::
    Fun (Vector B) C -> Fun (Vector A) B -> FnProp (Vector A)
prop_Vector_Semicomonad1_comm f g = checkFnEqual (law_Semicomonad1_comm f g)

prop_Vector_Semicomonad1_comm' ::
    Fun (Vector B) C -> Fun (Vector A) B -> FnProp (Vector A)
prop_Vector_Semicomonad1_comm' (Fn f) (Fn g) =
    checkFnEqual (law_Semicomonad1_comm' f g)



type UA = Int
type UB = Double
type UC = Complex Double

prop_UVector_Functor_id :: FnProp (UVector UA)
prop_UVector_Functor_id = checkFnEqual law_Functor_id

prop_UVector_Functor_comp ::
    (UB -#> UC) -> (UA -#> UB) -> FnProp (UVector UA)
prop_UVector_Functor_comp f g = checkFnEqual (law_Functor_comp f g)

prop_UVector_Semicomonad1_comm' ::
    Fun (UVector UB) UC -> Fun (UVector UA) UB -> FnProp (UVector UA)
prop_UVector_Semicomonad1_comm' (Fn f) (Fn g) =
    checkFnEqual (law_Semicomonad1_comm' f g)
