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



prop_Vector_Functor_id :: CheckedLaw (Vector A)
prop_Vector_Functor_id = checkLaw law_Functor_id

prop_Vector_Functor_comp :: Fun B C -> Fun A B -> CheckedLaw (Vector A)
prop_Vector_Functor_comp f g = checkLaw (law_Functor_comp f g)

prop_Vector_Semicomonad_comm ::
    Fun (Vector B) C -> Fun (Vector A) B -> CheckedLaw (Vector A)
prop_Vector_Semicomonad_comm f g = checkLaw (law_Semicomonad_comm f g)

prop_Vector_Semicomonad1_comm ::
    Fun (Vector B) C -> Fun (Vector A) B -> CheckedLaw (Vector A)
prop_Vector_Semicomonad1_comm f g = checkLaw (law_Semicomonad1_comm f g)

prop_Vector_Semicomonad1_comm' ::
    Fun (Vector B) C -> Fun (Vector A) B -> CheckedLaw (Vector A)
prop_Vector_Semicomonad1_comm' (Fn f) (Fn g) =
    checkLaw (law_Semicomonad1_comm' f g)



type UA = Int
type UB = Double
type UC = Complex Double

prop_UVector_Functor_id :: CheckedLaw (UVector UA)
prop_UVector_Functor_id = checkLaw law_Functor_id

prop_UVector_Functor_comp ::
    (UB -#> UC) -> (UA -#> UB) -> CheckedLaw (UVector UA)
prop_UVector_Functor_comp f g = checkLaw (law_Functor_comp f g)

prop_UVector_Semicomonad1_comm' ::
    Fun (UVector UB) UC -> Fun (UVector UA) UB -> CheckedLaw (UVector UA)
prop_UVector_Semicomonad1_comm' (Fn f) (Fn g) =
    checkLaw (law_Semicomonad1_comm' f g)
