{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module NVectorSpec where

import Data.Complex

import Test.QuickCheck
import Test.QuickCheck.Poly

import Category
import Comonad
import Functor
import NVector
import Unboxed



type N = 10

prop_NVector_Functor_id :: FnProp (NVector N A)
prop_NVector_Functor_id = checkFnEqual law_Functor_id

prop_NVector_Functor_comp :: Fun B C -> Fun A B -> FnProp (NVector N A)
prop_NVector_Functor_comp f g = checkFnEqual (law_Functor_comp f g)

prop_NVector_Semicomonad_comm ::
    Fun (NVector N B) C -> Fun (NVector N A) B -> FnProp (NVector N A)
prop_NVector_Semicomonad_comm f g = checkFnEqual (law_Semicomonad_comm f g)

prop_NVector_Semicomonad1_comm ::
    Fun (NVector N B) C -> Fun (NVector N A) B -> FnProp (NVector N A)
prop_NVector_Semicomonad1_comm f g = checkFnEqual (law_Semicomonad1_comm f g)

prop_NVector_Semicomonad1_comm' ::
    Fun (NVector N B) C -> Fun (NVector N A) B -> FnProp (NVector N A)
prop_NVector_Semicomonad1_comm' (Fn f) (Fn g) =
    checkFnEqual (law_Semicomonad1_comm' f g)



type UA = Int
type UB = Double
type UC = Complex Double

prop_NUVector_Functor_id :: FnProp (NUVector N UA)
prop_NUVector_Functor_id = checkFnEqual law_Functor_id

prop_NUVector_Functor_comp ::
    (UB -#> UC) -> (UA -#> UB) -> FnProp (NUVector N UA)
prop_NUVector_Functor_comp f g = checkFnEqual (law_Functor_comp f g)

prop_NUVector_Semicomonad1_comm' ::
    Fun (NUVector N UB) UC -> Fun (NUVector N UA) UB ->
    FnProp (NUVector N UA)
prop_NUVector_Semicomonad1_comm' (Fn f) (Fn g) =
    checkFnEqual (law_Semicomonad1_comm' f g)
