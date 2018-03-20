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

prop_NVector_Functor_id :: CheckedLaw (NVector N A)
prop_NVector_Functor_id = checkLaw law_Functor_id

prop_NVector_Functor_comp :: Fun B C -> Fun A B -> CheckedLaw (NVector N A)
prop_NVector_Functor_comp f g = checkLaw (law_Functor_comp f g)

prop_NVector_Semicomonad_comm ::
    Fun (NVector N B) C -> Fun (NVector N A) B -> CheckedLaw (NVector N A)
prop_NVector_Semicomonad_comm f g = checkLaw (law_Semicomonad_comm f g)



type UA = Int
type UB = Double
type UC = Complex Double

prop_NUVector_Functor_id :: CheckedLaw (NUVector N UA)
prop_NUVector_Functor_id = checkLaw law_Functor_id

prop_NUVector_Functor_comp ::
    (UB -#> UC) -> (UA -#> UB) -> CheckedLaw (NUVector N UA)
prop_NUVector_Functor_comp f g = checkLaw (law_Functor_comp f g)
