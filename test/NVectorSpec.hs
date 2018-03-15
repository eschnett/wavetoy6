{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module NVectorSpec where

import Data.Complex

import Test.QuickCheck
import Test.QuickCheck.Poly

import Comonad
import Functor
import NVector
import Unboxed



type N = 10

prop_NVector_Functor_id :: NVector N A -> Property
prop_NVector_Functor_id = law_Functor_id

prop_NVector_Functor_comp :: Fun B C -> Fun A B -> NVector N A -> Property
prop_NVector_Functor_comp = law_Functor_comp

prop_NVector_Semicomonad_comm ::
    Fun (NVector N B) C -> Fun (NVector N A) B -> NVector N A -> Property
prop_NVector_Semicomonad_comm = law_Semicomonad_comm



type UA = Int
type UB = Double
type UC = Complex Double

prop_NUVector_Functor_id :: NUVector N UA -> Property
prop_NUVector_Functor_id = law_Functor_id

prop_NUVector_Functor_comp ::
    (UB -#> UC) -> (UA -#> UB) -> NUVector N UA -> Property
prop_NUVector_Functor_comp = law_Functor_comp
