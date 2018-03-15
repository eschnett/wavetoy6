{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module CNVectorSpec where

import Data.Complex

import Test.QuickCheck
import Test.QuickCheck.Poly

import CNVector
import Functor
import Unboxed



type N = 10

prop_CNVector_Functor_id :: CNVector N A -> Property
prop_CNVector_Functor_id = law_Functor_id

prop_CNVector_Functor_comp :: Fun B C -> Fun A B -> CNVector N A -> Property
prop_CNVector_Functor_comp = law_Functor_comp

type UA = Int
type UB = Double
type UC = Complex Double

prop_CNUVector_Functor_id :: CNUVector N UA -> Property
prop_CNUVector_Functor_id = law_Functor_id

prop_CNUVector_Functor_comp ::
    (UB -#> UC) -> (UA -#> UB) -> CNUVector N UA -> Property
prop_CNUVector_Functor_comp = law_Functor_comp
