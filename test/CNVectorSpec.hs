{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module CNVectorSpec where

import Data.Complex
import Data.Proxy

import Test.QuickCheck
import Test.QuickCheck.Poly

import CNVector
import Comonad
import Functor
import Unboxed
import Vec



type N = 10

prop_CNVector_Functor_id :: CNVector N A -> Property
prop_CNVector_Functor_id = law_Functor_id

prop_CNVector_Functor_comp :: Fun B C -> Fun A B -> CNVector N A -> Property
prop_CNVector_Functor_comp = law_Functor_comp

prop_CNVector_Semicomonad_comm ::
    Fun (CNVector N B) C -> Fun (CNVector N A) B -> CNVector N A -> Property
prop_CNVector_Semicomonad_comm = law_Semicomonad_comm

prop_CNVector_Comonad_id :: CNVector N A -> Property
prop_CNVector_Comonad_id = law_Comonad_id (Proxy @(->))

prop_CNVector_Comonad_apply :: Fun (CNVector N A) B -> CNVector N A -> Property
prop_CNVector_Comonad_apply = law_Comonad_apply



type UA = Int
type UB = Double
type UC = Complex Double

prop_CNUVector_Functor_id :: CNUVector N UA -> Property
prop_CNUVector_Functor_id = law_Functor_id

prop_CNUVector_Functor_comp ::
    (UB -#> UC) -> (UA -#> UB) -> CNUVector N UA -> Property
prop_CNUVector_Functor_comp = law_Functor_comp

prop_CNUVector_CompactSemicomonad_restrict ::
    Proxy (CNUVector N) -> (UVec3 N) UA -> Property
prop_CNUVector_CompactSemicomonad_restrict = law_CompactSemicomonad_restrict
