{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module CNVectorSpec where

import Data.Complex
import Data.Proxy

import Test.QuickCheck
import Test.QuickCheck.Poly

import CNVector
import Category
import Comonad
import Functor
import Unboxed
-- import Vec



type N = 10

prop_CNVector_Functor_id :: CheckedLaw (CNVector N A)
prop_CNVector_Functor_id = checkLaw law_Functor_id

prop_CNVector_Functor_comp :: Fun B C -> Fun A B -> CheckedLaw (CNVector N A)
prop_CNVector_Functor_comp f g = checkLaw (law_Functor_comp f g)

prop_CNVector_Semicomonad_comm ::
    Fun (CNVector N B) C -> Fun (CNVector N A) B -> CheckedLaw (CNVector N A)
prop_CNVector_Semicomonad_comm f g = checkLaw (law_Semicomonad_comm f g)

prop_CNVector_Comonad_id :: CheckedLaw (CNVector N A)
prop_CNVector_Comonad_id = law_Comonad_id (Proxy @(->))

prop_CNVector_Comonad_apply :: Fun (CNVector N A) B -> CheckedLaw (CNVector N A)
prop_CNVector_Comonad_apply = law_Comonad_apply

prop_CNVector_Semicomonad1_comm ::
    Fun (CNVector N B) C -> Fun (CNVector N A) B -> CheckedLaw (CNVector N A)
prop_CNVector_Semicomonad1_comm f g = checkLaw (law_Semicomonad1_comm f g)

prop_CNVector_Semicomonad1_comm' ::
    Fun (CNVector N B) C -> Fun (CNVector N A) B -> CheckedLaw (CNVector N A)
prop_CNVector_Semicomonad1_comm' (Fn f) (Fn g) =
    checkLaw (law_Semicomonad1_comm' f g)

prop_CNVector_Comonad1_id :: CheckedLaw (CNVector N A)
prop_CNVector_Comonad1_id = checkLaw (law_Comonad1_id (Proxy @(->)))

prop_CNVector_Comonad1_id' :: CheckedLaw (CNVector N A)
prop_CNVector_Comonad1_id' = checkLaw law_Comonad1_id'

prop_CNVector_Comonad1_apply ::
    Fun (CNVector N A) B -> CheckedLaw (CNVector N A)
prop_CNVector_Comonad1_apply f = checkLaw (law_Comonad1_apply f)

prop_CNVector_Comonad1_apply' ::
    Fun (CNVector N A) B -> CheckedLaw (CNVector N A)
prop_CNVector_Comonad1_apply' (Fn f) = checkLaw (law_Comonad1_apply' f)



type UA = Int
type UB = Double
type UC = Complex Double

prop_CNUVector_Functor_id :: CheckedLaw (CNUVector N UA)
prop_CNUVector_Functor_id = checkLaw law_Functor_id

prop_CNUVector_Functor_comp ::
    (UB -#> UC) -> (UA -#> UB) -> CheckedLaw (CNUVector N UA)
prop_CNUVector_Functor_comp f g = checkLaw (law_Functor_comp f g)

-- prop_CNUVector_NatAdjunction_restrict ::
--     Proxy (CNUVector N) -> (UVec3 N) UA -> Property
-- prop_CNUVector_NatAdjunction_restrict = law_NatAdjunction_restrict

prop_CNUVector_Semicomonad1_comm' ::
    Fun (CNUVector N UB) UC -> Fun (CNUVector N UA) UB ->
    CheckedLaw (CNUVector N UA)
prop_CNUVector_Semicomonad1_comm' (Fn f) (Fn g) =
    checkLaw (law_Semicomonad1_comm'
                     (f :: CNUVector N UB -> UC)
                     (g :: CNUVector N UA -> UB))

prop_CNUVector_Comonad1_id' :: CheckedLaw (CNUVector N UA)
prop_CNUVector_Comonad1_id' = checkLaw law_Comonad1_id'

prop_CNUVector_Comonad1_apply' ::
    Fun (CNVector N UA) UB -> CheckedLaw (CNVector N UA)
prop_CNUVector_Comonad1_apply' (Fn f) = checkLaw (law_Comonad1_apply' f)
