{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module UnboxedSpec where

import Data.Complex
import Data.Proxy

import Test.QuickCheck

import Category
import Functor
import Unboxed



type UA = Int *#* Float
type UB = Double
type UC = Complex Double
type UD = Int

prop_Unboxed_Discretization_inv :: Fun UA UB -> UA -> Property
prop_Unboxed_Discretization_inv f = law_Discretization_inv (UQCFun f)

prop_Unboxed_Discretization_approx :: Fun UA UB -> UA -> Property
prop_Unboxed_Discretization_approx (Fn f) x =
    law_Discretization_approx (Proxy @(-#>)) f x (===)



prop_Unboxed_MId_id :: UA -> Property
prop_Unboxed_MId_id = law_MId_id (Proxy @Unboxed)

prop_Unboxed_MCompose_compose :: Fun UB UC -> Fun UA UB -> UA -> Property
prop_Unboxed_MCompose_compose f g = law_MCompose_compose (UQCFun f) (UQCFun g)

prop_Unboxed_MCompose_left_id :: Fun UA UB -> UA -> Property
prop_Unboxed_MCompose_left_id f = law_MCompose_left_id (UQCFun f)

prop_Unboxed_MCompose_right_id :: Fun UA UB -> UA -> Property
prop_Unboxed_MCompose_right_id f = law_MCompose_right_id (UQCFun f)

prop_Unboxed_MCompose_assoc ::
    Fun UC UD -> Fun UB UC -> Fun UA UB -> UA -> Property
prop_Unboxed_MCompose_assoc f g h =
    law_MCompose_assoc (UQCFun f) (UQCFun g) (UQCFun h)



prop_Unboxed_Functor_id :: CheckedLaw (Float *#* UA)
prop_Unboxed_Functor_id = checkLaw law_Functor_id

prop_Unboxed_Functor_comp ::
    (UB -#> UC) -> (UA -#> UB) -> CheckedLaw (Float *#* UA)
prop_Unboxed_Functor_comp f g = checkLaw (law_Functor_comp f g)
