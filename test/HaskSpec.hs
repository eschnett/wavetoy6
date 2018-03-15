{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module HaskSpec where

import Data.Functor.Compose
import Data.Functor.Identity
import Data.Functor.Product
import Data.Functor.Sum
import Data.Proxy

import Test.QuickCheck
import Test.QuickCheck.Poly

import Category
import Functor
import Hask



prop_Hask_Discretization_inv :: Fun A B -> A -> Property
prop_Hask_Discretization_inv (Fn f) = law_Discretization_inv f

prop_Hask_Discretization_approx :: Fun A B -> A -> Property
prop_Hask_Discretization_approx (Fn f) x =
    law_Discretization_approx (Proxy @(->)) f x (===)



prop_Hask_MId_id :: A -> Property
prop_Hask_MId_id = law_MId_id (Proxy @Hask)

prop_Hask_MCompose_compose :: Fun B C -> Fun A B -> A -> Property
prop_Hask_MCompose_compose (Fn f) (Fn g) = law_MCompose_compose f g

prop_Hask_MCompose_left_id :: Fun A B -> A -> Property
prop_Hask_MCompose_left_id (Fn f) = law_MCompose_left_id f

prop_Hask_MCompose_right_id :: Fun A B -> A -> Property
prop_Hask_MCompose_right_id (Fn f) = law_MCompose_right_id f

type D = A

prop_Hask_MCompose_assoc :: Fun C D -> Fun B C -> Fun A B -> A -> Property
prop_Hask_MCompose_assoc (Fn f) (Fn g) (Fn h) = law_MCompose_assoc f g h



prop_Proxy_Functor_id :: Proxy A -> Property
prop_Proxy_Functor_id = law_Functor_id

prop_Proxy_Functor_comp :: Fun B C -> Fun A B -> Proxy A -> Property
prop_Proxy_Functor_comp = law_Functor_comp

prop_Identity_Functor_id :: Identity A -> Property
prop_Identity_Functor_id = law_Functor_id

prop_Identity_Functor_comp :: Fun B C -> Fun A B -> Identity A -> Property
prop_Identity_Functor_comp = law_Functor_comp

prop_Maybe_Functor_id :: Maybe A -> Property
prop_Maybe_Functor_id = law_Functor_id

prop_Maybe_Functor_comp :: Fun B C -> Fun A B -> Maybe A -> Property
prop_Maybe_Functor_comp = law_Functor_comp

prop_Either_Functor_id :: Either Int A -> Property
prop_Either_Functor_id = law_Functor_id

prop_Either_Functor_comp :: Fun B C -> Fun A B -> Either Int A -> Property
prop_Either_Functor_comp = law_Functor_comp

prop_Tuple_Functor_id :: (Int, A) -> Property
prop_Tuple_Functor_id = law_Functor_id

prop_Tuple_Functor_comp :: Fun B C -> Fun A B -> (Int, A) -> Property
prop_Tuple_Functor_comp = law_Functor_comp

prop_List_Functor_id :: [A] -> Property
prop_List_Functor_id = law_Functor_id

prop_List_Functor_comp :: Fun B C -> Fun A B -> [A] -> Property
prop_List_Functor_comp = law_Functor_comp

type FA = Either Int
type FB = (,) Double
type FC = []

prop_Sum_Functor_id :: Sum FA FB A -> Property
prop_Sum_Functor_id = law_Functor_id

prop_Sum_Functor_comp :: Fun B C -> Fun A B -> Sum FA FB A -> Property
prop_Sum_Functor_comp = law_Functor_comp

prop_Product_Functor_id :: Product FA FB A -> Property
prop_Product_Functor_id = law_Functor_id

prop_Product_Functor_comp :: Fun B C -> Fun A B -> Product FA FB A -> Property
prop_Product_Functor_comp = law_Functor_comp

prop_Compose_Functor_id :: Compose FA FB A -> Property
prop_Compose_Functor_id = law_Functor_id

prop_Compose_Functor_comp :: Fun B C -> Fun A B -> Compose FA FB A -> Property
prop_Compose_Functor_comp = law_Functor_comp
