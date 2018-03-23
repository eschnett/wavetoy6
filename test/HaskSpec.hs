{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module HaskSpec where

import Data.Biapplicative
import Data.Functor.Compose
import Data.Functor.Identity
import Data.Functor.Product
import Data.Functor.Sum
import Data.Proxy

import Test.QuickCheck
import Test.QuickCheck.Poly

import Category
import Comonad
import Functor
import Hask


biapply :: Bifunctor f => a -> b -> f (a -> c) (b -> d) -> f c d
biapply x y fs = bimap (\f -> f x) (\g -> g y) fs

prop_Hask_Discretization_inv :: Fun A B -> FnProp A
prop_Hask_Discretization_inv (Fn f) = checkFnEqual (law_Discretization_inv f)

prop_Hask_Discretization_approx :: Fun A B -> FnProp A
prop_Hask_Discretization_approx (Fn f) =
    checkFnEqual (law_Discretization_approx (Proxy @(->)) f)



prop_Hask_MId_id :: A -> Property
prop_Hask_MId_id = law_MId_id (Proxy @Hask)

prop_Hask_MCompose_compose :: Fun B C -> Fun A B -> FnProp A
prop_Hask_MCompose_compose (Fn f) (Fn g) = law_MCompose_compose f g

prop_Hask_MCompose_left_id :: Fun A B ->  FnProp A
prop_Hask_MCompose_left_id (Fn f) = law_MCompose_left_id f

prop_Hask_MCompose_right_id :: Fun A B -> FnProp A
prop_Hask_MCompose_right_id (Fn f) = law_MCompose_right_id f

type D = A

prop_Hask_MCompose_assoc :: Fun C D -> Fun B C -> Fun A B -> FnProp A
prop_Hask_MCompose_assoc (Fn f) (Fn g) (Fn h) = law_MCompose_assoc f g h



prop_Proxy_Functor_id :: FnProp (Proxy A)
prop_Proxy_Functor_id = checkFnEqual law_Functor_id

prop_Proxy_Functor_comp :: Fun B C -> Fun A B -> FnProp (Proxy A)
prop_Proxy_Functor_comp f g = checkFnEqual (law_Functor_comp f g)

prop_Proxy_Semicomonad_comm ::
    Fun (Proxy B) C -> Fun (Proxy A) B -> FnProp (Proxy A)
prop_Proxy_Semicomonad_comm f g = checkFnEqual (law_Semicomonad_comm f g)

prop_Proxy_Semicomonad1_comm ::
    Fun (Proxy B) C -> Fun (Proxy A) B -> FnProp (Proxy A)
prop_Proxy_Semicomonad1_comm f g = checkFnEqual (law_Semicomonad1_comm f g)

prop_Proxy_Semicomonad1_comm' ::
    Fun (Proxy B) C -> Fun (Proxy A) B -> FnProp (Proxy A)
prop_Proxy_Semicomonad1_comm' (Fn f) (Fn g) =
    checkFnEqual (law_Semicomonad1_comm' f g)



prop_Identity_Functor_id :: FnProp (Identity A)
prop_Identity_Functor_id = checkFnEqual law_Functor_id

prop_Identity_Functor_comp :: Fun B C -> Fun A B -> FnProp (Identity A)
prop_Identity_Functor_comp f g = checkFnEqual (law_Functor_comp f g)

prop_Identity_Semicomonad_comm ::
    Fun (Identity B) C -> Fun (Identity A) B -> FnProp (Identity A)
prop_Identity_Semicomonad_comm f g = checkFnEqual (law_Semicomonad_comm f g)

prop_Identity_Comonad_id :: FnProp (Identity A)
prop_Identity_Comonad_id = checkFnEqual (law_Comonad_id (Proxy @(->)))

prop_Identity_Comonad_apply :: Fun (Identity A) B -> FnProp (Identity A)
prop_Identity_Comonad_apply f = checkFnEqual (law_Comonad_apply f)

prop_Identity_Semicomonad1_comm ::
    Fun (Identity B) C -> Fun (Identity A) B -> FnProp (Identity A)
prop_Identity_Semicomonad1_comm f g = checkFnEqual (law_Semicomonad1_comm f g)

prop_Identity_Semicomonad1_comm' ::
    Fun (Identity B) C -> Fun (Identity A) B -> FnProp (Identity A)
prop_Identity_Semicomonad1_comm' (Fn f) (Fn g) =
    checkFnEqual (law_Semicomonad1_comm' f g)



prop_Maybe_Functor_id :: FnProp (Maybe A)
prop_Maybe_Functor_id = checkFnEqual law_Functor_id

prop_Maybe_Functor_comp :: Fun B C -> Fun A B -> FnProp (Maybe A)
prop_Maybe_Functor_comp f g = checkFnEqual (law_Functor_comp f g)

prop_Maybe_Semicomonad_comm ::
    Fun (Maybe B) C -> Fun (Maybe A) B -> FnProp (Maybe A)
prop_Maybe_Semicomonad_comm f g = checkFnEqual (law_Semicomonad_comm f g)

prop_Maybe_Semicomonad1_comm ::
    Fun (Maybe B) C -> Fun (Maybe A) B -> FnProp (Maybe A)
prop_Maybe_Semicomonad1_comm f g = checkFnEqual (law_Semicomonad1_comm f g)

prop_Maybe_Semicomonad1_comm' ::
    Fun (Maybe B) C -> Fun (Maybe A) B -> FnProp (Maybe A)
prop_Maybe_Semicomonad1_comm' (Fn f) (Fn g) =
    checkFnEqual (law_Semicomonad1_comm' f g)



prop_Either_Functor_id :: FnProp (Either Int A)
prop_Either_Functor_id = checkFnEqual law_Functor_id

prop_Either_Functor_comp :: Fun B C -> Fun A B -> FnProp (Either Int A)
prop_Either_Functor_comp f g = checkFnEqual (law_Functor_comp f g)

prop_Either_Semicomonad_comm ::
    Fun (Either Int B) C -> Fun (Either Int A) B -> FnProp (Either Int A)
prop_Either_Semicomonad_comm f g = checkFnEqual (law_Semicomonad_comm f g)

prop_Either_Semicomonad1_comm ::
    Fun (Either Int B) C -> Fun (Either Int A) B -> FnProp (Either Int A)
prop_Either_Semicomonad1_comm f g = checkFnEqual (law_Semicomonad1_comm f g)

prop_Either_Semicomonad1_comm' ::
    Fun (Either Int B) C -> Fun (Either Int A) B -> FnProp (Either Int A)
prop_Either_Semicomonad1_comm' (Fn f) (Fn g) =
    checkFnEqual (law_Semicomonad1_comm' f g)



prop_Tuple_Functor_id :: FnProp (Int, A)
prop_Tuple_Functor_id = checkFnEqual law_Functor_id

prop_Tuple_Functor_comp :: Fun B C -> Fun A B -> FnProp (Int, A)
prop_Tuple_Functor_comp f g = checkFnEqual (law_Functor_comp f g)

prop_Tuple_Semicomonad_comm ::
    Fun (Int, B) C -> Fun (Int, A) B -> FnProp (Int, A)
prop_Tuple_Semicomonad_comm f g = checkFnEqual (law_Semicomonad_comm f g)

prop_Tuple_Comonad_id :: FnProp (Int, A)
prop_Tuple_Comonad_id = checkFnEqual (law_Comonad_id (Proxy @(->)))

prop_Tuple_Comonad_apply :: Fun (Int, A) B -> FnProp (Int, A)
prop_Tuple_Comonad_apply f = checkFnEqual (law_Comonad_apply f)

prop_Tuple_Semicomonad1_comm ::
    Fun (Int, B) C -> Fun (Int, A) B -> FnProp (Int, A)
prop_Tuple_Semicomonad1_comm f g = checkFnEqual (law_Semicomonad1_comm f g)

prop_Tuple_Semicomonad1_comm' ::
    Fun (Int, B) C -> Fun (Int, A) B -> FnProp (Int, A)
prop_Tuple_Semicomonad1_comm' (Fn f) (Fn g) =
    checkFnEqual (law_Semicomonad1_comm' f g)



-- prop_Function_Semicomonad_comm ::
--     Fun (Fun Int B) C -> Fun (Fun Int A) B -> Fun Int A -> Property
-- prop_Function_Semicomonad_comm = law_Semicomonad_comm

-- prop_Function_Comonad_id :: FnProp (Fun Int A)
-- prop_Function_Comonad_id = checkFnEqual (law_Comonad_id (Proxy @(->)))



prop_List_Functor_id :: FnProp [A]
prop_List_Functor_id = checkFnEqual law_Functor_id

prop_List_Functor_comp :: Fun B C -> Fun A B -> FnProp [A]
prop_List_Functor_comp f g = checkFnEqual (law_Functor_comp f g)

prop_List_Semicomonad_comm :: Fun [B] C -> Fun [A] B -> FnProp [A]
prop_List_Semicomonad_comm f g = checkFnEqual (law_Semicomonad_comm f g)

prop_List_Semicomonad1_comm :: Fun [B] C -> Fun [A] B -> FnProp [A]
prop_List_Semicomonad1_comm f g = checkFnEqual (law_Semicomonad1_comm f g)

prop_List_Semicomonad1_comm' :: Fun [B] C -> Fun [A] B -> FnProp [A]
prop_List_Semicomonad1_comm' (Fn f) (Fn g) =
    checkFnEqual (law_Semicomonad1_comm' f g)



type FA = Either Int
type FB = (,) Double
type FC = []

prop_Sum_Functor_id :: FnProp (Sum FA FB A)
prop_Sum_Functor_id = checkFnEqual law_Functor_id

prop_Sum_Functor_comp :: Fun B C -> Fun A B -> FnProp (Sum FA FB A)
prop_Sum_Functor_comp f g = checkFnEqual (law_Functor_comp f g)



prop_Product_Functor_id :: FnProp (Product FA FB A)
prop_Product_Functor_id = checkFnEqual law_Functor_id

prop_Product_Functor_comp :: Fun B C -> Fun A B -> FnProp (Product FA FB A)
prop_Product_Functor_comp f g = checkFnEqual (law_Functor_comp f g)



prop_Compose_Functor_id :: FnProp (Compose FA FB A)
prop_Compose_Functor_id = checkFnEqual law_Functor_id

prop_Compose_Functor_comp :: Fun B C -> Fun A B -> FnProp (Compose FA FB A)
prop_Compose_Functor_comp f g = checkFnEqual (law_Functor_comp f g)
