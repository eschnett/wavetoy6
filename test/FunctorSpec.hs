{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module FunctorSpec where

import Prelude hiding (Functor(..))

import Data.Complex
import Data.Constraint
import Data.Functor.Compose
import Data.Functor.Identity
import Data.Functor.Product
import Data.Functor.Sum
import Data.Proxy

import Test.QuickCheck
import Test.QuickCheck.Instances()
import Test.QuickCheck.Poly

import CNVector
import Category
import Functor
import NVector
import Unboxed
import Vector



-- fmap id == id
tmpl_Functor_id :: forall f a.
                   (Functor f
                   , Dom f a
                   , Cod f (f a)
                   , Morphism (FunMor f (MId (Dom f)))
                   , MorCat (FunMor f (MId (Dom f))) (f a)
                   , Eq (f a), Show (f a)
                   ) => f a -> Property
tmpl_Functor_id xs = fmap MId `chase` xs === (MId @(Cod f)) `chase` xs

-- fmap (f . g) == fmap f . fmap g
tmpl_Functor_comp :: forall f m n mn a b c.
                     ( Functor f
                     , Morphism m, MorCat m ~ Dom f
                     , Morphism n, MorCat n ~ Dom f
                     , mn ~ MCompose m n b
                     , Dom f a
                     , Dom f b
                     , Dom f c
                     , Eq (f c), Show (f c)
                     ) => m b c -> n a b -> f a -> Property
tmpl_Functor_comp f g xs =
    fmap (f `MCompose` g) `chase` xs === (fmap f `MCompose` fmap g) `chase` xs
         \\ (proveFunCod Proxy :: Dom f a :- Cod f (f a))
         \\ (proveFunMor (Proxy @f, Proxy @m) ::
                 (Morphism m, MorCat m ~ Dom f)
                 :- (Morphism (FunMor f m), MorCat (FunMor f m) ~ Cod f))
         \\ (proveFunMor (Proxy @f, Proxy @n) ::
                 (Morphism n, MorCat n ~ Dom f)
                 :- (Morphism (FunMor f n), MorCat (FunMor f n) ~ Cod f))
         \\ (proveFunMor (Proxy @f, Proxy @mn) ::
                 (Morphism mn, MorCat mn ~ Dom f)
                 :- (Morphism (FunMor f mn), MorCat (FunMor f mn) ~ Cod f))



prop_Proxy_Functor_id :: Proxy A -> Property
prop_Proxy_Functor_id = tmpl_Functor_id

prop_Proxy_Functor_comp :: Fun B C -> Fun A B -> Proxy A -> Property
prop_Proxy_Functor_comp = tmpl_Functor_comp

prop_Identity_Functor_id :: Identity A -> Property
prop_Identity_Functor_id = tmpl_Functor_id

prop_Identity_Functor_comp :: Fun B C -> Fun A B -> Identity A -> Property
prop_Identity_Functor_comp = tmpl_Functor_comp

prop_Maybe_Functor_id :: Maybe A -> Property
prop_Maybe_Functor_id = tmpl_Functor_id

prop_Maybe_Functor_comp :: Fun B C -> Fun A B -> Maybe A -> Property
prop_Maybe_Functor_comp = tmpl_Functor_comp

prop_Either_Functor_id :: Either Int A -> Property
prop_Either_Functor_id = tmpl_Functor_id

prop_Either_Functor_comp :: Fun B C -> Fun A B -> Either Int A -> Property
prop_Either_Functor_comp = tmpl_Functor_comp

prop_Tuple_Functor_id :: (Int, A) -> Property
prop_Tuple_Functor_id = tmpl_Functor_id

prop_Tuple_Functor_comp :: Fun B C -> Fun A B -> (Int, A) -> Property
prop_Tuple_Functor_comp = tmpl_Functor_comp

prop_List_Functor_id :: [A] -> Property
prop_List_Functor_id = tmpl_Functor_id

prop_List_Functor_comp :: Fun B C -> Fun A B -> [A] -> Property
prop_List_Functor_comp = tmpl_Functor_comp



type FA = Either Int
type FB = (,) Double
type FC = []

prop_Sum_Functor_id :: Sum FA FB A -> Property
prop_Sum_Functor_id = tmpl_Functor_id

prop_Sum_Functor_comp :: Fun B C -> Fun A B -> Sum FA FB A -> Property
prop_Sum_Functor_comp = tmpl_Functor_comp

prop_Product_Functor_id :: Product FA FB A -> Property
prop_Product_Functor_id = tmpl_Functor_id

prop_Product_Functor_comp :: Fun B C -> Fun A B -> Product FA FB A -> Property
prop_Product_Functor_comp = tmpl_Functor_comp

prop_Compose_Functor_id :: Compose FA FB A -> Property
prop_Compose_Functor_id = tmpl_Functor_id

prop_Compose_Functor_comp :: Fun B C -> Fun A B -> Compose FA FB A -> Property
prop_Compose_Functor_comp = tmpl_Functor_comp



type UA = Int
type UB = Double
type UC = Complex Double
type N = 10

prop_Vector_Functor_id :: Vector A -> Property
prop_Vector_Functor_id = tmpl_Functor_id

prop_Vector_Functor_comp :: Fun B C -> Fun A B -> Vector A -> Property
prop_Vector_Functor_comp = tmpl_Functor_comp

prop_UVector_Functor_id :: UVector UA -> Property
prop_UVector_Functor_id = tmpl_Functor_id

prop_UVector_Functor_comp ::
    (UB -#> UC) -> (UA -#> UB) -> UVector UA -> Property
prop_UVector_Functor_comp = tmpl_Functor_comp

prop_NVector_Functor_id :: NVector N A -> Property
prop_NVector_Functor_id = tmpl_Functor_id

prop_NVector_Functor_comp :: Fun B C -> Fun A B -> NVector N A -> Property
prop_NVector_Functor_comp = tmpl_Functor_comp

prop_NUVector_Functor_id :: NUVector N UA -> Property
prop_NUVector_Functor_id = tmpl_Functor_id

prop_NUVector_Functor_comp ::
    (UB -#> UC) -> (UA -#> UB) -> NUVector N UA -> Property
prop_NUVector_Functor_comp = tmpl_Functor_comp

prop_CNVector_Functor_id :: CNVector N A -> Property
prop_CNVector_Functor_id = tmpl_Functor_id

prop_CNVector_Functor_comp :: Fun B C -> Fun A B -> CNVector N A -> Property
prop_CNVector_Functor_comp = tmpl_Functor_comp

prop_CNUVector_Functor_id :: CNUVector N UA -> Property
prop_CNUVector_Functor_id = tmpl_Functor_id

prop_CNUVector_Functor_comp ::
    (UB -#> UC) -> (UA -#> UB) -> CNUVector N UA -> Property
prop_CNUVector_Functor_comp = tmpl_Functor_comp
