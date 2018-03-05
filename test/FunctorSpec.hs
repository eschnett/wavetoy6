{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module FunctorSpec where

import Prelude hiding (Functor(..))

import Data.Constraint
import Data.Functor.Identity
import Data.Proxy

import Test.QuickCheck
import Test.QuickCheck.Instances()
import Test.QuickCheck.Poly

import Category
import Unboxed



tmpl_Functor_id :: forall f a.
                   (Functor f
                   , Dom f a
                   , Cod f (f a)
                   , Morphism (FunMor f (MId (Dom f)))
                   , MorCat (FunMor f (MId (Dom f))) (f a)
                   , Eq (f a), Show (f a)
                   ) => f a -> Property
tmpl_Functor_id xs = fmap MId `chase` xs === (MId @(Cod f)) `chase` xs

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

prop_Functor_id_Proxy :: Proxy A -> Property
prop_Functor_id_Proxy = tmpl_Functor_id

prop_Functor_comp_Proxy :: Fun B C -> Fun A B -> Proxy A -> Property
prop_Functor_comp_Proxy = tmpl_Functor_comp

prop_Functor_id_Identity :: Identity A -> Property
prop_Functor_id_Identity = tmpl_Functor_id

prop_Functor_comp_Identity :: Fun B C -> Fun A B -> Identity A -> Property
prop_Functor_comp_Identity = tmpl_Functor_comp

prop_Functor_id_Maybe :: Maybe A -> Property
prop_Functor_id_Maybe = tmpl_Functor_id

prop_Functor_comp_Maybe :: Fun B C -> Fun A B -> Maybe A -> Property
prop_Functor_comp_Maybe = tmpl_Functor_comp

prop_Functor_id_Either :: Either Int A -> Property
prop_Functor_id_Either = tmpl_Functor_id

prop_Functor_comp_Either :: Fun B C -> Fun A B -> Either Int A -> Property
prop_Functor_comp_Either = tmpl_Functor_comp

prop_Functor_id_Tuple :: (Int, A) -> Property
prop_Functor_id_Tuple = tmpl_Functor_id

prop_Functor_comp_Tuple :: Fun B C -> Fun A B -> (Int, A) -> Property
prop_Functor_comp_Tuple = tmpl_Functor_comp

prop_Functor_id_List :: [A] -> Property
prop_Functor_id_List = tmpl_Functor_id

prop_Functor_comp_List :: Fun B C -> Fun A B -> [A] -> Property
prop_Functor_comp_List = tmpl_Functor_comp



type UA = Int
type UB = Double
type UC = Char
type N = 10

prop_Functor_id_Vector :: Vector A -> Property
prop_Functor_id_Vector = tmpl_Functor_id

prop_Functor_comp_Vector :: Fun B C -> Fun A B -> Vector A -> Property
prop_Functor_comp_Vector = tmpl_Functor_comp

prop_Functor_id_UVector :: UVector UA -> Property
prop_Functor_id_UVector = tmpl_Functor_id

prop_Functor_comp_UVector ::
    (UB -#> UC) -> (UA -#> UB) -> UVector UA -> Property
prop_Functor_comp_UVector = tmpl_Functor_comp

prop_Functor_id_NVector :: NVector N A -> Property
prop_Functor_id_NVector = tmpl_Functor_id

prop_Functor_comp_NVector :: Fun B C -> Fun A B -> NVector N A -> Property
prop_Functor_comp_NVector = tmpl_Functor_comp

prop_Functor_id_NUVector :: NUVector N UA -> Property
prop_Functor_id_NUVector = tmpl_Functor_id

prop_Functor_comp_NUVector ::
    (UB -#> UC) -> (UA -#> UB) -> NUVector N UA -> Property
prop_Functor_comp_NUVector = tmpl_Functor_comp

prop_Functor_id_CNVector :: CNVector N A -> Property
prop_Functor_id_CNVector = tmpl_Functor_id

prop_Functor_comp_CNVector :: Fun B C -> Fun A B -> CNVector N A -> Property
prop_Functor_comp_CNVector = tmpl_Functor_comp

prop_Functor_id_CNUVector :: CNUVector N UA -> Property
prop_Functor_id_CNUVector = tmpl_Functor_id

prop_Functor_comp_CNUVector ::
    (UB -#> UC) -> (UA -#> UB) -> CNUVector N UA -> Property
prop_Functor_comp_CNUVector = tmpl_Functor_comp
