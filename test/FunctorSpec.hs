{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module FunctorSpec where

import Prelude hiding (Functor(..))

import Data.Functor.Identity
import Data.Proxy

import Test.QuickCheck
import Test.QuickCheck.Instances()
import Test.QuickCheck.Poly

import Category
import Hask



tmpl_Functor_id :: forall f.
                   (Functor f
                   , Dom f A
                   , Cod f (f A)
                   , Morphism (FunMor f (MId (Dom f)))
                   , MorCat (FunMor f (MId (Dom f))) (f A)
                   , Eq (f A), Show (f A)
                   ) => Proxy f -> f A -> Property
tmpl_Functor_id Proxy xs = fmap MId `chase` xs === (MId @(Cod f)) `chase` xs

tmpl_Functor_comp :: forall f.
                     (Functor f
                     , Dom f ~ Hask -- TODO: Why???
                     , Morphism (FunMor f (->))
                     , MorCat (FunMor f (->)) (f A)
                     , Morphism (FunMor f (MCompose (->) (->) B))
                     , MorCat (FunMor f (MCompose (->) (->) B)) (f A)
                     , Eq (f C), Show (f C)
                     ) => Proxy f -> Fun B C -> Fun A B -> f A -> Property
tmpl_Functor_comp Proxy (Fn f) (Fn g) xs =
    fmap (f `MCompose` g) `chase` xs === (fmap f `MCompose` fmap g) `chase` xs



prop_Functor_id_Proxy :: Proxy A -> Property
prop_Functor_id_Proxy = tmpl_Functor_id (Proxy @Proxy)

prop_Functor_comp_Proxy :: Fun B C -> Fun A B -> Proxy A -> Property
prop_Functor_comp_Proxy = tmpl_Functor_comp (Proxy @Proxy)

prop_Functor_id_Identity :: Identity A -> Property
prop_Functor_id_Identity = tmpl_Functor_id (Proxy @Identity)

prop_Functor_comp_Identity :: Fun B C -> Fun A B -> Identity A -> Property
prop_Functor_comp_Identity = tmpl_Functor_comp (Proxy @Identity)

prop_Functor_id_Either :: Either Int A -> Property
prop_Functor_id_Either = tmpl_Functor_id (Proxy @(Either Int))

prop_Functor_comp_Either :: Fun B C -> Fun A B -> Either Int A -> Property
prop_Functor_comp_Either = tmpl_Functor_comp (Proxy @(Either Int))

prop_Functor_id_Tuple :: (Int, A) -> Property
prop_Functor_id_Tuple = tmpl_Functor_id (Proxy @((,) Int))

prop_Functor_comp_Tuple :: Fun B C -> Fun A B -> (Int, A) -> Property
prop_Functor_comp_Tuple = tmpl_Functor_comp (Proxy @((,) Int))

prop_Functor_id_List :: [A] -> Property
prop_Functor_id_List = tmpl_Functor_id (Proxy @[])

prop_Functor_comp_List :: Fun B C -> Fun A B -> [A] -> Property
prop_Functor_comp_List = tmpl_Functor_comp (Proxy @[])
