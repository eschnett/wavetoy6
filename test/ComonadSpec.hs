{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module ComonadSpec where

import Prelude hiding (Functor(..))

-- import Data.Constraint
import Data.Functor.Compose
import Data.Functor.Const
import Data.Functor.Product
import Data.Functor.Sum
import Data.Functor.Identity
import qualified Data.Vector as V
import Data.Proxy

import Test.QuickCheck
import Test.QuickCheck.Function
import Test.QuickCheck.Instances()
import Test.QuickCheck.Poly

import Category
import Hask
import Unboxed



-- TODO: declare (or find!) this elsewhere
instance Function a => Function (Identity a) where
    function = functionMap runIdentity Identity

instance Function a => Function (Const a b) where
    function = functionMap getConst Const



-- Semicomonad

-- extend f . extend g = extend (f . extend g)
tmpl_Semicomonad_comm :: forall f m n mn a b c.
                         ( Semicomonad f
                         , Morphism m, MorCat m ~ Dom f
                         , Morphism n, MorCat n ~ Dom f
                         , mn ~ MCompose m (FunMor f n) (f b)
                         , Eq (f c), Show (f c)
                         -- TODO: prove the ones below
                         , Morphism (FunMor f m), MorCat (FunMor f m) ~ Cod f
                         , Morphism (FunMor f n), MorCat (FunMor f n) ~ Cod f
                         , Morphism (FunMor f mn), MorCat (FunMor f mn) ~ Cod f
                         , Cod f (f a)
                         ) => m (f b) c -> n (f a) b -> f a -> Property
tmpl_Semicomonad_comm f g xs =
    (extend f `MCompose` extend g) `chase` xs ===
        (extend (f `MCompose` extend g)) `chase` xs



-- Comonad

-- extend extract = id
tmpl_Comonad_id :: forall f m n a.
                   ( Comonad f
                   , Morphism m, MorCat m ~ Dom f
                   , n ~ FunMor f m
                   , Eq (f a), Show (f a)
                   -- TODO: prove the ones below
                   , Morphism n, MorCat n ~ Cod f
                   , Morphism (FunMor f n), MorCat (FunMor f n) ~ Cod f
                   , Cod f (f a)
                   ) => Proxy m -> f a -> Property
tmpl_Comonad_id _ xs = extend (extract' (Proxy @m)) `chase` xs === xs

-- extract . extend f = f
tmpl_Comonad_apply :: forall f m a b.
                      ( Comonad f
                      , Morphism m, MorCat m ~ Dom f
                      , Morphism (FunMor f m), MorCat (FunMor f m) ~ Cod f
                      , Eq b, Show b
                      -- TODO: prove the ones below
                      , Cod f (f a)
                      ) => m (f a) b -> f a -> Property
tmpl_Comonad_apply f xs =
    (extract' (Proxy @m) `MCompose` extend f) `chase` xs === f `chase` xs



prop_Proxy_Semicomonad_comm ::
    Fun (Proxy B) C -> Fun (Proxy A) B -> Proxy A -> Property
prop_Proxy_Semicomonad_comm = tmpl_Semicomonad_comm



prop_Identity_Semicomonad_comm ::
    Fun (Identity B) C -> Fun (Identity A) B -> Identity A -> Property
prop_Identity_Semicomonad_comm = tmpl_Semicomonad_comm

prop_Identity_Comonad_id :: Identity A -> Property
prop_Identity_Comonad_id = tmpl_Comonad_id (Proxy @(->))

prop_Identity_Comonad_apply :: Fun (Identity A) B -> Identity A -> Property
prop_Identity_Comonad_apply = tmpl_Comonad_apply



prop_Maybe_Semicomonad_comm ::
    Fun (Maybe B) C -> Fun (Maybe A) B -> Maybe A -> Property
prop_Maybe_Semicomonad_comm = tmpl_Semicomonad_comm



prop_Either_Semicomonad_comm ::
    Fun (Either Int B) C -> Fun (Either Int A) B -> Either Int A -> Property
prop_Either_Semicomonad_comm = tmpl_Semicomonad_comm



prop_Tuple_Semicomonad_comm ::
    Fun (Int, B) C -> Fun (Int, A) B -> (Int, A) -> Property
prop_Tuple_Semicomonad_comm = tmpl_Semicomonad_comm

prop_Tuple_Comonad_id :: (Int, A) -> Property
prop_Tuple_Comonad_id = tmpl_Comonad_id (Proxy @(->))

prop_Tuple_Comonad_apply :: Fun (Int, A) B -> (Int, A) -> Property
prop_Tuple_Comonad_apply = tmpl_Comonad_apply



-- prop_Function_Semicomonad_comm ::
--     Fun (Fun Int B) C -> Fun (Fun Int A) B -> Fun Int A -> Property
-- prop_Function_Semicomonad_comm = tmpl_Semicomonad_comm

-- prop_Function_Comonad_id :: Fun Int A -> Property
-- prop_Function_Comonad_id = tmpl_Comonad_id (Proxy @(->))



prop_List_Semicomonad_comm ::
    Fun [B] C -> Fun [A] B -> [A] -> Property
prop_List_Semicomonad_comm = tmpl_Semicomonad_comm



type FA = Either Int
type FB = (,) Double
type FC = []



-- prop_Sum_Semicomonad_comm ::
--     Fun (Sum FA FB B) C -> Fun (Sum FA FB A) B -> Sum FA FB A -> Property
-- prop_Sum_Semicomonad_comm = tmpl_Semicomonad_comm

-- Product

-- Compose



type UA = Int
type UB = Double
type UC = Char
type N = 10



prop_Vector_Semicomonad_comm ::
    Fun (Vector B) C -> Fun (Vector A) B -> Vector A -> Property
prop_Vector_Semicomonad_comm = tmpl_Semicomonad_comm



prop_NVector_Semicomonad_comm ::
    Fun (NVector N B) C -> Fun (NVector N A) B -> NVector N A -> Property
prop_NVector_Semicomonad_comm = tmpl_Semicomonad_comm



prop_CNVector_Semicomonad_comm ::
    Fun (CNVector N B) C -> Fun (CNVector N A) B -> CNVector N A -> Property
prop_CNVector_Semicomonad_comm = tmpl_Semicomonad_comm

prop_CNVector_Comonad_id :: CNVector N A -> Property
prop_CNVector_Comonad_id = tmpl_Comonad_id (Proxy @(->))

prop_CNVector_Comonad_apply :: Fun (CNVector N A) B -> CNVector N A -> Property
prop_CNVector_Comonad_apply = tmpl_Comonad_apply
