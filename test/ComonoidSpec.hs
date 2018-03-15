module ComonoidSpec where

import Prelude as P

import Data.Monoid hiding ((<>))
import Data.Proxy
import Data.Semigroup

import Test.QuickCheck

import Comonoid
import Functor
import Hask()



-- instance Semigroup A where
--     A a <> A b = A (getSum (Sum a <> Sum b))
-- instance Monoid A where
--     mempty = A (getSum mempty)
--     mappend = (<>)
-- 
-- instance Cosemigroup A where
-- instance Comonoid A where
--     counit (A a) = a == 0
--     split (A a) = (A 1, A (a - 1))
-- 
-- instance Semigroup B where
--     B a <> B b = B (getSum (Sum a <> Sum b))
-- instance Monoid B where
--     mempty = B (getSum mempty)
--     mappend = (<>)
-- 
-- instance Cosemigroup B where
-- instance Comonoid B where
--     counit (B a) = a == 0
--     split (B a) = (B 1, B (a - 1))

newtype A = A (Sum Integer)
    deriving ( Eq, Ord, Read, Show, Monoid, Num, Semigroup
             , Arbitrary
             , Cosemigroup, Comonoid
             )
newtype B = B (Sum Integer)
    deriving ( Eq, Ord, Read, Show, Monoid, Num, Semigroup
             , Arbitrary
             , Cosemigroup, Comonoid
             )



prop_Proxy_Cosemigroup_inv :: Proxy A -> Property
prop_Proxy_Cosemigroup_inv = law_Cosemigroup_inv

prop_Proxy_Comonoid_counit :: Proxy A -> Property
prop_Proxy_Comonoid_counit = law_Comonoid_counit

prop_Proxy_Comonoid_inv :: Proxy A -> Property
prop_Proxy_Comonoid_inv = law_Comonoid_inv



prop_Maybe_Cosemigroup_inv :: Maybe A -> Property
prop_Maybe_Cosemigroup_inv = law_Cosemigroup_inv

prop_Maybe_Comonoid_counit :: Maybe A -> Property
prop_Maybe_Comonoid_counit = law_Comonoid_counit

prop_Maybe_Comonoid_inv :: Maybe A -> Property
prop_Maybe_Comonoid_inv = law_Comonoid_inv



-- Either is not a Monoid. (Then why is it a Semigroup?)
-- prop_Either_Cosemigroup_inv :: Either A B -> Property
-- prop_Either_Cosemigroup_inv = law_Cosemigroup_inv
-- 
-- prop_Either_Comonoid_counit :: Either A B -> Property
-- prop_Either_Comonoid_counit = law_Comonoid_counit
-- 
-- prop_Either_Comonoid_inv :: Either A B -> Property
-- prop_Either_Comonoid_inv = law_Comonoid_inv



prop_Tuple_Cosemigroup_inv :: (A, B) -> Property
prop_Tuple_Cosemigroup_inv = law_Cosemigroup_inv

prop_Tuple_Comonoid_counit :: (A, B) -> Property
prop_Tuple_Comonoid_counit = law_Comonoid_counit

prop_Tuple_Comonoid_inv :: (A, B) -> Property
prop_Tuple_Comonoid_inv = law_Comonoid_inv



prop_List_Cosemigroup_inv :: [A] -> Property
prop_List_Cosemigroup_inv = law_Cosemigroup_inv

prop_List_Comonoid_counit :: [A] -> Property
prop_List_Comonoid_counit = law_Comonoid_counit

prop_List_Comonoid_inv :: [A] -> Property
prop_List_Comonoid_inv = law_Comonoid_inv



prop_Counter_Cosemigroup :: NonNegative Int -> Property
prop_Counter_Cosemigroup (NonNegative n) =
    take n (mapUnfold getCounter (Counter 0)) === [0 .. n - 1]

prop_CountDown_Cosemigroup :: NonNegative Int -> Property
prop_CountDown_Cosemigroup (NonNegative n) =
    mapUnfold getCountDown (CountDown n) === [n, n - 1 .. 1]

prop_Counted_Cosemigroup :: NonNegative Int -> A -> Property
prop_Counted_Cosemigroup (NonNegative n) x =
    unfold (Counted n x) ===
           take n (mapUnfold (Counted 1 . getForever) (Forever x))

prop_Forever_Cosemigroup :: NonNegative Int -> A -> Property
prop_Forever_Cosemigroup (NonNegative n) x =
    P.length (take n (unfold (Forever x))) === n
