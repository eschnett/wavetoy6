{-# LANGUAGE UndecidableInstances #-}

module Category ( CatKind
                , ObjKind
                , MorKind
                , Category(..)
                , Subcategory(..)
                , ProveSubcategory
                , Object(..)
                , Morphism(..)
                , Discretization(..)
                , MId(..)
                , MCompose(..)
                , Functor(..)
                , Apply(..)
                , Applicative(..)
                ) where

import Prelude hiding ( Functor(..)
                      , Applicative(..)
                      )

import Data.Constraint
import Data.Kind
import Data.Proxy



type CatKind = Type -> Constraint
type ObjKind = Type
type MorKind = Type -> Type -> Type



-- | Constraints
class Category (k :: CatKind) where
    -- | This is unused
    type Obj k :: ObjKind -> Constraint
    type Obj k = k

class (Category s, Category k)
        => Subcategory (s :: CatKind) (k :: CatKind) where
    proveSubcategory :: s a :- k a

-- | 'Subcategory' relations form a monoid
instance Category k => Subcategory k k where
    proveSubcategory = refl

-- | Prove that 'k1' is a subcategory of 'k3' by explicitly providing
-- a path via 'k2'. (If we could express 'exists k2', then this would
-- not be necessary.)
class (Category k1, Category k2, Category k3,
       Subcategory k2 k3, Subcategory k1 k2)
    => ProveSubcategory k2 k1 k3

instance (Category k1, Category k3, ProveSubcategory k2 k1 k3)
        => Subcategory k1 k3 where
    proveSubcategory =
        trans
        (proveSubcategory :: k2 a :- k3 a)
        (proveSubcategory :: k1 a :- k2 a)



-- | Types
-- (This class is unused.)
class Object (o :: ObjKind) where
    type ObjCat o :: CatKind



-- | Functions
class Category (MorCat m) => Morphism (m :: MorKind) where
    type MorCat m :: CatKind
    proveChase :: m a b -> MorCat m a :- MorCat m b
    -- | Each morphism has a dinatural transformation to Haskell functions
    chase :: MorCat m a => a `m` b -> a -> b
    -- type FromHaskC m a b :: Constraint
    -- -- type FromHaskC m a b = (MorCat m a, MorCat m b)
    -- fromHask :: FromHaskC m a b => (a -> b) -> a `m` b

class Morphism m => Discretization (m :: MorKind) where
    -- | A morphism might have an "approximate dinatural
    -- transformation" from Haskell functions
    discretize :: (MorCat m a, MorCat m b) => (a -> b) -> a `m` b



data MId (k :: CatKind) a b where
    MId :: MId k a a
instance Category k => Morphism (MId k) where
    type MorCat (MId k) = k
    proveChase MId = refl
    chase MId = id
    -- type FromHaskC (MId k) a b = a ~ b
    -- fromHask _ = MId

data MCompose m n b a c where
    MCompose :: m b c -> n a b -> MCompose m n b a c
instance (Morphism m, Morphism n, MorCat m ~ MorCat n)
        => Morphism (MCompose m n b) where
    type MorCat (MCompose m n b) = MorCat m
    proveChase (MCompose f g) = trans (proveChase f) (proveChase g)
    chase (MCompose f g) =
        case proveChase g of Sub Dict -> chase f . chase g
    -- | We arbitrarily split f === id . f
    -- type FromHaskC (MCompose m n b) a c =
    --     (b ~ c, FromHaskC m b c, FromHaskC n a b)
    -- fromHask f = MCompose (fromHask id) (fromHask f)



-- | Functor
class (Category (Dom f), Category (Cod f)) => Functor f where
    type Dom f :: CatKind
    type Cod f :: CatKind
    type FunMor f (m :: MorKind) :: MorKind
    -- type FunMor f :: MorKind -> MorKind
    proveFunctor :: Proxy f -> Dom f a :- Cod f (f a)
    proveFunMor ::
        (n ~ FunMor f m)
        => (Proxy f, Proxy m)
        -> (Morphism m, MorCat m ~ Dom f) :- (Morphism n, MorCat n ~ Cod f)
    -- TODO: allow 'Subcategory (MorCat m) (Dom f)'
    fmap ::
        (Dom f a, Dom f b, Morphism m, MorCat m ~ Dom f, n ~ FunMor f m)
        => a `m` b -> f a `n` f b

-- | Apply
class Functor f => Apply f where
    -- liftA2' :: ( Dom f a, Dom f b, Dom f c
    --            , Morphism m, MorCat m ~ Dom f, n ~ FunMor f m
    --            )
    --            => (a, b) `m` c -> (f a, f b) `n` f c
    liftA2 :: ( Dom f a, Dom f b, Dom f c
              , Morphism m, MorCat m ~ Dom f, n ~ FunMor f m
              )
              => a `m` (b `m` c) -> f a `n` (f b `n` f c)

-- | Applicative
class Apply f => Applicative f where
    pure :: Dom f a => a -> f a
