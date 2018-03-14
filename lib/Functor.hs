module Functor ( Functor(..)
               , Unfoldable(..)
               , Foldable(..)
               , Apply(..)
               , Applicative(..)
               , Alt(..)
               , Alternative(..)
               , Distributive(..)
               , Traversable(..)
               , Monad(..)
               ) where

import Prelude hiding ( Foldable(..)
                      , Functor(..)
                      , Applicative(..)
                      , Traversable(..)
                      , Monad(..)
                      )

import Data.Constraint
import Data.Monoid hiding (Alt(..))
import Data.Proxy

import Category
import Comonoid



-- | Functor
class (Category (Dom f), Category (Cod f)) => Functor f where
    type Dom f :: CatKind
    type Cod f :: CatKind
    type FunMor f (m :: MorKind) :: MorKind
    -- type FunMor f :: MorKind -> MorKind
    -- TODO: Rename this to 'proveFunObj'?
    proveFunCod :: Proxy f -> Dom f a :- Cod f (f a)
    proveFunMor ::
        (n ~ FunMor f m)
        => (Proxy f, Proxy m)
        -> (Morphism m, MorCat m ~ Dom f) :- (Morphism n, MorCat n ~ Cod f)
    -- TODO: allow 'Subcategory (MorCat m) (Dom f)'
    fmap ::
        (Dom f a, Dom f b, Morphism m, MorCat m ~ Dom f, n ~ FunMor f m)
        => a `m` b -> f a `n` f b

-- class (forall a b. (Cod f dom (f a), Cod f dom (f b)))
--         => Functor f (dom :: CatKind) where
--     type Dom f dom = dom :: CatKind
--     type Dom f dom = dom
--     type Cod f dom :: CatKind
--     fmap :: (Dom f a, Dom f b) => (a -> b) -> f a -> f b

-- | Unfoldable
class Functor f => Unfoldable f where
    mapUnfold :: (Comonoid a, Dom f b) => (a -> b) -> a -> f b
    unfold :: (Comonoid a, Dom f a) => a -> f a
    unfold = mapUnfold id
    -- TODO: provide default implementation
    fromList :: (Dom f a, Dom [] a) => [a] -> f a
    fromList = mapUnfold head

-- | Foldable
-- E. Kmett: "Folds are closed, corepresentable profunctors"
-- ... what are then Unfolds?
class Functor f => Foldable f where
    foldMap :: (Dom f a, Monoid b) => (a -> b) -> f a -> b
    fold :: (Dom f a, Monoid a) => f a -> a
    fold = foldMap id
    null :: Dom f a => f a -> Bool
    null = getAll . foldMap (All . const False)
    length :: Dom f a => f a -> Int
    length = getSum . foldMap (Sum . const 1)
    elem :: (Dom f a, Eq a) => a -> f a -> Bool
    elem x = getAny . foldMap (Any . (== x))
    -- TODO: provide default implementation
    toList :: (Dom f a, Dom [] a) => f a -> [a]
    toList = foldMap (:[])

-- maximum, minimum, sum, product

-- | Apply
class Functor f => Apply f where
    -- TODO: Should this be the preferred way, since it works for
    -- categories without functions?
    -- TODO: Add default implementations based on MCurry
    liftA2' :: ( Dom f a, Dom f b, Dom f c
               , Morphism m, MorCat m ~ Dom f, n ~ FunMor f m
               )
               => CProduct (Dom f) a b `m` c ->
                   CProduct (Cod f) (f a) (f b) `n` f c
    -- TODO: Should 'liftA2' allow for different morphisms? it seems
    -- 'liftA2' only works for categories that have function types;
    -- otherwise, currying won't work
    liftA2 :: ( Dom f a, Dom f b, Dom f c
              , Morphism m, MorCat m ~ Dom f
              , Morphism n, MorCat n ~ Dom f
              , p ~ FunMor f m
              , q ~ FunMor f n
              )
              => a `m` (b `n` c) -> f a `p` (f b `q` f c)

-- | Applicative
class Apply f => Applicative f where
    pure' :: (Dom f a, Morphism m, MorCat m ~ Dom f, n ~ FunMor f m)
             => Proxy m -> a `n` f a
    pure :: Dom f a => a -> f a

-- | Alt
class Applicative f => Alt f where
    (<|>) :: f a -> f a -> f a

-- | Alternative
class Alt f => Alternative f where
    empty :: f a

-- | Distributive
class (Functor f, Dom f ~ Cod f) => Distributive f where
    cotraverseMap :: (Foldable g, Morphism m)
                     => g b `m` c -> a `m` f b -> g a -> f c
    -- collect = cotraverseMap MId
    -- distribute = cotraverseMap MId MId

-- | Traversable
class (Functor f, Dom f ~ Cod f) => Traversable f where
    mapTraverse :: (Applicative g, Morphism m)
                   => f b `m` c -> a `m` g b -> f a -> g c
   -- traverse = mapTraverse MId
   -- sequence = mapTraverse MId MId

-- | Monad
class (Applicative f, Dom f ~ Cod f) => Monad f where
    (>>=) :: (Morphism m, MorCat m ~ Dom f) => f a -> (a `m` f b) -> f b
    -- (<=<) :: (Morphism m, MorCat m ~ Dom f)
    --          => b `m` f c -> a `m` f b -> a `m` f c

-- MonadZero, MonadPlus
