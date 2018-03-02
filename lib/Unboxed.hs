{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -funbox-strict-fields #-}

module Unboxed ( Unboxed
               , Vector(..)
               , UVector(..)
               ) where

import Prelude hiding ( Foldable(..)
                      , Functor(..)
                      , Applicative(..)
                      , Monad(..)
                      )

import Control.Exception (assert)
import Data.Constraint
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as U

import GHC.TypeLits

import Category
import Comonoid
import Hask
import Sized



-- | The category of numeric types
class U.Unbox a => Unboxed a
instance U.Unbox a => Unboxed a
instance Category Unboxed



-- | A mock function type
data (-#>) a b where
    UFun :: (Unboxed a, Unboxed b) => (a -> b) -> (a -#> b)
instance Morphism (-#>) where
    type MorCat (-#>) = Unboxed
    proveChase (UFun f) = Sub Dict
    chase (UFun f) = f
instance Discretization (-#>) where
    discretize = UFun






newtype Vector a = Vector (V.Vector a)
    deriving (Eq, Ord, Read, Show)

newtype UVector a = UVector (U.Vector a)
    deriving (Eq, Ord, Read, Show)

newtype NList (n :: Nat) a = NList { getNList :: [a] }
    deriving (Eq, Ord, Read, Show)

newtype NVector (n :: Nat) a = NVector (Vector a)
    deriving (Eq, Ord, Read, Show)

newtype NUVector (n :: Nat) a = NUVector (UVector a)
    deriving (Eq, Ord, Read, Show)

data CNVector (n :: Nat) a = CNVector !Int (NVector n a)
    deriving (Eq, Ord, Read, Show)

data CNUVector (n :: Nat) a = CNUVector !Int (NUVector n a)
    deriving (Eq, Ord, Read, Show)



instance Functor Vector where
    type Dom Vector = Hask
    type Cod Vector = Hask
    type FunMor Vector m = (->)
    proveFunctor _ = Sub Dict
    proveFunMor _ = Sub Dict
    fmap f (Vector xs) = Vector (V.map (chase f) xs)

instance Functor UVector where
    type Dom UVector = Unboxed
    type Cod UVector = Hask
    type FunMor UVector m = (->)
    proveFunctor _ = Sub Dict
    proveFunMor _ = Sub Dict
    fmap f (UVector xs) = UVector (U.map (chase f) xs)

instance Functor (NList n) where
    type Dom (NList n) = Hask
    type Cod (NList n) = Hask
    type FunMor (NList n) m = (->)
    proveFunctor _ = Sub Dict
    proveFunMor _ = Sub Dict
    fmap f (NList xs) = NList (fmap f xs)

instance Functor (NVector n) where
    type Dom (NVector n) = Hask
    type Cod (NVector n) = Hask
    type FunMor (NVector n) m = (->)
    proveFunctor _ = Sub Dict
    proveFunMor _ = Sub Dict
    fmap f (NVector xs) = NVector (fmap f xs)

instance Functor (NUVector n) where
    type Dom (NUVector n) = Unboxed
    type Cod (NUVector n) = Hask
    type FunMor (NUVector n) m = (->)
    proveFunctor _ = Sub Dict
    proveFunMor _ = Sub Dict
    fmap f (NUVector xs) = NUVector (fmap f xs)

instance Functor (CNVector n) where
    type Dom (CNVector n) = Hask
    type Cod (CNVector n) = Hask
    type FunMor (CNVector n) m = (->)
    proveFunctor _ = Sub Dict
    proveFunMor _ = Sub Dict
    fmap f (CNVector i xs) = CNVector i (fmap f xs)

instance Functor (CNUVector n) where
    type Dom (CNUVector n) = Unboxed
    type Cod (CNUVector n) = Hask
    type FunMor (CNUVector n) m = (->)
    proveFunctor _ = Sub Dict
    proveFunMor _ = Sub Dict
    fmap f (CNUVector i xs) = CNUVector i (fmap f xs)



instance Unfoldable Vector where
    mapUnfold f x = Vector (V.fromList (mapUnfold f x))

instance Unfoldable UVector where
    mapUnfold f x = UVector (U.fromList (mapUnfold f x))

instance KnownNat n => Unfoldable (NList n) where
    mapUnfold f x = NList (go (intVal @n) x)
        where go i y = if i == 0
                       then []
                       else let (y1, y2) = split y
                            in f y1 : go (i - 1) y2

instance KnownNat n => Unfoldable (NVector n) where
    mapUnfold :: forall a b. (Comonoid a, Dom (NVector n) b)
                 => (a -> b) -> a -> NVector n b
    mapUnfold f x = NVector (Vector (V.fromListN (intVal @n) ys))
        where ys = getNList (mapUnfold f x :: NList n b)

instance KnownNat n => Unfoldable (NUVector n) where
    mapUnfold :: forall a b. (Comonoid a, Dom (NUVector n) b)
                 => (a -> b) -> a -> NUVector n b
    mapUnfold f x = NUVector (UVector (U.fromListN (intVal @n) ys))
        where ys = getNList (mapUnfold f x :: NList n b)

instance (KnownNat n, 1 <= n) => Unfoldable (CNVector n) where
    mapUnfold f x = CNVector 0 (mapUnfold f x)

instance (KnownNat n, 1 <= n) => Unfoldable (CNUVector n) where
    mapUnfold f x = CNUVector 0 (mapUnfold f x)



instance Foldable Vector where
    foldMap f (Vector xs) =
        V.foldl' (\r x -> r `mappend` (f `chase` x)) mempty xs

instance Foldable UVector where
    foldMap f (UVector xs) =
        U.foldl' (\r x -> r `mappend` (f `chase` x)) mempty xs

instance Foldable (NList n) where
    foldMap f (NList xs) = foldMap f xs

instance Foldable (NVector n) where
    foldMap f (NVector xs) = foldMap f xs

instance Foldable (NUVector n) where
    foldMap f (NUVector xs) = foldMap f xs

instance Foldable (CNVector n) where
    foldMap f (CNVector i xs) = foldMap f xs

instance Foldable (CNUVector n) where
    foldMap f (CNUVector i xs) = foldMap f xs



instance Apply Vector where
    liftA2 f (Vector xs) (Vector ys) = Vector (V.zipWith (chase2 f) xs ys)

instance Apply UVector where
    liftA2 f (UVector xs) (UVector ys) = UVector (U.zipWith (chase2 f) xs ys)

instance Apply (NList n) where
    liftA2 f (NList xs) (NList ys) = NList (liftA2 f xs ys)

instance Apply (NVector n) where
    liftA2 f (NVector xs) (NVector ys) = NVector (liftA2 f xs ys)

instance Apply (NUVector n) where
    liftA2 f (NUVector xs) (NUVector ys) = NUVector (liftA2 f xs ys)

instance Apply (CNVector n) where
    liftA2 f (CNVector i xs) (CNVector j ys) =
        CNVector (min i j) (liftA2 f xs ys)

instance Apply (CNUVector n) where
    liftA2 f (CNUVector i xs) (CNUVector j ys) =
        CNUVector (min i j) (liftA2 f xs ys)



instance KnownNat n => Applicative (NList n) where
    pure x = NList (replicate (intVal @n) x)

instance KnownNat n => Applicative (NVector n) where
    pure x = NVector (Vector (V.replicate (intVal @n) x))

instance KnownNat n => Applicative (NUVector n) where
    pure x = NUVector (UVector (U.replicate (intVal @n) x))

instance (KnownNat n, 1 <= n) => Applicative (CNVector n) where
    pure x = CNVector 0 (pure x)

instance (KnownNat n, 1 <= n) => Applicative (CNUVector n) where
    pure x = CNUVector 0 (pure x)



instance (KnownNat n, 1 <= n) => Comonad (CNVector n) where
    extract (CNVector i (NVector (Vector xs))) = xs V.! i
    extend f (CNVector i (NVector (Vector xs))) =
        CNVector i (NVector (Vector (V.imap go xs)))
                 where go j y = f `chase` CNVector j (NVector (Vector xs))

-- | Unboxed arrays are not comonadic! They are not endofunctors,
-- since they cannot contain other unboxed arrays, and hence are
-- neither monadic nor comonadic. Since we still want to use unboxed
-- arrays for stencil operations, we need another abstraction. Maybe
-- distributive or traversable functors are the way to go?

-- instance (KnownNat n, 1 <= n) => Comonad (CNUVector n) where
--     extract (CNUVector i (NUVector (UVector xs))) = xs U.! i
--     extend f (CNUVector i (NUVector (UVector xs))) =
--         CNUVector i (NUVector (UVector (U.imap go xs)))
--                  where go j y = f `chase` CNUVector j (NUVector (UVector xs))



instance (KnownNat n, 1 <= n) => ComonadStore Int (CNVector n) where
    pos (CNVector i (NVector (Vector xs))) = i
    peek j (CNVector i (NVector (Vector xs))) =
        assert (j >= 0 && j < intVal @n) $ xs V.! j

-- instance (KnownNat n, 1 <= n) => ComonadStore Int (CNUVector n) where
--     pos (CNUVector i (NUVector (UVector xs))) = i
--     peek j (CNUVector i (NUVector (UVector xs))) =
--         assert (j >= 0 && j < intVal @n) $ xs U.! j
