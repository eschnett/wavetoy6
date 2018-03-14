{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -funbox-strict-fields #-}

module CNVector ( CNVector(..)
                , CNUVector(..)
                ) where

import Prelude hiding ( Foldable(..)
                      , Functor(..)
                      , Applicative(..)
                      , Traversable(..)
                      , Monad(..)
                      )
import qualified Prelude as P

import Data.Constraint
import Data.Default
import Data.Validity
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as U

import GHC.TypeLits

import qualified Test.QuickCheck as QC

import Category
import Comonad
import Functor
import Hask
import NVector
import Sized
import Unboxed
import Vec
import Vector



data CNVector (n :: Nat) a = CNVector !Int (NVector n a)
    deriving (Eq, Ord, Read, Show)

data CNUVector (n :: Nat) a = CNUVector !Int (NUVector n a)
    deriving (Eq, Ord, Read, Show)



instance (KnownNat n, 1 <= n, Default a) => Default (CNVector n a) where
    def = CNVector def def

instance (KnownNat n, 1 <= n, Unboxed a, Default a)
        => Default (CNUVector n a) where
    def = CNUVector def def



instance (KnownNat n, 1 <= n, QC.Arbitrary a)
        => QC.Arbitrary (CNVector n a) where
    arbitrary = do i <- QC.choose (0, intVal @n - 1)
                   xs <- QC.arbitrary
                   P.return (CNVector i xs)
    shrink (CNVector i xs) = [CNVector i' xs' | (i', xs') <- QC.shrink (i, xs)]

instance (KnownNat n, 1 <= n, Unboxed a, QC.Arbitrary a)
        => QC.Arbitrary (CNUVector n a) where
    arbitrary = do i <- QC.choose (0, intVal @n - 1)
                   xs <- QC.arbitrary
                   P.return (CNUVector i xs)
    shrink (CNUVector i xs) =
        [CNUVector i' xs' | (i', xs') <- QC.shrink (i, xs)]



instance QC.CoArbitrary a => QC.CoArbitrary (CNVector n a) where
    coarbitrary (CNVector i xs) = QC.coarbitrary (i, xs)

instance (Unboxed a, QC.CoArbitrary a) => QC.CoArbitrary (CNUVector n a) where
    coarbitrary (CNUVector i xs) = QC.coarbitrary (i, xs)



instance (KnownNat n, QC.Function (NVector n a))
        => QC.Function (CNVector n a) where
    function = QC.functionMap f g
        where f :: CNVector n a -> (Int, NVector n a)
              f (CNVector i xs) = (i, xs)
              g (i, xs) = CNVector (i `mod` (intVal @n)) xs

instance (KnownNat n, QC.Function (NUVector n a))
        => QC.Function (CNUVector n a) where
    function = QC.functionMap f g
        where f :: CNUVector n a -> (Int, NUVector n a)
              f (CNUVector i xs) = (i, xs)
              g (i, xs) = CNUVector (i `mod` (intVal @n)) xs



instance (KnownNat n, Validity (NVector n a)) => Validity (CNVector n a) where
    validate (CNVector i xs) =
        mconcat
        [ 0 <= i && i < (intVal @n) <?@> "Position is legal"
        , xs <?!> "Vector"
        ]

instance (KnownNat n, Validity (NUVector n a)) => Validity (CNUVector n a) where
    validate (CNUVector i xs) =
        mconcat
        [ 0 <= i && i < (intVal @n) <?@> "Position is legal"
        , xs <?!> "Vector"
        ]



instance Functor (CNVector n) where
    type Dom (CNVector n) = Hask
    type Cod (CNVector n) = Hask
    type FunMor (CNVector n) m = (->)
    proveFunCod _ = Sub Dict
    proveFunMor _ = Sub Dict
    fmap f (CNVector i xs) = CNVector i (fmap f xs)

instance Functor (CNUVector n) where
    type Dom (CNUVector n) = Unboxed
    type Cod (CNUVector n) = Hask
    type FunMor (CNUVector n) m = (->)
    proveFunCod _ = Sub Dict
    proveFunMor _ = Sub Dict
    fmap f (CNUVector i xs) = CNUVector i (fmap f xs)



instance (KnownNat n, 1 <= n) => Unfoldable (CNVector n) where
    mapUnfold f x = CNVector 0 (mapUnfold f x)
    fromList = CNVector 0 . fromList

instance (KnownNat n, 1 <= n) => Unfoldable (CNUVector n) where
    mapUnfold f x = CNUVector 0 (mapUnfold f x)
    fromList = CNUVector 0 . fromList



instance Foldable (CNVector n) where
    foldMap f (CNVector i xs) = foldMap f xs
    toList (CNVector i xs) = toList xs

instance Foldable (CNUVector n) where
    foldMap f (CNUVector i xs) = foldMap f xs
    toList (CNUVector i xs) = toList xs



instance (KnownNat n, 1 <= n) => Apply (CNVector n) where
    liftA2' f = uncurry (liftA2 (curry (chase f . CProduct))) . getCProduct
    liftA2 f (CNVector i xs) (CNVector j ys) =
        CNVector (i + j `mod` intVal @n) (liftA2 f xs ys)

instance (KnownNat n, 1 <= n) => Apply (CNUVector n) where
    liftA2' f (CProduct (CNUVector i xs, CNUVector j ys)) =
        CNUVector (i + j `mod` intVal @n) (liftA2' f (CProduct (xs, ys)))
    liftA2 f (CNUVector i xs) (CNUVector j ys) =
        CNUVector (i + j `mod` intVal @n) (liftA2 f xs ys)



instance (KnownNat n, 1 <= n) => Applicative (CNVector n) where
    pure' _ = pure
    pure x = CNVector 0 (pure x)

instance (KnownNat n, 1 <= n) => Applicative (CNUVector n) where
    pure' _ = pure
    pure x = CNUVector 0 (pure x)



instance (KnownNat n, 1 <= n) => Semicomonad (CNVector n) where
    extend f (CNVector i xs) =
        CNVector i (NVector (Vector (V.generate (intVal @n) go)))
        where go j = f `chase` CNVector j xs



instance (KnownNat n, 1 <= n) => Comonad (CNVector n) where
    extract (CNVector i (NVector (Vector xs))) = xs V.! i
    extract' _ = extract



instance (KnownNat n, 1 <= n) => SemicomonadStore Int (CNVector n) where
    peek i (CNVector j xs) = peek i xs



instance (KnownNat n, 1 <= n) => ComonadStore Int (CNVector n) where
    pos (CNVector i xs) = i



instance (KnownNat n, 1 <= n)
        => CompactSemicomonad (UVec3 n) (CNUVector n) where
    restrict (CNUVector i xs) =
        CVec3 i (if i - 1 >= 0 then xs ! (i - 1) else def)
                (xs ! i)
                (if i + 1 < intVal @n then xs ! (i + 1) else def)
        where (!) (NUVector (UVector ys)) j = ys U.! j
    -- 'expand' forgets the stencil's boundary values
    -- maybe the stencil should have 'def' outside the domain?
    expand (CVec3 i xm x xp) =
        CNUVector i (NUVector (UVector (U.generate (intVal @n) go)))
        where go j = if | j == i - 1 -> xm
                        | j == i -> x
                        | j == i + 1 -> xp
                        | otherwise -> def
    extendC f (CNUVector i xs) =
        CNUVector i (NUVector (UVector (U.generate (intVal @n) go)))
        where go j = f `chase` restrict (CNUVector @n j xs)



instance (KnownNat n, 1 <= n) => CompactComonad (UVec3 n) (CNUVector n) where
    extractC (CNUVector i (NUVector (UVector xs))) = xs U.! i
    extractC' (CVec3 i xm x xp) = x
