{-# LANGUAGE UndecidableInstances #-}

module NVector ( NVector(..)
               , NUVector(..)
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
import Comonoid
import Functor
import Hask
import Sized
import Vector
import Unboxed



newtype NList (n :: Nat) a = NList [a]
    deriving (Eq, Ord, Read, Show)

newtype NVector (n :: Nat) a = NVector (Vector a)
    deriving (Eq, Ord, Read, Show)

newtype NUVector (n :: Nat) a = NUVector (UVector a)
    deriving (Eq, Ord, Read, Show)



instance (KnownNat n, Default a) => Default (NList n a) where
    def = pure def

instance (KnownNat n, Default a) => Default (NVector n a) where
    def = pure def

instance (KnownNat n, Unboxed a, Default a) => Default (NUVector n a) where
    def = pure def



instance (KnownNat n, QC.Arbitrary a) => QC.Arbitrary (NList n a) where
    arbitrary = do xs <- QC.vector (intVal @n)
                   P.return (NList xs)
    shrink (NList xs) = [ NList xs'
                        | xs' <- QC.shrink xs
                        , length xs' == (intVal @n)]

instance (KnownNat n, QC.Arbitrary a) => QC.Arbitrary (NVector n a) where
    arbitrary = fromList . toList <$> QC.arbitrary @(NList n a)
    shrink =
        P.fmap (fromList . toList) . QC.shrink @(NList n a) . fromList . toList

instance (KnownNat n, Unboxed a, QC.Arbitrary a)
        => QC.Arbitrary (NUVector n a) where
    arbitrary = fromList . toList <$> QC.arbitrary @(NList n a)
    shrink =
        P.fmap (fromList . toList) . QC.shrink @(NList n a) . fromList . toList



instance QC.CoArbitrary a => QC.CoArbitrary (NList n a) where
    coarbitrary (NList xs) = QC.coarbitrary xs

instance QC.CoArbitrary a => QC.CoArbitrary (NVector n a) where
    coarbitrary (NVector xs) = QC.coarbitrary xs

instance (Unboxed a, QC.CoArbitrary a) => QC.CoArbitrary (NUVector n a) where
    coarbitrary (NUVector xs) = QC.coarbitrary xs



instance {-# OVERLAPPING #-} QC.Function (NList 0 a) where
    function = QC.functionMap (const ()) (const (NList []))

instance {-# OVERLAPPING #-}
        (1 <= n, QC.Function a, QC.Function (NList (n - 1) a))
        => QC.Function (NList n a) where
    function = QC.functionMap f g
        where f :: NList n a -> (a, NList (n-1) a)
              f (NList (x:xs)) = (x, NList xs)
              f (NList []) = undefined
              g (x, NList xs) = NList (x:xs)

instance (KnownNat n, QC.Function (NList n a))
        => QC.Function (NVector n a) where
    function =
        QC.functionMap @(NList n a) (fromList . toList) (fromList . toList)

instance (KnownNat n, Unboxed a, QC.Function (NList n a))
        => QC.Function (NUVector n a) where
    function =
        QC.functionMap @(NList n a) (fromList . toList) (fromList . toList)



instance (KnownNat n, Validity [a]) => Validity (NList n a) where
    validate (NList xs) =
        mconcat
        [ length xs == (intVal @n) <?@> "List has correct length"
        , xs <?!> "List"
        ]

instance (KnownNat n, Validity (Vector a))
        => Validity (NVector n a) where
    validate (NVector xs) =
        mconcat
        [ length xs == (intVal @n) <?@> "Vector has correct length"
        , xs <?!> "Vector"
        ]

instance (KnownNat n, Unboxed a, Validity (UVector a))
        => Validity (NUVector n a) where
    validate (NUVector xs) =
        mconcat
        [ length xs == (intVal @n) <?@> "Vector has correct length"
        , xs <?!> "Vector"
        ]



instance Functor (NList n) where
    type Dom (NList n) = Hask
    type Cod (NList n) = Hask
    type FunMor (NList n) m = (->)
    proveFunCod _ = Sub Dict
    proveFunMor _ = Sub Dict
    fmap f (NList xs) = NList (P.map (chase f) xs)

instance Functor (NVector n) where
    type Dom (NVector n) = Hask
    type Cod (NVector n) = Hask
    type FunMor (NVector n) m = (->)
    proveFunCod _ = Sub Dict
    proveFunMor _ = Sub Dict
    fmap f (NVector xs) = NVector (fmap f xs)

instance Functor (NUVector n) where
    type Dom (NUVector n) = Unboxed
    type Cod (NUVector n) = Hask
    type FunMor (NUVector n) m = (->)
    proveFunCod _ = Sub Dict
    proveFunMor _ = Sub Dict
    fmap f (NUVector xs) = NUVector (fmap f xs)



instance KnownNat n => Unfoldable (NList n) where
    mapUnfold f x = NList (go (intVal @n) x)
        where go i y = if i == 0
                       then []
                       else let (y1, y2) = split y
                            in f y1 : go (i - 1) y2
    fromList = NList . take (intVal @n)

instance KnownNat n => Unfoldable (NVector n) where
    mapUnfold f = fromList . toList . mapUnfold @(NList n) f
    fromList = NVector . fromList . toList . fromList @(NList n)

instance KnownNat n => Unfoldable (NUVector n) where
    mapUnfold f = fromList . toList . mapUnfold @(NList n) f
    fromList = NUVector . fromList . toList . fromList @(NList n)



instance Foldable (NList n) where
    foldMap f (NList xs) = foldMap f xs
    toList (NList xs) = xs

instance Foldable (NVector n) where
    foldMap f (NVector xs) = foldMap f xs
    toList (NVector xs) = toList xs

instance Foldable (NUVector n) where
    foldMap f (NUVector xs) = foldMap f xs
    toList (NUVector xs) = toList xs



instance Apply (NList n) where
    liftA2' f = uncurry (liftA2 (curry (chase f . CProduct))) . getCProduct
    liftA2 f (NList xs) (NList ys) = NList (P.zipWith (chase2 f) xs ys)

instance Apply (NVector n) where
    liftA2' f = uncurry (liftA2 (curry (chase f . CProduct))) . getCProduct
    liftA2 f (NVector xs) (NVector ys) = NVector (liftA2 f xs ys)

instance Apply (NUVector n) where
    liftA2' f (CProduct (NUVector xs, NUVector ys)) =
        NUVector (liftA2' f (CProduct (xs, ys)))
    liftA2 f (NUVector xs) (NUVector ys) = NUVector (liftA2 f xs ys)



instance KnownNat n => Applicative (NList n) where
    pure' _ = pure
    pure x = NList (replicate (intVal @n) x)

instance KnownNat n => Applicative (NVector n) where
    pure' _ = pure
    pure x = NVector (Vector (V.replicate (intVal @n) x))

instance KnownNat n => Applicative (NUVector n) where
    pure' _ = pure
    pure x = NUVector (UVector (U.replicate (intVal @n) x))



-- TODO: rotate?
instance KnownNat n => Semicomonad (NList n) where
    extend f xs = pure (f `chase` xs)

instance KnownNat n => Semicomonad (NVector n) where
    extend f xs = pure (f `chase` xs)



instance KnownNat n => SemicomonadStore Int (NList n) where
    peek i (NList xs) = xs !! i

instance KnownNat n => SemicomonadStore Int (NVector n) where
    peek i (NVector xs) = peek i xs
