{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -funbox-strict-fields #-}

module Unboxed ( Unboxed
               , type (-#>)
               , Vector(..)
               , UVector(..)
               , NVector(..)
               , NUVector(..)
               , CNVector(..)
               , CNUVector(..)
               ) where

import Prelude hiding ( Foldable(..)
                      , Functor(..)
                      , Applicative(..)
                      , Monad(..)
                      )
import qualified Prelude as P

import Data.Constraint
import Data.Validity
import Data.Validity.Vector ()
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as U
import Data.Vector.Unboxed.Deriving

import GHC.TypeLits

import qualified Test.QuickCheck as QC
import qualified Test.QuickCheck.Instances ()

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
    UQCFun :: (Unboxed a, Unboxed b) => QC.Fun a b -> (a -#> b)
instance Show (QC.Fun a b) => Show ((-#>) a b) where
    show (UFun f) = show ("UFun" :: String)
    show (UQCFun f) = show f

instance Morphism (-#>) where
    type MorCat (-#>) = Unboxed
    proveChase (UFun f) = Sub Dict
    proveChase (UQCFun f) = Sub Dict
    chase (UFun f) = f
    chase (UQCFun f) = QC.applyFun f
instance Discretization (-#>) where
    discretize = UFun

instance (Unboxed a, Unboxed b, QC.Arbitrary (QC.Fun a b))
        => QC.Arbitrary ((-#>) a b) where
    arbitrary = UQCFun <$> QC.arbitrary
    shrink (UQCFun f) = UQCFun <$> QC.shrink f
    shrink f = undefined



newtype Vector a = Vector (V.Vector a)
    deriving (Eq, Ord, Read, Show, QC.Arbitrary, Validity)

newtype UVector a = UVector (U.Vector a)
    deriving (Eq, Ord, Read, Show, QC.Arbitrary)
deriving instance Validity (U.Vector a) => Validity (UVector a)

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



instance (KnownNat n, Validity [a]) => Validity (NList n a) where
    validate (NList xs) =
        mconcat
        [ length xs == (intVal @n) <?@> "List has correct length"
        , xs <?!> "List"
        ]

instance (KnownNat n, Validity (Vector a)) => Validity (NVector n a) where
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



instance (KnownNat n, QC.Arbitrary a) => QC.Arbitrary (NList n a) where
    arbitrary = do xs <- QC.vector (intVal @n)
                   P.return (NList xs)
    shrink (NList xs) = [ NList xs'
                        | xs' <- QC.shrink xs
                        , length xs' == (intVal @n)]

instance (KnownNat n, QC.Arbitrary a) => QC.Arbitrary (NVector n a) where
    arbitrary = f <$> QC.arbitrary
        where f :: NList n a -> NVector n a
              f (NList xs) = NVector (Vector (V.fromList xs))
    shrink = P.fmap f . QC.shrink . g
        where f :: NList n a -> NVector n a
              f (NList xs) = NVector (Vector (V.fromList xs))
              g (NVector (Vector xs)) = NList (V.toList xs)

instance (KnownNat n, Unboxed a, QC.Arbitrary a)
        => QC.Arbitrary (NUVector n a) where
    arbitrary = f <$> QC.arbitrary
        where f :: NList n a -> NUVector n a
              f (NList xs) = NUVector (UVector (U.fromList xs))
    shrink = P.fmap f . QC.shrink . g
        where f :: NList n a -> NUVector n a
              f (NList xs) = NUVector (UVector (U.fromList xs))
              g (NUVector (UVector xs)) = NList (U.toList xs)

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



instance QC.CoArbitrary a => QC.CoArbitrary (Vector a) where
    coarbitrary (Vector xs) = QC.coarbitrary (V.toList xs)

instance (U.Unbox a, QC.CoArbitrary a) => QC.CoArbitrary (UVector a) where
    coarbitrary (UVector xs) = QC.coarbitrary (U.toList xs)

instance QC.CoArbitrary a => QC.CoArbitrary (NList n a) where
    coarbitrary (NList xs) = QC.coarbitrary xs

instance QC.CoArbitrary a => QC.CoArbitrary (NVector n a) where
    coarbitrary (NVector xs) = QC.coarbitrary xs

instance (U.Unbox a, QC.CoArbitrary a) => QC.CoArbitrary (NUVector n a) where
    coarbitrary (NUVector xs) = QC.coarbitrary xs

instance QC.CoArbitrary a => QC.CoArbitrary (CNVector n a) where
    coarbitrary (CNVector i xs) = QC.coarbitrary (i, xs)

instance (U.Unbox a, QC.CoArbitrary a) => QC.CoArbitrary (CNUVector n a) where
    coarbitrary (CNUVector i xs) = QC.coarbitrary (i, xs)



instance QC.Function [a] => QC.Function (Vector a) where
    function = QC.functionMap f g
        where f (Vector xs) = V.toList xs
              g xs = Vector (V.fromList xs)

instance (U.Unbox a, QC.Function [a]) => QC.Function (UVector a) where
    function = QC.functionMap f g
        where f (UVector xs) = U.toList xs
              g xs = UVector (U.fromList xs)

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

instance QC.Function (NList n a) => QC.Function (NVector n a) where
    function = QC.functionMap f g
        where f :: NVector n a -> NList n a
              f (NVector (Vector xs)) = NList (V.toList xs)
              g (NList xs) = NVector (Vector (V.fromList xs))

instance (U.Unbox a, QC.Function (NList n a))
        => QC.Function (NUVector n a) where
    function = QC.functionMap f g
        where f :: NUVector n a -> NList n a
              f (NUVector (UVector xs)) = NList (U.toList xs)
              g (NList xs) = NUVector (UVector (U.fromList xs))

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



instance Functor Vector where
    type Dom Vector = Hask
    type Cod Vector = Hask
    type FunMor Vector m = (->)
    proveFunCod _ = Sub Dict
    proveFunMor _ = Sub Dict
    fmap f (Vector xs) = Vector (V.map (chase f) xs)

instance Functor UVector where
    type Dom UVector = Unboxed
    type Cod UVector = Hask
    type FunMor UVector m = (->)
    proveFunCod _ = Sub Dict
    proveFunMor _ = Sub Dict
    fmap f (UVector xs) = UVector (U.map (chase f) xs)

instance Functor (NList n) where
    type Dom (NList n) = Hask
    type Cod (NList n) = Hask
    type FunMor (NList n) m = (->)
    proveFunCod _ = Sub Dict
    proveFunMor _ = Sub Dict
    fmap f (NList xs) = NList (fmap f xs)

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



-- TODO: rotate?
instance Semicomonad Vector where
    extend f xs = Vector (V.singleton (f `chase` xs))

instance KnownNat n => Semicomonad (NList n) where
    extend f xs = pure (f `chase` xs)

instance KnownNat n => Semicomonad (NVector n) where
    extend f xs = pure (f `chase` xs)

instance (KnownNat n, 1 <= n) => Semicomonad (CNVector n) where
    extend f (CNVector i (NVector (Vector xs))) =
        CNVector i (NVector (Vector (V.imap go xs)))
                 where go j y = f `chase` CNVector j (NVector (Vector xs))



instance (KnownNat n, 1 <= n) => Comonad (CNVector n) where
    extract (CNVector i (NVector (Vector xs))) = xs V.! i
    extract' _ = extract

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



instance SemicomonadStore Int Vector where
    peek i (Vector xs) = xs V.! i

-- instance SemicomonadStore Int UVector where
--     peek i (UVector xs) = xs U.! i

instance KnownNat n => SemicomonadStore Int (NList n) where
    peek i (NList xs) = xs !! i

instance KnownNat n => SemicomonadStore Int (NVector n) where
    peek i (NVector xs) = peek i xs

instance (KnownNat n, 1 <= n) => SemicomonadStore Int (CNVector n) where
    peek i (CNVector j xs) = peek i xs

-- instance SemicomonadStore Int (CNUVector n) where
--     peek i (CNUVector j xs) = peek i xs



instance (KnownNat n, 1 <= n) => ComonadStore Int (CNVector n) where
    pos (CNVector i xs) = i

-- instance (KnownNat n, 1 <= n) => ComonadStore Int (CNUVector n) where
--     pos (CNUVector i (NUVector (UVector xs))) = i



data Stencil a = Stencil Int !a !a !a
                 deriving (Eq, Ord, Read, Show)

instance Functor Stencil where
    type Dom Stencil = Hask
    type Cod Stencil = Hask
    type FunMor Stencil m = (->)
    proveFunCod _ = Sub Dict
    proveFunMor _ = Sub Dict
    fmap f (Stencil i xm x xp) =
        Stencil i (f `chase` xm) (f `chase` x) (f `chase` xp)

instance KnownNat n => LocalSemicomonad (CNVector n) where
    type Local (CNVector n) = Stencil
    global x0 (Stencil i xm x xp) = undefined
    local x0 (CNVector i xs) =
        Stencil i (if i - 1 >= 0 then peek (i - 1) xs else x0)
                  (peek i xs)
                  (if i + 1 < intVal @n then peek (i + 1) xs else x0)
    extendL f (CNVector i xs) = CNVector i (imap go xs)
        where imap f (NVector (Vector xs)) = NVector (Vector (V.imap f xs))
              go j y = f `chase` local y (CNVector @n j xs)

instance (KnownNat n, 1 <= n) => LocalComonad (CNVector n) where
    extractL (CNVector i xs) = peek i xs



data UStencil a = UStencil Int !a !a !a
                  deriving (Eq, Ord, Read, Show)

derivingUnbox "UStencil"
    [t| forall a. U.Unbox a => UStencil a -> (Int, a, a, a) |]
    [| \ (UStencil i xm x xp) -> (i, xm, x, xp) |]
    [| \ (i, xm, x, xp) -> (UStencil i xm x xp) |]

instance Functor UStencil where
    type Dom UStencil = Unboxed
    type Cod UStencil = Hask
    type FunMor UStencil m = (->)
    proveFunCod _ = Sub Dict
    proveFunMor _ = Sub Dict
    fmap f (UStencil i xm x xp) =
        UStencil i (f `chase` xm) (f `chase` x) (f `chase` xp)

instance KnownNat n => LocalSemicomonad (CNUVector n) where
    type Local (CNUVector n) = UStencil
    global x0 (UStencil i xm x xp) = undefined
    local x0 (CNUVector i xs) =
        UStencil i (if i - 1 >= 0 then xs ! (i - 1) else x0)
                   (xs ! i)
                   (if i + 1 < intVal @n then xs ! (i + 1) else x0)
        where (!) (NUVector (UVector xs)) i = xs U.! i
    extendL f (CNUVector i xs) = CNUVector i (imap go xs)
        where imap f (NUVector (UVector xs)) = NUVector (UVector (U.imap f xs))
              go j y = f `chase` local y (CNUVector @n j xs)

instance (KnownNat n, 1 <= n) => LocalComonad (CNUVector n) where
    extractL (CNUVector i xs) = xs ! i
        where (!) (NUVector (UVector xs)) i = xs U.! i
