{-# LANGUAGE UndecidableInstances #-}

module Vector ( Vector(..)
              , UVector(..)
              ) where

import Prelude hiding ( Foldable(..)
                      , Functor(..)
                      , Applicative(..)
                      , Traversable(..)
                      , Monad(..)
                      )

import Data.Constraint
import Data.Validity
import Data.Validity.Vector ()
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as U

import qualified Test.QuickCheck as QC
import qualified Test.QuickCheck.Instances ()

import Category
import Comonad
import Functor
import Hask
import Unboxed



newtype Vector a = Vector (V.Vector a)
    deriving (Eq, Ord, Read, Show, QC.Arbitrary, Validity)

newtype UVector a = UVector (U.Vector a)
    deriving (Eq, Ord, Read, Show, QC.Arbitrary)
deriving instance Validity (U.Vector a) => Validity (UVector a)



instance QC.CoArbitrary a => QC.CoArbitrary (Vector a) where
    coarbitrary (Vector xs) = QC.coarbitrary (V.toList xs)

instance (U.Unbox a, QC.CoArbitrary a) => QC.CoArbitrary (UVector a) where
    coarbitrary (UVector xs) = QC.coarbitrary (U.toList xs)



instance QC.Function [a] => QC.Function (Vector a) where
    function = QC.functionMap f g
        where f (Vector xs) = V.toList xs
              g xs = Vector (V.fromList xs)

instance (U.Unbox a, QC.Function [a]) => QC.Function (UVector a) where
    function = QC.functionMap f g
        where f (UVector xs) = U.toList xs
              g xs = UVector (U.fromList xs)



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



instance Unfoldable Vector where
    mapUnfold f x = Vector (V.fromList (mapUnfold f x))
    fromList = Vector . V.fromList

instance Unfoldable UVector where
    mapUnfold f x = UVector (U.fromList (mapUnfold f x))
    fromList = UVector . U.fromList



instance Foldable Vector where
    foldMap f (Vector xs) =
        V.foldl' (\r x -> r `mappend` (f `chase` x)) mempty xs
    toList (Vector xs) = V.toList xs

instance Foldable UVector where
    foldMap f (UVector xs) =
        U.foldl' (\r x -> r `mappend` (f `chase` x)) mempty xs
    toList (UVector xs) = U.toList xs



instance Apply Vector where
    liftA2' f = uncurry (liftA2 (curry (chase f . CProduct))) . getCProduct
    liftA2 f (Vector xs) (Vector ys) = Vector (V.zipWith (chase2 f) xs ys)

instance Apply UVector where
    liftA2' f (CProduct (UVector xs, UVector ys)) = go
        where go = UVector (U.zipWith g xs ys)
              g x y = f `chase` CProduct (x, y)
    liftA2 f (UVector xs) (UVector ys) = UVector (U.zipWith (chase2 f) xs ys)
    -- liftA2 f = curry (liftA2' g . CProduct)
    --     where g = UFun (uncurry (chase2 f) . getCProduct)



-- TODO: rotate?
instance Semicomonad Vector where
    extend f xs = Vector (V.singleton (f `chase` xs))



instance SemicomonadStore Int Vector where
    peek i (Vector xs) = xs V.! i
