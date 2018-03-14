{-# LANGUAGE UndecidableInstances #-}
-- {-# LANGUAGE UndecidableSuperClasses #-}

module VectorSpace ( Additive1(..)
                   , Additive(..)
                   , VectorSpace(..)
                   , (^*)
                   , (^/)
                   , InnerSpace(..)
                   , SumV(..)
                   , VectorSpaceOver()
                   , type (*^*)
                   , type (-^>)
                   ) where

import Data.Biapplicative
import Data.Constraint
import Data.Kind
import Data.Semigroup

import qualified Test.QuickCheck as QC

import Category
-- import Functor



-- class Apply f => Additive1 f where
--     negateV :: Dom f a => f a -> f a
--     default negateV :: (Dom f a, Additive1 a) => f a -> f a
--     negateV = fmap negateV
--     (^+^) :: Dom f a => f a -> f a -> f a
--     default (^+^) :: (Dom f a, Additive1 a) => f a -> f a -> f a
--     (^+^) = liftA2 (^+^)
-- 
-- class (Applicative f, Additive1 f) => Additive f where
--     zeroV :: Dom f a => f a
--     default zeroV :: (Dom f a, Additive a) => f a
--     zeroV = pure zeroV
-- 
-- newtype SumV a = SumV { getSumV :: a }
--     deriving (Eq, Ord, Read, Show)
-- instance Additive1 a => Semigroup (SumV a) where
--     (<>) = (^+^)
-- instance Additive a => Monoid (SumV a) where
--     mempty = zeroV
-- 
-- class Additive f => VectorSpace f where
--     -- type Scalar f = Num
--     (*^) :: Dom f a => a -> f a -> f a
--     default (*^) :: (Dom f a, VectorSpace f a) => a -> f a -> f a
--     (*^) a = fmap (a *^)
--     (^*) :: Dom f a => f a -> a -> f a
--     (^*) = flip (*^)
--     (^/) :: Dom f a => f a -> a -> f a
--     default (^/) :: (Dom f a, VectorSpace a) => f a -> a -> f a
--     (^/) xs a = fmap (^/ a) xs
-- 
-- class (Foldable f, VectorSpace f) => InnerSpace f where
--    (<.>) :: Dom f a => f a -> f a -> a
--    default (<.>) :: (Dom f a, Additive (f a)) => f a -> f a -> a
--    xs <.> ys = getSumV . foldMap SumV . liftA2 (<.>) xs ys



class Additive1 v where
    negateV :: v -> v
    (^+^) :: v -> v -> v

class Additive1 v => Additive v where
    zeroV :: v

class Additive v => VectorSpace v where
    type Scalar v :: Type
    infixr 7 *^
    (*^) :: Scalar v -> v -> v

infixl 7 ^*
(^*) :: VectorSpace v => v -> Scalar v -> v
(^*) = flip (*^)

infixl 7 ^/
(^/) :: (VectorSpace v, Fractional (Scalar v)) => v -> Scalar v -> v
x ^/ a = x ^* (1 / a)

class VectorSpace v => InnerSpace v where
   (<.>) :: v -> v -> Scalar v

newtype SumV v = SumV { getSumV :: v }
    deriving (Eq, Ord, Read, Show)
instance Additive1 v => Semigroup (SumV v) where
    SumV x <> SumV y = SumV (x ^+^ y)
instance Additive v => Monoid (SumV v) where
    mempty = SumV zeroV
    mappend = (<>)



-- instance Num a => Additive1 a where
--     negateV = negate
--     (^+^) = (+)
-- 
-- instance Num a => Additive a where
--     zeroV = 0
-- 
-- instance Num a => VectorSpace a where
--     type Scalar a = a
--     (*^) a = (a *)
-- 
-- instance Real a => InnerSpace a where
--    a <.> b = a * b
-- 
-- instance RealFloat a => InnerSpace (Complex a) where
--    a <.> b = conjugate a * b



-- TODO: Use Template Haskell for this

instance Additive1 () where negateV _ = (); _ ^+^_ = ()
instance Additive () where zeroV = ()
instance VectorSpace () where type Scalar () = (); _ *^ _ = ()
instance InnerSpace () where _ <.> _ = ()

instance Additive1 Int where negateV = negate; (^+^) = (+)
instance Additive Int where zeroV = 0
instance VectorSpace Int where type Scalar Int = Int; (*^) a = (a *)
instance InnerSpace Int where a <.> b = a * b

instance Additive1 Rational where negateV = negate; (^+^) = (+)
instance Additive Rational where zeroV = 0
instance VectorSpace Rational where type Scalar Rational = Rational; (*^) a = (a *)
instance InnerSpace Rational where a <.> b = a * b

instance Additive1 Float where negateV = negate; (^+^) = (+)
instance Additive Float where zeroV = 0
instance VectorSpace Float where type Scalar Float = Float; (*^) a = (a *)
instance InnerSpace Float where a <.> b = a * b

instance Additive1 Double where negateV = negate; (^+^) = (+)
instance Additive Double where zeroV = 0
instance VectorSpace Double where type Scalar Double = Double; (*^) a = (a *)
instance InnerSpace Double where a <.> b = a * b



-- | The category of vector spaces over a given scalar type
class (VectorSpace v, Scalar v ~ s) => VectorSpaceOver s v
instance (VectorSpace v, Scalar v ~ s) => VectorSpaceOver s v
instance Category (VectorSpaceOver s)



-- | The cateogry's product type
type (*^*) s = CProduct (VectorSpaceOver s)

instance (Additive1 v, Additive1 w, s ~ Scalar v, s ~ Scalar w)
        => Additive1 ((*^*) s v w) where
    (^+^) = biliftA2 (^+^) (^+^)
    negateV = bimap negateV negateV

instance (Additive v, Additive w, s ~ Scalar v, s ~ Scalar w)
        => Additive ((*^*) s v w) where
    zeroV = bipure zeroV zeroV

instance (VectorSpace v, VectorSpace w, s ~ Scalar v, s ~ Scalar w)
        => VectorSpace ((*^*) s v w) where
    type Scalar ((*^*) s v w) = s
    (*^) a = bimap (a *^) (a *^)

instance (InnerSpace v, InnerSpace w, Additive1 s, s ~ Scalar v, s ~ Scalar w)
        => InnerSpace ((*^*) s v w) where
   CProduct (x1, x2) <.> CProduct (y1, y2) = (x1 <.> y1) ^+^ (x2 <.> y2)



-- | A mock function type
data (-^>) s a b where
    VFun :: (VectorSpaceOver s a, VectorSpaceOver s b)
            => (a -> b) -> ((-^>) s a b)
    VQCFun :: (VectorSpaceOver s a, VectorSpaceOver s b)
              => QC.Fun a b -> ((-^>) s a b)
instance Show (QC.Fun a b) => Show ((-^>) s a b) where
    show (VFun f) = show ("VFun" :: String)
    show (VQCFun f) = show f

instance Morphism ((-^>) s) where
    type MorCat ((-^>) s) = VectorSpaceOver s
    proveChase (VFun f) = Sub Dict
    proveChase (VQCFun f) = Sub Dict
    chase (VFun f) = f
    chase (VQCFun f) = QC.applyFun f
instance Discretization ((-^>) s) where
    discretize = VFun

instance (VectorSpaceOver s a, VectorSpaceOver s b, QC.Arbitrary (QC.Fun a b))
        => QC.Arbitrary ((-^>) s a b) where
    arbitrary = VQCFun <$> QC.arbitrary
    shrink (VQCFun f) = VQCFun <$> QC.shrink f
    shrink f = undefined
