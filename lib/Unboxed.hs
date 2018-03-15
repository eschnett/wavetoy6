{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}

module Unboxed ( Unboxed
               , type (*#*)
               , type (-#>)(..)
               ) where

import Prelude hiding (Functor(..))

import Data.Constraint
import Data.Default
import qualified Data.Vector.Unboxed as U
import Data.Vector.Unboxed.Deriving

import qualified Test.QuickCheck as QC

import Category
-- import Numeric
import Default()
import Functor



-- | The category of unboxed types with default values
class (U.Unbox a, Default a) => Unboxed a
instance (U.Unbox a, Default a) => Unboxed a
instance Category Unboxed



-- | The category's product type

type (*#*) = CProduct Unboxed

derivingUnbox "CProduct_Unboxed"
    [t| forall a b. (U.Unbox a, U.Unbox b) => a *#* b -> (a, b) |]
    [| \(CProduct (x, y)) -> (x, y) |]
    [| \(x, y) -> CProduct (x, y) |]

-- instance (Num a, Num b) => Num (a *#* b) where
--     CProduct (x1, x2) + CProduct (y1, y2) = CProduct (x1 + y1, x2 + y2)
--     CProduct (x1, x2) * CProduct (y1, y2) = CProduct (x1 * y1, x2 * y2)
--     negate (CProduct (x1, x2)) = CProduct (negate x1, negate x2)
--     abs (CProduct (x1, x2)) = CProduct (abs x1, abs x2)
--     signum (CProduct (x1, x2)) = CProduct (signum x1, signum x2)
--     fromInteger i = CProduct (fromInteger i, fromInteger i)

-- instance (AdditiveGroup v, AdditiveGroup w, Scalar v ~ Scalar w)
--         => AdditiveGroup (v *#* w) where
--     (^+^) = biliftA2 (^+^) (^+^)
--     zeroV = bipure zeroV zeroV
--     negateV = bimap negateV negateV
-- 
-- instance (VectorSpace v, VectorSpace w, Scalar v ~ Scalar w)
--         => VectorSpace (v *#* w) where
--     type Scalar (v *#* w) = Scalar v
--     (*^) a = bimap (a *^) (a *^)
-- 
-- instance (InnerSpace v, InnerSpace w, Scalar v ~ Scalar w)
--         => InnerSpace (v *#* w) where
--    CProduct (x1, x2) <.> CProduct (y1, y2) = (x1 <.> y1) ^+^ (x2 <.> y2)



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



instance Unboxed a => Functor ((*#*) a) where
    type Dom ((*#*) a) = Unboxed
    type Cod ((*#*) a) = Unboxed
    type FunMor ((*#*) a) m = (-#>)
    proveFunCod _ = Sub Dict
    proveFunMor _ = Sub Dict
    fmap f = UFun (\(CProduct (a, x)) -> CProduct (a, f `chase` x))
