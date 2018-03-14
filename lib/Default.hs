{-# LANGUAGE UndecidableInstances #-}

module Default ( type (*?*)
               , type (-?>)
               ) where

import Data.Constraint
import Data.Default

import qualified Test.QuickCheck as QC
import qualified Test.QuickCheck.Instances ()

import Category



-- | The category of types with default values
instance Category Default



-- | The cateogry's product type

type (*?*) = CProduct Default

instance (Default a, Default b) => Default (a *?* b) where
    def = CProduct (def, def)



-- | A mock function type
data (-?>) a b where
    NFun :: (Default a, Default b) => (a -> b) -> (a -?> b)
    NQCFun :: (Default a, Default b) => QC.Fun a b -> (a -?> b)
instance Show (QC.Fun a b) => Show ((-?>) a b) where
    show (NFun f) = show ("NFun" :: String)
    show (NQCFun f) = show f

instance Morphism (-?>) where
    type MorCat (-?>) = Default
    proveChase (NFun f) = Sub Dict
    proveChase (NQCFun f) = Sub Dict
    chase (NFun f) = f
    chase (NQCFun f) = QC.applyFun f
instance Discretization (-?>) where
    discretize = NFun

instance (Default a, Default b, QC.Arbitrary (QC.Fun a b))
        => QC.Arbitrary ((-?>) a b) where
    arbitrary = NQCFun <$> QC.arbitrary
    shrink (NQCFun f) = NQCFun <$> QC.shrink f
    shrink f = undefined
