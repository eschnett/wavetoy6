{-# LANGUAGE UndecidableInstances #-}

module Unboxed ( Unboxed
               , Vector(..)
               , UVector(..)
               ) where

import Data.Constraint
import qualified Data.Vector as V
import qualified Data.Vector.Unboxed as U

import GHC.TypeLits

import Category



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
newtype NVector (n :: Nat) a = NVector (V.Vector a)
    deriving (Eq, Ord, Read, Show)
newtype NUVector (n :: Nat) a = NUVector (U.Vector a)
    deriving (Eq, Ord, Read, Show)
