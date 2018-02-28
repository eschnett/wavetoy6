{-# LANGUAGE UndecidableInstances #-}

module Numeric (Numeric) where

import Data.Constraint

import Category



-- | The category of numeric types
class Num a => Numeric a
instance Num a => Numeric a
instance Category Numeric



-- | A mock function type
data (-.>) a b where
    NFun :: (Num a, Num b) => (a -> b) -> (a -.> b)
instance Morphism (-.>) where
    type MorCat (-.>) = Numeric
    proveChase (NFun f) = Sub Dict
    chase (NFun f) = f
instance Discretization (-.>) where
    discretize = NFun
