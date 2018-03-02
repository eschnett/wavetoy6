module Sized (Sized(..), intVal) where

import Data.Proxy
import GHC.TypeLits



-- | Use as 'intVal @n'
intVal :: forall n. KnownNat n => Int
intVal = fromInteger (natVal (Proxy @n))

class KnownNat (Size v) => Sized v where
    type Size v :: Nat
    size :: Int
    size = intVal @(Size v)
