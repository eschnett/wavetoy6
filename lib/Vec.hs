{-# LANGUAGE TemplateHaskell #-}

{-# OPTIONS_GHC -funbox-strict-fields #-}

module Vec ( CVec3(..)
           , Vec3
           , UVec3
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
import qualified Data.Vector.Unboxed as U
import Data.Vector.Unboxed.Deriving

import GHC.TypeLits

import qualified Test.QuickCheck as QC

import Category
import Functor
import Hask
import Sized
import Unboxed



data CVec3 (k :: CatKind) (n :: Nat) a =
    CVec3 !Int !a !a !a
    deriving (Eq, Ord, Read, Show)

derivingUnbox "CVec3"
    [t| forall k n a. U.Unbox a => CVec3 k n a -> (Int, a, a, a) |]
    [| \(CVec3 i xm x xp) -> (i, xm, x, xp) |]
    [| \(i, xm, x, xp) -> CVec3 i xm x xp |]

instance (KnownNat n, Default a, QC.Arbitrary a)
        => QC.Arbitrary (CVec3 k n a) where
    arbitrary = do i <- QC.choose (0, intVal @n - 1)
                   xm' <- QC.arbitrary
                   let xm = if i - 1 < 0 then def else xm'
                   x <- QC.arbitrary
                   xp' <- QC.arbitrary
                   let xp = if i + 1 >= 3 then def else xp'
                   P.return (CVec3 i xm x xp)
    shrink (CVec3 i xm x xp) =
        [CVec3 i' xm' x' xp' | (i', xm', x', xp') <- QC.shrink (i, xm, x, xp)]

instance Default a => Default (CVec3 k n a) where
    def = CVec3 0 def def def

instance (Default a, Eq a, Validity a) => Validity (CVec3 k n a) where
    validate (CVec3 i xm x xp) =
        mconcat
        [ i <?!> "position"
        , i >= 0 && i < 3 <?@> "index is in range"
        , xm <?!> "xm"
        , x <?!> "x"
        , xp <?!> "xp"
        , i - 1 >= 0 || xm == def <?@> "xm is not out of range"
        , i + 1 < 3 || xp == def <?@> "xp is not out of range"
        ]



type Vec3 = CVec3 Hask
  
instance Functor (CVec3 Hask n) where
    type Dom (CVec3 Hask n) = Hask
    type Cod (CVec3 Hask n) = Hask
    type FunMor (CVec3 Hask n) m = (->)
    proveFunCod _ = Sub Dict
    proveFunMor _ = Sub Dict
    fmap f (CVec3 i xm x xp) =
        CVec3 i (f `chase` xm) (f `chase` x) (f `chase` xp)

instance KnownNat n => Apply (CVec3 Hask n) where
    liftA2' f = uncurry (liftA2 (curry (chase f . CProduct))) . getCProduct
    liftA2 f (CVec3 i xm x xp) (CVec3 j ym y yp) =
        CVec3 ((i + j) `mod` intVal @n)
                  (f `chase` xm `chase` ym)
                  (f `chase` x `chase` y)
                  (f `chase` xp `chase` yp)

instance KnownNat n => Applicative (CVec3 Hask n) where
    pure' _ = pure
    pure x = CVec3 0 x x x



type UVec3 = CVec3 Unboxed
    
instance Functor (CVec3 Unboxed n) where
    type Dom (CVec3 Unboxed n) = Unboxed
    type Cod (CVec3 Unboxed n) = Unboxed
    type FunMor (CVec3 Unboxed n) m = (-#>)
    proveFunCod _ = Sub Dict
    proveFunMor _ = Sub Dict
    -- fmap f = UFun (\(CVec3 i xm x xp) ->
    --                CVec3 i (f `chase` xm) (f `chase` x) (f `chase` xp))
    fmap f = UFun go
        where go (CVec3 i xm x xp) = CVec3 i (g xm) (g x) (g xp)
              g = chase f

-- instance (KnownNat n, Num a) => Num (CVec3 Unboxed n a) where
--     (+) = curry (chase (liftA2' (UFun (uncurry (+) . getCProduct))) . CProduct)
--     (*) = curry (chase (liftA2' (UFun (uncurry (*) . getCProduct))) . CProduct)
--     negate = chase (fmap (UFun negate))
--     abs = chase (fmap (UFun abs))
--     signum = chase (fmap (UFun signum))
--     fromInteger = pure . fromInteger

instance KnownNat n => Apply (CVec3 Unboxed n) where
    -- liftA2' f =
    --     UFun (\(CProduct (CVec3 i xm x xp, CVec3 j ym y yp)) ->
    --         CVec3 ((i + j) `mod` intVal @n)
    --                 (f `chase` (CProduct (xm, ym)))
    --                 (f `chase` (CProduct (x, y)))
    --                 (f `chase` (CProduct (xp, yp))))
    liftA2' f = UFun (uncurry go . getCProduct)
        where go (CVec3 i xm x xp) (CVec3 j ym y yp) =
                  CVec3 ((i + j) `mod` intVal @n) (g xm ym) (g x y) (g xp yp)
              g = curry (chase f . CProduct)
                  
    -- 'liftA2' cannot be implemented for categories without functions
    liftA2 = undefined

instance KnownNat n => Applicative (CVec3 Unboxed n) where
    pure' _ = UFun pure
    pure x = CVec3 0 x x x
