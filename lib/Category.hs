{-# LANGUAGE UndecidableInstances #-}

module Category ( CatKind
                , ObjKind
                , MorKind
                , Category(..)
                , chase2
                , Subcategory(..)
                , ProveSubcategory
                , Object(..)
                , CProduct(..)
                , CSum(..)
                , Morphism(..)
                , Discretization(..)
                , FnEqual(..)
                , FnProp
                , checkFnEqual
                , law_Discretization_inv
                , law_Discretization_approx
                , MId(..)
                , MCompose(..)
                , law_MId_id
                , law_MCompose_compose
                , law_MCompose_left_id
                , law_MCompose_right_id
                , law_MCompose_assoc
                ) where

import Data.Biapplicative
import Data.Bifunctor()
import Data.Constraint
import Data.Default
import Data.Kind
import Data.Proxy

import qualified Test.QuickCheck as QC



type CatKind = Type -> Constraint
type ObjKind = Type
type MorKind = Type -> Type -> Type



-- | Constraints
class Category (k :: CatKind) where
    -- | This is unused
    type Obj k :: ObjKind -> Constraint
    type Obj k = k

-- | Subcategory relationahips. Note that it does not matter why a
-- category 's' is a subcategory of another category 'k', and we can
-- therefore allow incoherent instances.
class (Category s, Category k)
        => Subcategory (s :: CatKind) (k :: CatKind) where
    proveSubcategory :: s a :- k a

-- | 'Subcategory' relations form a monoid
instance {-# INCOHERENT #-} Category k => Subcategory k k where
    proveSubcategory = refl

-- | Prove that 'k1' is a subcategory of 'k3' by explicitly providing
-- a path via 'k2'. (If we could express 'exists k2', then this would
-- not be necessary.)
class (Category k1, Category k2, Category k3,
       Subcategory k2 k3, Subcategory k1 k2)
    => ProveSubcategory k2 k1 k3

instance {-# INCOHERENT #-}
        (Category k1, Category k3, ProveSubcategory k2 k1 k3)
        => Subcategory k1 k3 where
    proveSubcategory =
        trans
        (proveSubcategory :: k2 a :- k3 a)
        (proveSubcategory :: k1 a :- k2 a)



-- | Types
-- (This class is unused.)
class Object (o :: ObjKind) where
    type ObjCat o :: CatKind



-- | Products
newtype CProduct (k :: CatKind) a b = CProduct { getCProduct :: (a, b) }
    deriving ( Eq, Ord, Read, Show
             , QC.Arbitrary, QC.CoArbitrary
             , Bifunctor, Biapplicative, Default
             )

instance QC.Function (a, b) => QC.Function (CProduct k a b) where
    function = QC.functionMap getCProduct CProduct



-- | Sums
newtype CSum (k :: CatKind) a b = CSum { getCSum :: Either a b }
    deriving ( Eq, Ord, Read, Show
             , QC.Arbitrary, QC.CoArbitrary
             , Bifunctor
             )

instance QC.Function (Either a b) => QC.Function (CSum k a b) where
    function = QC.functionMap getCSum CSum



-- | A law (property) stating that two functions are equal
data FnEqual a b where
    FnEqual :: ( Morphism m, MorCat m a
               , Morphism n, MorCat n a
               , MorCat m ~ MorCat n)
               => a `m` b -> a `n` b -> FnEqual a b

type FnProp a = a -> QC.Property

checkFnEqual :: (Show b, Eq b) => FnEqual a b -> FnProp a
checkFnEqual (FnEqual fx fy) z = fx `chase` z QC.=== fy `chase` z



-- | Functions
class Category (MorCat m) => Morphism (m :: MorKind) where
    type MorCat m :: CatKind
    proveChase :: m a b -> MorCat m a :- MorCat m b
    -- | Each morphism has a dinatural transformation to Haskell functions
    chase :: MorCat m a => a `m` b -> a -> b
    -- type FromHaskC m a b :: Constraint
    -- -- type FromHaskC m a b = (MorCat m a, MorCat m b)
    -- fromHask :: FromHaskC m a b => (a -> b) -> a `m` b

chase2 :: (Morphism m, Morphism n, MorCat m a, MorCat n b)
          => a `m` (b `n` c) -> a -> b -> c
chase2 f x y = f `chase` x `chase` y

class Morphism m => Discretization (m :: MorKind) where
    -- | A morphism might have an "approximate dinatural
    -- transformation" from Haskell functions. This also defines an
    -- adjoint functor pair.
    discretize :: (MorCat m a, MorCat m b) => (a -> b) -> a `m` b

-- | discretize . chase == id
law_Discretization_inv :: forall m a b.
                          ( Discretization m
                          , MorCat m a
                          , MorCat m b
                          ) => a `m` b -> FnEqual a b
law_Discretization_inv f = discretize @m (chase f) `FnEqual` f

-- | chase . discretize `approx` id
law_Discretization_approx :: forall m a b.
                             ( Discretization m
                             , MorCat m a
                             , MorCat m b
                             , Morphism (->), MorCat (->) a
                             ) => Proxy m -> (a -> b) -> FnEqual a b
law_Discretization_approx _ f = chase (discretize @m f) `FnEqual` f



data MId (k :: CatKind) a b where
    MId :: MId k a a
deriving instance Eq (MId k a b)
deriving instance Ord (MId k a b)
deriving instance Show (MId k a b)
instance Category k => Morphism (MId k) where
    type MorCat (MId k) = k
    proveChase MId = refl
    chase MId = id
    -- type FromHaskC (MId k) a b = a ~ b
    -- fromHask _ = MId

data MCompose m n b a c where
    MCompose :: m b c -> n a b -> MCompose m n b a c
                deriving (Eq, Ord, Read, Show)
    
instance (Morphism m, Morphism n, MorCat m ~ MorCat n)
        => Morphism (MCompose m n b) where
    type MorCat (MCompose m n b) = MorCat m
    proveChase (MCompose f g) = trans (proveChase f) (proveChase g)
    chase (MCompose f g) =
        case proveChase g of Sub Dict -> chase f . chase g
    -- | We arbitrarily split f === id . f
    -- type FromHaskC (MCompose m n b) a c =
    --     (b ~ c, FromHaskC m b c, FromHaskC n a b)
    -- fromHask f = MCompose (fromHask id) (fromHask f)

-- MId == id
law_MId_id :: forall k a.
              ( Category k
              , k a
              , Eq a, Show a
              ) => Proxy k -> a -> QC.Property
law_MId_id _ x = (MId :: MId k a a) `chase` x QC.=== x

-- f `MCompose` g == f . g
law_MCompose_compose :: ( Morphism m
                        , Morphism n
                        , k ~ MorCat m
                        , k ~ MorCat n
                        , k a, k b
                        , Eq c, Show c
                        ) => b `m` c -> a `n` b -> a -> QC.Property
law_MCompose_compose f g x =
    MCompose f g `chase` x QC.=== (chase f . chase g) x

-- MId `MCompose` f == f
law_MCompose_left_id :: ( Morphism m
                        , k ~ MorCat m
                        , k a
                        , Eq b, Show b
                        ) => a `m` b -> a -> QC.Property
law_MCompose_left_id f x = (MId `MCompose` f) `chase` x QC.=== f `chase` x

-- f `MCompose` MId == f
law_MCompose_right_id :: ( Morphism m
                         , k ~ MorCat m
                         , k a
                         , Eq b, Show b
                         ) => a `m` b -> a -> QC.Property
law_MCompose_right_id f x = (f `MCompose` MId) `chase` x QC.=== f `chase` x

-- (f . g) . h == f . (g . h)
law_MCompose_assoc :: ( Morphism m
                      , Morphism n
                      , Morphism p
                      , k ~ MorCat m
                      , k ~ MorCat n
                      , k ~ MorCat p
                      , k a
                      , Eq d, Show d
                      ) => c `m` d -> b `n` c -> a `p` b -> a -> QC.Property
law_MCompose_assoc f g h x =
    ((f `MCompose` g) `MCompose` h) `chase` x QC.===
    (f `MCompose` (g `MCompose` h)) `chase` x
