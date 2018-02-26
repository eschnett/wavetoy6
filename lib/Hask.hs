-- {-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Hask ( Hask(..)
            ) where

import Prelude hiding (Functor(..))

import Data.Constraint
import Data.Functor.Compose
import Data.Functor.Const
import Data.Functor.Identity
import Data.Functor.Product
import Data.Functor.Sum
import Data.Proxy

import qualified GHC.Exts as Exts (Any)

import Category



-- | 'Hask' is the category of all Haskell types
class Hask (o :: ObjKind)
instance Hask (o :: ObjKind)
instance Category Hask where
    -- type Obj Hask = Hask

instance Category k => Subcategory k Hask where
    proveSubcategory = Sub Dict

-- | Haskell functions are morphisms in Hask
instance Morphism (->) where
    type MorCat (->) = Hask
    proveChase :: (a -> b) -> Hask a :- Hask b
    proveChase f = Sub Dict
    chase = id
    -- type FromHaskC (->) a b = ()
    -- fromHask = id
instance Discretization (->) where
    discretize = id



-- | 'Impossible' is the empty category
class Bottom => Impossible (o :: ObjKind)
instance Category Impossible
instance Category k => Subcategory Impossible k where
    proveSubcategory = trans bottom (Sub Dict :: Impossible a :- Bottom)



-- | 'Proxy'
instance Functor Proxy where
    type Dom Proxy = Hask
    type Cod Proxy = Hask
    proveFunctor _ = Sub Dict
    type FunMor Proxy m = (->)
    proveFunMor _ = Sub Dict
    fmap f = \Proxy -> Proxy

-- | 'Identity'
instance Functor Identity where
    type Dom Identity = Hask
    type Cod Identity = Hask
    proveFunctor _ = Sub Dict
    type FunMor Identity m = (->)
    proveFunMor _ = Sub Dict
    fmap f = \(Identity x) -> Identity (chase f x)

-- | 'Either'
instance Functor (Either a) where
    type Dom (Either a) = Hask
    type Cod (Either a) = Hask
    proveFunctor _ = Sub Dict
    type FunMor (Either a) m = (->)
    proveFunMor _ = Sub Dict
    fmap f = \case
             Left x -> Left x
             Right y -> Right (chase f y)

-- | '(,)'
instance Functor ((,) a) where
    type Dom ((,) a) = Hask
    type Cod ((,) a) = Hask
    proveFunctor _ = Sub Dict
    type FunMor ((,) a) m = (->)
    proveFunMor _ = Sub Dict
    fmap f = \(x, y) -> (x, chase f y)

-- | '(->)'
instance Functor ((->) a) where
    type Dom ((->) a) = Hask
    type Cod ((->) a) = Hask
    proveFunctor _ = Sub Dict
    type FunMor ((->) a) m = (->)
    proveFunMor _ = Sub Dict
    fmap f = \fx -> chase f . fx

-- | '[]'
instance Functor [] where
    type Dom [] = Hask
    type Cod [] = Hask
    proveFunctor _ = Sub Dict
    type FunMor [] m = (->)
    proveFunMor _ = Sub Dict
    fmap f = \case
             [] -> []
             (x:xs) -> chase f x : fmap f xs

-- -- | 'Sum'
-- instance (Functor f, Functor g, Dom f ~ Dom g, Cod f ~ Cod g)
--         => Functor (Sum f g) where
--     type Dom (Sum f g) = Dom f
--     type Cod (Sum f g) = Cod f
--     proveFunctor _ = proveFunctor (Proxy @f) *** proveFunctor (Proxy @g)
--     type FunMor (Sum f g) m = FunMor f m
--     proveFunMor _ = Sub Dict
--     fmap f = \case
--              InL xs -> InL (fmap f xs)
--              InR ys -> InR (fmap f ys)

-- | 'Product'
instance (Functor f, Functor g, Dom f ~ Dom g) -- Cod f ~ Cod g
        => Functor (Product f g) where
    type Dom (Product f g) = Dom f
    type Cod (Product f g) = Hask -- Cod f
    proveFunctor :: Proxy (Product f g) -> Dom f a :- Hask (Product f g a)
    proveFunctor _ = Sub Dict
    type FunMor (Product f g) m = (->) -- FunMor f m
    proveFunMor _ = Sub Dict
    fmap ::
        forall m a b. (Dom f a, Dom f b, Morphism m, MorCat m ~ Dom f)
        => a `m` b -> Product f g a -> Product f g b
    fmap f = r \\ x1 \\ x2 \\ x3 \\ x4
        where
          r :: ( MorCat (FunMor f m) (f a)
               , Morphism (FunMor f m)
               , MorCat (FunMor g m) (g a)
               , Morphism (FunMor g m)
               )
              => Product f g a -> Product f g b
          r = \(Pair xs ys) -> Pair (chase (fmap f) xs) (chase (fmap f) ys)
          y1 :: (Morphism m, MorCat m ~ Dom f) :- (MorCat (FunMor f m) ~ Cod f)
          y1 = trans weaken2 $ proveFunMor (Proxy @f, Proxy @m)
          x1 :: (Dom f a) :- MorCat (FunMor f m) (f a)
          x1 = proveFunctor (Proxy @f) \\ y1
          x2 :: () :- Morphism (FunMor f m)
          x2 = Sub Dict \\ (trans weaken1 $ proveFunMor (Proxy @f, Proxy @m))
          y3 :: (Morphism m, MorCat m ~ Dom g) :- (MorCat (FunMor g m) ~ Cod g)
          y3 = trans weaken2 $ proveFunMor (Proxy @g, Proxy @m)
          x3 :: (Dom g a) :- MorCat (FunMor g m) (g a)
          x3 = proveFunctor (Proxy @g) \\ y3
          x4 :: () :- Morphism (FunMor g m)
          x4 = Sub Dict \\ (trans weaken1 $ proveFunMor (Proxy @g, Proxy @m))
             


-- -- | 'Compose'
-- instance (Functor f, Functor g, Dom f ~ Cod g) => Functor (Compose f g) where
--     type Dom (Compose f g) = Dom g
--     type Cod (Compose f g) = Hask -- Cod f
--     -- proveFunctor _ = trans (proveFunctor (Proxy @f)) (proveFunctor (Proxy @g))
--     proveFunctor _ = Sub Dict
--     type FunMor (Compose f g) m = (->) -- FunMor f (FunMor g m)
--     proveFunMor _ = Sub Dict
--     fmap f = case proveFunMor (Proxy @g) of
--                Sub Dict -> \(Compose xss) -> Compose (chase (fmap (fmap f)) xss)
--     -- fmap f = \(Compose xss) -> Compose (chase (fmap (fmap f)) xss)
