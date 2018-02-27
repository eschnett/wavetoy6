{-# LANGUAGE UndecidableSuperClasses #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module Hask ( Hask
            , Impossible
            ) where

import Prelude hiding (Functor(..))

import Data.Constraint
import Data.Functor.Compose
import Data.Functor.Identity
import Data.Functor.Product
import Data.Functor.Sum
import Data.Proxy

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

-- | 'Sum'
instance ( Functor f, Functor g, Dom f ~ Dom g
         , Subcategory (Cod f) Hask, Subcategory (Cod g) Hask)
        => Functor (Sum f g) where
    type Dom (Sum f g) = Dom f
    type Cod (Sum f g) = Hask
    proveFunctor _ = Sub Dict
    type FunMor (Sum f g) m = (->)
    proveFunMor _ = Sub Dict
    fmap ::
        forall m a b. (Dom f a, Dom f b, Morphism m, MorCat m ~ Dom f)
        => a `m` b -> Sum f g a -> Sum f g b
    fmap f = r \\ p1 \\ p2 \\ p3 \\ p4
        where
          r :: ( Morphism (FunMor f m)
               , MorCat (FunMor f m) (f a)
               , Morphism (FunMor g m)
               , MorCat (FunMor g m) (g a)
               )
              => Sum f g a -> Sum f g b
          r = \case
              InL xs -> InL (chase (fmap f) xs)
              InR ys -> InR (chase (fmap f) ys)

          p1 :: () :- Morphism (FunMor f m)
          q2 :: (Morphism m, MorCat m ~ Dom f) :- (MorCat (FunMor f m) ~ Cod f)
          p2 :: Dom f a :- MorCat (FunMor f m) (f a)
          p3 :: () :- Morphism (FunMor g m)
          q4 :: (Morphism m, MorCat m ~ Dom g) :- (MorCat (FunMor g m) ~ Cod g)
          p4 :: Dom g a :- MorCat (FunMor g m) (g a)

          p1 = Sub Dict \\ (trans weaken1 $ proveFunMor (Proxy @f, Proxy @m))
          q2 = trans weaken2 $ proveFunMor (Proxy @f, Proxy @m)
          p2 = proveFunctor (Proxy @f) \\ q2
          p3 = Sub Dict \\ (trans weaken1 $ proveFunMor (Proxy @g, Proxy @m))
          q4 = trans weaken2 $ proveFunMor (Proxy @g, Proxy @m)
          p4 = proveFunctor (Proxy @g) \\ q4

-- | 'Product'
instance ( Functor f, Functor g, Dom f ~ Dom g
         , Subcategory (Cod f) Hask, Subcategory (Cod g) Hask)
        => Functor (Product f g) where
    type Dom (Product f g) = Dom f
    type Cod (Product f g) = Hask
    proveFunctor :: Proxy (Product f g) -> Dom f a :- Hask (Product f g a)
    proveFunctor _ = Sub Dict
    type FunMor (Product f g) m = (->)
    proveFunMor _ = Sub Dict
    fmap ::
        forall m a b. (Dom f a, Dom f b, Morphism m, MorCat m ~ Dom f)
        => a `m` b -> Product f g a -> Product f g b
    fmap f = r \\ p1 \\ p2 \\ p3 \\ p4
        where
          r :: ( Morphism (FunMor f m)
               , MorCat (FunMor f m) (f a)
               , Morphism (FunMor g m)
               , MorCat (FunMor g m) (g a)
               )
              => Product f g a -> Product f g b
          r = \(Pair xs ys) -> Pair (chase (fmap f) xs) (chase (fmap f) ys)

          p1 :: () :- Morphism (FunMor f m)
          q2 :: (Morphism m, MorCat m ~ Dom f) :- (MorCat (FunMor f m) ~ Cod f)
          p2 :: Dom f a :- MorCat (FunMor f m) (f a)
          p3 :: () :- Morphism (FunMor g m)
          q4 :: (Morphism m, MorCat m ~ Dom g) :- (MorCat (FunMor g m) ~ Cod g)
          p4 :: Dom g a :- MorCat (FunMor g m) (g a)

          p1 = Sub Dict \\ (trans weaken1 $ proveFunMor (Proxy @f, Proxy @m))
          q2 = trans weaken2 $ proveFunMor (Proxy @f, Proxy @m)
          p2 = proveFunctor (Proxy @f) \\ q2
          p3 = Sub Dict \\ (trans weaken1 $ proveFunMor (Proxy @g, Proxy @m))
          q4 = trans weaken2 $ proveFunMor (Proxy @g, Proxy @m)
          p4 = proveFunctor (Proxy @g) \\ q4

-- | 'Compose'
instance ( Functor f, Functor g
         , Cod g ~ Dom f        -- TODO: Subcategory (Cod g) (Dom f)
         , Subcategory (Cod f) Hask)
        => Functor (Compose f g) where
    type Dom (Compose f g) = Dom g
    type Cod (Compose f g) = Hask
    proveFunctor _ = Sub Dict
    type FunMor (Compose f g) m = (->)
    proveFunMor _ = Sub Dict
    fmap :: forall m n p a b.
            ( Dom g a, Dom g b, Morphism m, MorCat m ~ Dom g
            , n ~ FunMor g m, p ~ FunMor f n
            )
            => a `m` b -> Compose f g a -> Compose f g b
    fmap f = r \\ p4 \\ p5 \\ p6 \\ p7 \\ p10 \\ p11 \\ p14 \\ p15
        where
          r :: ( Morphism n
               , MorCat n ~ Cod g
               , Dom f (g a)
               , Dom f (g b)
               , Cod f (f (g a))
               -- , Cod f (f (g b))
               , Morphism p
               , MorCat p ~ Cod f
               )
               => Compose f g a -> Compose f g b
          r = \(Compose xss) -> Compose (chase (fmap (fmap f)) xss)

          p1 :: Dom g a :- Cod g (g a)
          p2 :: Dom g b :- Cod g (g b)
          p3 :: (Morphism m, MorCat m ~ Dom g)
                :- (Morphism n, MorCat n ~ Cod g)
          p4 :: (Morphism m, MorCat m ~ Dom g) :- Morphism n
          p5 :: (Morphism m, MorCat m ~ Dom g) :- (MorCat n ~ Cod g)

          p6 :: Dom g a :- Dom f (g a)
          p7 :: Dom g b :- Dom f (g b)
          p8 :: Dom f (g a) :- Cod f (f (g a))
          p9 :: Dom f (g b) :- Cod f (f (g b))
          p10 :: Dom g a :- Cod f (f (g a))
          p11 :: Dom g b :- Cod f (f (g b))
          p12 :: (Morphism n, MorCat n ~ Dom f)
                 :- (Morphism p, MorCat p ~ Cod f)
          p13 :: (Morphism m, MorCat m ~ Dom g)
                 :- (Morphism p, MorCat p ~ Cod f)
          p14 :: (Morphism m, MorCat m ~ Dom g) :- Morphism p
          p15 :: (Morphism m, MorCat m ~ Dom g) :- (MorCat p ~ Cod f)

          p1 = proveFunctor (Proxy @g)
          p2 = proveFunctor (Proxy @g)
          p3 = proveFunMor (Proxy @g, Proxy @m)
          p4 = trans weaken1 p3
          p5 = trans weaken2 p3

          p6 = proveFunctor (Proxy @g)
          p7 = proveFunctor (Proxy @g)
          p8 = proveFunctor (Proxy @f)
          p9 = proveFunctor (Proxy @f)
          p10 = trans p8 p1
          p11 = trans p9 p2
          p12 = proveFunMor (Proxy @f, Proxy @n)
          p13 = trans p12 p3
          p14 = trans weaken1 p13
          p15 = trans weaken2 p13
