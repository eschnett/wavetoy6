{-# LANGUAGE UndecidableInstances #-}

module Category ( CatKind
                , ObjKind
                , MorKind
                , Category(..)
                , chase2
                , Subcategory(..)
                , ProveSubcategory
                , Object(..)
                , Morphism(..)
                , Discretization(..)
                , MId(..)
                , MCompose(..)
                , Functor(..)
                , Unfoldable(..)
                , Foldable(..)
                , Apply(..)
                , Applicative(..)
                , Alt(..)
                , Alternative(..)
                , Distributive(..)
                , Traversable(..)
                , Monad(..)
                , Semicomonad(..)
                , Comonad(..)
                , SemicomonadStore(..)
                , ComonadStore(..)
                , LocalSemicomonad(..)
                , LocalComonad(..)
                ) where

import Prelude hiding ( Foldable(..)
                      , Functor(..)
                      , Applicative(..)
                      , Traversable(..)
                      , Monad(..)
                      )

import Data.Constraint
import Data.Kind
import Data.Proxy

import Comonoid



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
          => m a (n b c) -> a -> b -> c
chase2 f x y = f `chase` x `chase` y

class Morphism m => Discretization (m :: MorKind) where
    -- | A morphism might have an "approximate dinatural
    -- transformation" from Haskell functions
    discretize :: (MorCat m a, MorCat m b) => (a -> b) -> a `m` b



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



-- | Functor
class (Category (Dom f), Category (Cod f)) => Functor f where
    type Dom f :: CatKind
    type Cod f :: CatKind
    type FunMor f (m :: MorKind) :: MorKind
    -- type FunMor f :: MorKind -> MorKind
    -- TODO: Rename this to 'proveFunObj'?
    proveFunCod :: Proxy f -> Dom f a :- Cod f (f a)
    proveFunMor ::
        (n ~ FunMor f m)
        => (Proxy f, Proxy m)
        -> (Morphism m, MorCat m ~ Dom f) :- (Morphism n, MorCat n ~ Cod f)
    -- TODO: allow 'Subcategory (MorCat m) (Dom f)'
    fmap ::
        (Dom f a, Dom f b, Morphism m, MorCat m ~ Dom f, n ~ FunMor f m)
        => a `m` b -> f a `n` f b

-- | Unfoldable
class Functor f => Unfoldable f where
    mapUnfold :: (Comonoid a, Dom f b) => (a -> b) -> a -> f b
    unfold :: (Comonoid a, Dom f a) => a -> f a
    unfold = mapUnfold id

-- | Foldable
-- E. Kmett: "Folds are closed, corepresentable profunctors"
class Functor f => Foldable f where
    foldMap :: (Dom f a, Monoid b) => (a -> b) -> f a -> b
    fold :: (Dom f a, Monoid a) => f a -> a
    fold = foldMap id

-- | Apply
class Functor f => Apply f where
    -- liftA2' :: ( Dom f a, Dom f b, Dom f c
    --            , Morphism m, MorCat m ~ Dom f, n ~ FunMor f m
    --            )
    --            => (a, b) `m` c -> (f a, f b) `n` f c
    liftA2 :: ( Dom f a, Dom f b, Dom f c
              , Morphism m, MorCat m ~ Dom f, n ~ FunMor f m
              )
              => a `m` (b `m` c) -> f a `n` (f b `n` f c)

-- | Applicative
class Apply f => Applicative f where
    pure :: Dom f a => a -> f a

-- | Alt
class Applicative f => Alt f where
    (<|>) :: f a -> f a -> f a

-- | Alternative
class Alt f => Alternative f where
    empty :: f a

-- | Distributive
class (Functor f, Dom f ~ Cod f) => Distributive f where
    cotraverseMap :: (Foldable g, Morphism m)
                     => g b `m` c -> a `m` f b -> g a -> f c
    -- collect = cotraverseMap MId
    -- distribute = cotraverseMap MId MId

-- | Traversable
class (Functor f, Dom f ~ Cod f) => Traversable f where
    mapTraverse :: (Applicative g, Morphism m)
                   => f b `m` c -> a `m` g b -> f a -> g c
   -- traverse = mapTraverse MId
   -- sequence = mapTraverse MId MId

-- | Monad
class (Applicative f, Dom f ~ Cod f) => Monad f where
    (>>=) :: (Morphism m, MorCat m ~ Dom f) => f a -> (a `m` f b) -> f b
    -- (<=<) :: (Morphism m, MorCat m ~ Dom f)
    --          => b `m` f c -> a `m` f b -> a `m` f c

-- MonadZero, MonadPlus

-- | Semicomonad (also called 'Extend'; see package "semigroupoids")
class (Functor f, Dom f ~ Cod f) => Semicomonad f where
    extend :: (Morphism m, MorCat m ~ Dom f, n ~ FunMor f m)
              => f a `m` b -> f a `n` f b
    -- default extend :: ( Morphism m, MorCat m ~ Dom f, n ~ FunMor f m
    --                   , n ~ (->)
    --                   ) => f a `m` b -> f a `n` f b
    -- extend f = fmap f . duplicate
    -- (=<=) :: Morphism m => f b `m` c -> f a `m` b -> f a `m` c
    duplicate :: f a -> f (f a)
    default duplicate :: (FunMor f (MId (Dom f)) ~ (->)) => f a -> f (f a)
    duplicate = extend MId
    -- duplicate' :: (Morphism m, MorCat m ~ Dom f, n ~ FunMor f m)
    --               => Proxy m -> f a `n` f (f a)
    -- duplicate' _ = extend MId

-- | Comonad
class Semicomonad f => Comonad f where
    extract :: f a -> a

-- ComonadApply

-- | SemicomonadStore
class Semicomonad f => SemicomonadStore s f | f -> s where
    peek :: s -> f a -> a

-- | ComonadStore
class (Comonad f, SemicomonadStore s f) => ComonadStore s f | f -> s where
    pos :: f a -> s
    peeks :: (s -> s) -> f a -> a
    peeks f xs = peek (f (pos xs)) xs
    seek :: s -> f a -> f a
    seek s = peek s . duplicate
    seeks :: (s -> s) -> f a -> f a
    seeks f = peeks f . duplicate
    -- experiment :: Functor g => (s -> g s) -> f a -> g a
    -- experiment f xs = fmap (`peek` xs) (f (pos xs))



-- -- | Global
-- class (Functor f, Functor (Local f)) => Global f where
--     type Local f :: Type -> Type
--     -- | local . global = id
--     local :: f a -> Local f a
--     global :: Local f a -> f a
-- 
-- -- | LocalComonad
-- class (Global f, Cod (Local f) ~ Dom (Local f)) => LocalComonad f where
--     extractL :: f a -> a
--     extendL :: (Morphism m, MorCat m ~ Dom f, n ~ FunMor f m)
--                => Local f a `m` b -> f a `n` f b
--     duplicateL :: f a -> f (Local f a)
--     default duplicateL :: (FunMor f (MId (Dom f)) ~ (->))
--                           => f a -> f (Local f a)
--     duplicateL = extendL MId
-- 
-- -- This is correct, but leads to overlapping instances
-- -- instance (Functor f, LocalComonad f, Local f ~ f) => Comonad f where
-- --     extract = extractL
-- --     extend = extendL
-- --     duplicate = duplicateL

-- | LocalSemicomonad
class (Functor f, Functor (Local f), Dom (Local f) ~ Dom f)
        => LocalSemicomonad f where
    type Local f :: Type -> Type
    -- | local . global = id
    global :: Dom f a => a -> Local f a -> f a
    local :: Dom f a => a -> f a -> Local f a
    extendL :: (Dom f a, Dom f b, Morphism m, MorCat m ~ Dom f, n ~ FunMor f m)
               => Local f a `m` b -> f a `n` f b
    duplicateL :: Dom f a => f a -> f (Local f a)
    default duplicateL :: ( Dom f a, Dom f (Local f a)
                          , FunMor f (MId (Dom f)) ~ (->))
                         => f a -> f (Local f a)
    duplicateL = extendL MId

-- | LocalComonad
class (LocalSemicomonad f, Functor (Local f), Dom (Local f) ~ Dom f)
        => LocalComonad f where
    extractL :: Dom f a => f a -> a
