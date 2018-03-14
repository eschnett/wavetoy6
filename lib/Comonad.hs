module Comonad ( Semicomonad(..)
               , Comonad(..)
               , SemicomonadStore(..)
               , ComonadStore(..)
               , CompactSemicomonad(..)
               , CompactComonad(..)
               ) where

import Prelude hiding ( Foldable(..)
                      , Functor(..)
                      , Applicative(..)
                      , Traversable(..)
                      , Monad(..)
                      )

import Data.Default
import Data.Proxy

import Category
import Functor



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
    extract' :: (Morphism m, MorCat m ~ Dom f, n ~ FunMor f m)
                => Proxy m -> f a `n` a

-- ComonadApply

-- | SemicomonadStore
-- TODO: avoid this, it doesn't seem useful
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



-- | CompactSemicomonad
class (Functor f, Functor g, Dom g ~ Dom f, Cod g ~ Dom g)
        => CompactSemicomonad g f where
    -- | restrict . expand = id
    -- Note that VectorSpace provides a Default
    restrict :: (Default a, Dom f a) => f a -> g a
    expand :: (Default a, Dom f a) => g a -> f a
    extendC :: (Dom f a, Dom f b, Morphism m, MorCat m ~ Dom f, n ~ FunMor f m)
               => g a `m` b -> f a `n` f b
    duplicateC :: Dom f a => f a -> f (g a)
    default duplicateC :: (Dom f a, Dom f (g a), FunMor f (MId (Dom f)) ~ (->))
                          => f a -> f (g a)
    duplicateC = extendC MId

-- | CompactComonad
class CompactSemicomonad g f => CompactComonad g f where
    extractC :: Dom f a => f a -> a
    extractC' :: Dom f a => g a -> a

-- | CompactSemicomonadStore
-- | CompactComonadStore
