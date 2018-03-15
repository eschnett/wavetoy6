module Comonad ( Semicomonad(..)
               , law_Semicomonad_comm
               , Comonad(..)
               , law_Comonad_id
               , law_Comonad_apply
               , SemicomonadStore(..)
               , ComonadStore(..)
               , CompactSemicomonad(..)
               , law_CompactSemicomonad_restrict
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

import qualified Test.QuickCheck as QC

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

-- extend f . extend g = extend (f . extend g)
law_Semicomonad_comm :: forall f m n mn a b c.
                        ( Semicomonad f
                        , Morphism m, MorCat m ~ Dom f
                        , Morphism n, MorCat n ~ Dom f
                        , mn ~ MCompose m (FunMor f n) (f b)
                        , Eq (f c), Show (f c)
                        -- TODO: prove the ones below
                        , Morphism (FunMor f m), MorCat (FunMor f m) ~ Cod f
                        , Morphism (FunMor f n), MorCat (FunMor f n) ~ Cod f
                        , Morphism (FunMor f mn), MorCat (FunMor f mn) ~ Cod f
                        , Cod f (f a)
                        ) => f b `m` c -> f a `n` b -> f a -> QC.Property
law_Semicomonad_comm f g xs =
    (extend f `MCompose` extend g) `chase` xs QC.===
        (extend (f `MCompose` extend g)) `chase` xs

-- | Comonad
class Semicomonad f => Comonad f where
    extract :: f a -> a
    extract' :: (Morphism m, MorCat m ~ Dom f, n ~ FunMor f m)
                => Proxy m -> f a `n` a

-- extend extract = id
law_Comonad_id :: forall f m n a.
                  ( Comonad f
                  , Morphism m, MorCat m ~ Dom f
                  , n ~ FunMor f m
                  , Eq (f a), Show (f a)
                  -- TODO: prove the ones below
                  , Morphism n, MorCat n ~ Cod f
                  , Morphism (FunMor f n), MorCat (FunMor f n) ~ Cod f
                  , Cod f (f a)
                  ) => Proxy m -> f a -> QC.Property
law_Comonad_id _ xs = extend (extract' (Proxy @m)) `chase` xs QC.=== xs

-- extract . extend f = f
law_Comonad_apply :: forall f m a b.
                     ( Comonad f
                     , Morphism m, MorCat m ~ Dom f
                     , Morphism (FunMor f m), MorCat (FunMor f m) ~ Cod f
                     , Eq b, Show b
                     -- TODO: prove the ones below
                     , Cod f (f a)
                     ) => f a `m` b -> f a -> QC.Property
-- TODO: add UFun constructors here for 'extract\'' and 'extend'?
law_Comonad_apply f xs =
    (extract' (Proxy @m) `MCompose` extend f) `chase` xs QC.=== f `chase` xs



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

-- restrict . expand = id
law_CompactSemicomonad_restrict :: forall f g a.
                                   ( CompactSemicomonad g f
                                   , Dom f a
                                   , Default a
                                   , Eq (g a), Show (g a)
                                   ) => Proxy f -> g a -> QC.Property
law_CompactSemicomonad_restrict _ xs =
    (restrict . (expand :: g a -> f a)) xs QC.=== xs

-- | CompactComonad
class CompactSemicomonad g f => CompactComonad g f where
    extractC :: Dom f a => f a -> a
    extractC' :: Dom f a => g a -> a

-- | CompactSemicomonadStore
-- | CompactComonadStore
