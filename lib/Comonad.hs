module Comonad ( Semicomonad(..)
               , law_Semicomonad_comm
               , Comonad(..)
               , law_Comonad_id
               , law_Comonad_apply
               , SemicomonadStore(..)
               , ComonadStore(..)
               , FAdjunction(..)
               , law_FAdjunction_restrict
               , AdjoiningSemicomonad(..)
               -- , law_AdjoiningSemicomonad_comm
               , AdjoiningComonad(..)
               , Semicomonad1(..)
               , law_Semicomonad1_comm
               , law_Semicomonad1_comm'
               , Comonad1(..)
               , law_Comonad1_id
               , law_Comonad1_id'
               -- , law_Comonad1_apply
               ) where

import Prelude hiding ( Foldable(..)
                      , Functor(..)
                      , Applicative(..)
                      , Traversable(..)
                      , Monad(..)
                      )

import Data.Constraint
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
                        -- TODO: prove the ones below
                        , Morphism (FunMor f m), MorCat (FunMor f m) ~ Cod f
                        , Morphism (FunMor f n), MorCat (FunMor f n) ~ Cod f
                        , Morphism (FunMor f mn), MorCat (FunMor f mn) ~ Cod f
                        , Cod f (f a)
                        ) => f b `m` c -> f a `n` b -> Law (f a) (f c)
law_Semicomonad_comm f g =
    (extend f `MCompose` extend g) `equals` (extend (f `MCompose` extend g))

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



--------------------------------------------------------------------------------



-- | AdjointFunctors

-- Adjoint functors, but for a category of functors. Thus the adjoint
-- functors are actually natural transformations for our 'Functor'
-- class.

-- In Milewski's notation <https://bartoszmilewski.com/2016/04/18/adjunctions/>:
--     category C
--     category D
--     functor L: D -> C
--     functor R: C -> D
--     law: idD -> R . L
--     law: L . R -> idC

--     category g
--     category f
--     functor restrict: f -> g
--     functor expand: g -> f
--     law: idf -> expand . restrict
--     law: restrict . expand -> idg

-- | FAdjunction
class (Functor f, Functor g, Dom g ~ Dom f, Cod g ~ Cod f)
        => FAdjunction g f where
    -- | 'restrict' is the left adjoint, 'expand' is the right adjoint
    -- | restrict . expand = id
    -- (Note that VectorSpace provides a Default.)
    restrict :: (Default a, Dom f a) => f a -> g a
    expand :: (Default a, Dom f a) => g a -> f a

-- restrict . expand = id
law_FAdjunction_restrict :: forall f g a.
                              ( FAdjunction g f
                              , Dom f a
                              , Default a
                              , Eq (g a), Show (g a)
                              ) => Proxy f -> g a -> QC.Property
law_FAdjunction_restrict _ xs =
    (restrict . (expand :: g a -> f a)) xs QC.=== xs
                                        
-- | Every functor category is adjoint to itself
instance Functor f => FAdjunction f f where
    restrict = id
    expand = id



class (FAdjunction g f, Cod g ~ Dom g) => AdjoiningSemicomonad g f where
    extendA :: (Dom f a, Dom f b, Morphism m, MorCat m ~ Dom f, n ~ FunMor f m)
               => g a `m` b -> f a `n` f b
    duplicateA :: Dom f a => f a -> f (g a)
    default duplicateA :: ( Dom f a
                          , Dom f (g a) -- TODO: prove this instead
                          , FunMor f (MId (Dom f)) ~ (->))
                          => f a -> f (g a)
    duplicateA = extendA MId

-- | Every Semicomonad is an AdjoiningSemicomonad with itself
instance Semicomonad f => AdjoiningSemicomonad f f where
    extendA = extend
    duplicateA = duplicate

-- extend f . extend g = extend (f . extend g)

-- This law does not hold if 'restrict' loses information. This
-- corresponds to composing two stencils, resulting in a larger
-- stencil, and that larger stencil might not fit into the left
-- adjoint functor any more.

-- law_AdjoiningSemicomonad_comm ::
--     forall f g m n mn p a b c.
--        ( AdjoiningSemicomonad g f
--        -- , Cod g ~ Dom g
--        , Dom f a, Dom f b, Dom f c
--        , Morphism m, MorCat m ~ Dom f
--        , Morphism n, MorCat n ~ Dom f
--        , mn ~ MCompose m (FunMor g n) (g b)
--        , p ~ FunMor f m
--        , q ~ FunMor f n
--        , r ~ FunMor (MCompose m q _) n
--        , Eq (f c), Show (f c)
--        -- TODO: prove the ones below
--        , Cod f (f a), Cod f (f b), Cod f (f c)
--        , Morphism (FunMor f m), MorCat (FunMor f m) ~ Cod f
--        , Morphism (FunMor f n), MorCat (FunMor f n) ~ Cod f
--        , Morphism (FunMor f mn), MorCat (FunMor f mn) ~ Cod f
--        , Morphism (FunMor g m), MorCat (FunMor g m) ~ Cod g
--        , Morphism (FunMor g n), MorCat (FunMor g n) ~ Cod g
--        , Morphism (FunMor g mn), MorCat (FunMor g mn) ~ Cod g
--        -- , AdjoiningSemicomonad g g
--        ) => g b `m` c -> g a `n` b -> f a -> QC.Property
-- law_AdjoiningSemicomonad_comm f g xs =
--     -- (extendA f `MCompose` extendA g) `chase` xs QC.===
--     --     (extendA (f `MCompose` extendA g)) `chase` xs
--     ((extendA f :: f b `p` f c) `MCompose`
--      (extendA g :: f a `q` f b)) `chase` xs QC.===
--     (extendA (f `MCompose` extendA g :: f a `q` f b)) `chase` xs
--     let l1 = extendA g :: f a `q` f b
--         l2 = extendA f :: f b `p` f c
--         l = l2 `MCompose` l1 :: MCompose p q (f b) (f a) (f c)
--         r1 = extendA g :: f a `q` f b
--         r2 = f `MCompose` r1 :: MCompose m q (fg b) (f a) c
--         r = extendA r2 :: f a `r` f c

-- | AdjoiningComonad
class AdjoiningSemicomonad g f => AdjoiningComonad g f where
    extractA :: Dom f a => f a -> a
    extractA' :: Dom f a => g a -> a

-- | AdjoiningSemicomonadStore
-- | AdjoiningComonadStore



--------------------------------------------------------------------------------



-- | Semicomonad (also called 'Extend'; see package "semigroupoids")
class Functor f => Semicomonad1 f where
    -- (=<=) :: ( Dom f a, Dom f b, Dom f c
    --          , Morphism m, MorCat m ~ Dom f
    --          , Morphism n, MorCat n ~ Dom f
    --          , p ~ FunMor f m
    --          , p ~ FunMor f n
    --          ) => f b `m` c -> f a `n` b -> f a `p` c
    extend1 :: (Dom f a, Dom f b, Morphism m, MorCat m ~ Dom f, n ~ FunMor f m)
               => f a `m` b -> f a `n` f b
    extend1' :: (Dom f a, Dom f b) => (f a -> b) -> f a -> f b
    duplicate1' :: forall m n a.
                   ( Morphism m, MorCat m ~ Dom f
                   , Dom f a
                   , Cod f ~ Dom f
                   , n ~ FunMor f m
                   ) => Proxy m -> f a `n` f (f a)
    default duplicate1' :: forall m n a.
                           ( Morphism m, MorCat m ~ Dom f
                           , Dom f a
                           , Cod f ~ Dom f
                           , n ~ FunMor f (MId (Dom f))
                           ) => Proxy m -> f a `n` f (f a)
    duplicate1' _ = extend1 MId
                    \\ (proveFunCod (Proxy @f) :: (Dom f a :- Cod f (f a)))
    duplicate1 :: ( Cod f ~ Dom f
                  , Dom f a
                  ) => f a -> f (f a)
    default duplicate1 :: ( Morphism (->), MorCat (->) ~ Dom f
                          , Cod f ~ Dom f
                          , Dom f a
                          , (->) ~ FunMor f (->)
                          ) => f a -> f (f a)
    duplicate1 = duplicate1' (Proxy @(->))

-- extend f . extend g = extend (f . extend g)
law_Semicomonad1_comm :: ( Semicomonad1 f
                         , Cod f ~ Dom f
                         , Morphism m, MorCat m ~ Dom f
                         , Morphism n, MorCat n ~ Dom f
                         , mn ~ MCompose m (FunMor f n) (f b)
                         , Dom f a, Dom f b, Dom f c
                         -- TODO: prove the ones below
                         , Morphism (FunMor f m), MorCat (FunMor f m) ~ Cod f
                         , Morphism (FunMor f n), MorCat (FunMor f n) ~ Cod f
                         , Morphism (FunMor f mn), MorCat (FunMor f mn) ~ Cod f
                         , Cod f (f a)
                         ) => f b `m` c -> f a `n` b -> Law (f a) (f c)
law_Semicomonad1_comm f g =
    (extend1 f `MCompose` extend1 g) `equals` (extend1 (f `MCompose` extend1 g))

law_Semicomonad1_comm' :: ( Semicomonad1 f
                          , Morphism (->)
                          , k ~ MorCat (->)
                          , Dom f a, Dom f b, Dom f c
                          -- , k a, k b, k c
                          -- TODO: prove the ones below
                          -- , Cod f (f a), Cod f (f b), Cod f (f c)
                          , k (f a) --, k (f b), k (f c)
                          ) => (f b -> c) -> (f a -> b) -> Law (f a) (f c)
law_Semicomonad1_comm' f g =
    (extend1' f `MCompose` extend1' g) `equals`
       (extend1' (chase (f `MCompose` extend1' g)))



-- | Comonad
class Semicomonad1 f => Comonad1 f where
    extract1' :: ( Morphism m, MorCat m ~ Dom f
                 , Dom f a
                 , n ~ FunMor f m
                 ) => Proxy m -> f a `n` a
    extract1 :: Dom f a => f a -> a
    default extract1 :: ( Morphism (->), MorCat (->) ~ Dom f
                        , Dom f a
                        , (->) ~ FunMor f (->)
                        ) => f a -> a
    extract1 = extract1' (Proxy @(->))

-- extend extract = id
law_Comonad1_id :: forall f m n p a.
                   ( Comonad1 f
                   , Cod f ~ Dom f
                   , Morphism m, MorCat m ~ Dom f
                   , Dom f a
                   -- TODO: prove the ones below
                   , n ~ FunMor f m
                   , Morphism n, MorCat n ~ Cod f
                   , p ~ FunMor f n
                   , Morphism p, MorCat p ~ Cod f
                   ) => Proxy m -> Law (f a) (f a)
law_Comonad1_id _ = extend1 (extract1' (Proxy @m)) `equals` MId
                    \\ (proveFunCod (Proxy @f) :: (Dom f a :- Cod f (f a)))

law_Comonad1_id' :: forall f a.
                    ( Comonad1 f
                    , Morphism (->), MorCat (->) ~ Cod f
                    , Dom f a
                    ) => Law (f a) (f a)
law_Comonad1_id' = extend1' extract1 `equals` MId
                   \\ (proveFunCod (Proxy @f) :: (Dom f a :- Cod f (f a)))

-- extract . extend f = f
