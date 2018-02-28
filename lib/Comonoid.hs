module Comonoid ( Cosemigroup(..)
                , Comonoid(..)
                , Counter(..)
                , CountDown(..)
                , Counted(..)
                , Forever(..)
                ) where



import Data.Monoid as M
import Data.Proxy



class Cosemigroup w where
    split1 :: w -> Maybe (w, w)
    default split1 :: Comonoid w => w -> Maybe (w, w)
    split1 = Just . split

class Cosemigroup w => Comonoid w where
    -- In a 'Comonad', this is 'extract'
    -- destroy :: w -> ()
    counit :: w -> Bool
    default counit :: Eq w => w -> Bool
    counit w = split w == (w, w)
    -- In a 'Comonad', this is 'duplicate'
    -- We could have both 'lsplit' and 'rsplit', akin to 'foldl' and 'foldr'
    split :: w -> (w, w)
    split' :: w -> Maybe (w, w)
    split' w = if counit w then Nothing else Just (split w)


-- Main rules:
-- - Don't define a Cosemigroup that is never splittable
-- - Don't define a Cosemigroup trivially based on a Monoid

instance Cosemigroup ()
instance Comonoid () where
    counit () = True
    split () = ((), ())

instance Cosemigroup (Proxy a)
instance Comonoid (Proxy a) where
    counit Proxy = True
    split Proxy = (Proxy, Proxy)

instance Cosemigroup (Maybe a)
instance Comonoid (Maybe a) where
    counit Nothing = True
    counit (Just x) = False
    split Nothing = (Nothing, Nothing)
    split (Just x) = (Just x, Nothing)

instance Monoid a => Cosemigroup (Either a b)
instance Monoid a => Comonoid (Either a b) where
    counit (Left x) = True
    counit (Right y) = False
    split xs = (xs, Left mempty)

instance Cosemigroup [a]
instance Comonoid [a] where
    counit [] = True
    counit (x:xs) = False
    split [] = ([], [])
    split (x:xs) = ([x], xs)



instance (Num a, Ord a) => Cosemigroup (M.Sum a)
instance (Num a, Ord a) => Comonoid (M.Sum a) where
    split (M.Sum x) = if | x > 0 -> (M.Sum 1, M.Sum (x - 1))
                         | x < 0 -> (M.Sum (-1), M.Sum (x + 1))
                         | otherwise -> (M.Sum 0, M.Sum x)



newtype Counter = Counter { getCounter :: Int }
    deriving (Eq, Ord, Read, Show)
instance Cosemigroup Counter
instance Comonoid Counter where
    counit (Counter n) = False
    split (Counter n) = (Counter n, Counter (n + 1))

newtype CountDown = CountDown { getCountDown :: Int }
    deriving (Eq, Ord, Read, Show)
instance Cosemigroup CountDown
instance Comonoid CountDown where
    counit (CountDown n) = n == 0
    split (CountDown n) = (CountDown n, CountDown (n - 1))

instance (Comonoid a, Comonoid b) => Cosemigroup (a, b)
instance (Comonoid a, Comonoid b) => Comonoid (a, b) where
    counit (x, y) = counit y
    split (x, y) = let (x1, x2) = split x
                       (y1, y2) = split y
                   in ((x1, y1), (x2, y2))

data Counted a = Counted { getCount :: Int, getCounted :: a }
                 deriving (Eq, Ord, Read, Show)
instance Comonoid a => Cosemigroup (Counted a)
instance Comonoid a => Comonoid (Counted a) where
    counit (Counted n x) = n == 0
    split (Counted n x) = bimap (Counted 1) (Counted (n - 1)) (split x)

newtype Forever a = Forever { getForever :: a }
    deriving (Eq, Ord, Read, Show)
instance Comonoid a => Cosemigroup (Forever a)
instance Comonoid a => Comonoid (Forever a) where
    counit (Forever x) = False
    split (Forever x) = bimap Forever Forever (split x)

-- This is Data.List.NonEmpty.NonEmpty
-- data FromList a = FromList { getFromList :: a, getRemainingList :: [a] }
--     deriving (Eq, Ord, Read, Show)
-- instance Cosemigroup (FromList a) where
--     split1 (FromList x []) = Nothing
--     split1 (FromList x (y:ys)) = Just (FromList x [], FromList y ys)



data Tree a = Leaf a | Branch (Tree a) (Tree a)
              deriving (Eq, Ord, Read, Show)
instance Cosemigroup (Tree a) where
    split1 (Leaf x) = Nothing
    split1 (Branch l r) = Just (l, r)



bimap :: (a -> s) -> (b -> t) -> (a, b) -> (s, t)
bimap f g (x, y) = (f x, g y)
