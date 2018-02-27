{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module HaskSpec where

import Test.QuickCheck
import Test.QuickCheck.Poly

import Category



-- prop_Hask_embed :: Fun A B -> A -> Property
-- prop_Hask_embed (Fn f) x = (discretize . chase) f x === f x
-- 
-- prop_Hask_project :: Fun A B -> A -> Property
-- prop_Hask_project (Fn f) x =
--     (chase . discretize @(->) . chase . discretize @(->)) f x ===
--     (chase . discretize @(->)) f x
