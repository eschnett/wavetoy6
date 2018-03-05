{-# LANGUAGE TypeApplications #-}

{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module CategorySpec where

import Test.QuickCheck
import Test.QuickCheck.Poly

import Category
import Hask



prop_MId_id :: A -> Property
prop_MId_id x = MId @Hask `chase` x === x

prop_MCompose_compose :: Fun B C -> Fun A B -> A -> Property
prop_MCompose_compose (Fn f) (Fn g) x = MCompose f g `chase` x === (f . g) x

prop_MCompose_left_id :: Fun A B -> A -> Property
prop_MCompose_left_id (Fn f) x = (MId `MCompose` f) `chase` x === f `chase` x

prop_MCompose_right_id :: Fun A B -> A -> Property
prop_MCompose_right_id (Fn f) x = (f `MCompose` MId) `chase` x === f `chase` x

prop_MCompose_assoc :: Fun C A -> Fun B C -> Fun A B -> A -> Property
prop_MCompose_assoc (Fn f) (Fn g) (Fn h) x =
    ((f `MCompose` g) `MCompose` h) `chase` x ===
    (f `MCompose` (g `MCompose` h)) `chase` x
