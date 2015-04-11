module Development.Hake.OrderedConfVar where

import Distribution.PackageDescription (ConfVar(..))

newtype OrderedConfVar = OrderedConfVar ConfVar deriving Eq

instance Ord OrderedConfVar where
  l `compare` r | l == r = EQ
  OrderedConfVar l `compare` OrderedConfVar r = case (l, r) of
    (OS     x, OS     y) -> compare x y
    (OS     _,        _) -> LT
    (Arch   x, Arch   y) -> compare x y
    (Arch   _,        _) -> LT
    (Flag   x, Flag   y) -> compare x y
    (Flag   _,        _) -> LT
    (Impl x _, Impl y _) -> compare x y
    (Impl _ _,        _) -> LT
