module Development.Hake.OrderedConfVar where

import Distribution.PackageDescription (ConfVar(..))

data OrderedConfVar = OrderedConfVar ConfVar deriving Eq

instance Ord OrderedConfVar where
  OrderedConfVar lv `compare` OrderedConfVar rv =
    case (lv, rv) of
      (OS     x, OS     y) -> compare x y
      (OS     _,        _) -> LT
      (Arch   x, Arch   y) -> compare x y
      (Arch   _,        _) -> LT
      (Flag   x, Flag   y) -> compare x y
      (Flag   _,        _) -> LT
      (Impl x _, Impl y _) -> compare x y
      (Impl _ _,        _) -> LT
