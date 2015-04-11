module Development.Hake.TraversableCondition where

import Distribution.PackageDescription (Condition(..))
import Data.Monoid

newtype TraversableCondition a = TraversableCondition {unTC :: Condition a}

instance Functor TraversableCondition where
  f `fmap` TraversableCondition a = TraversableCondition (g a) where
    g (Var c) = Var (f c)
    g (Lit c) = Lit c
    g (CNot c) = CNot (g c)
    g (COr c d) = COr (g c) (g d)
    g (CAnd c d) = CAnd (g c) (g d)

instance Foldable TraversableCondition where
  f `foldMap` TraversableCondition a = g a where
    g (Var c) = f c
    g (Lit _) = mempty
    g (CNot c) = g c
    g (COr c d) = g c <> g d
    g (CAnd c d) = g c <> g d

instance Traversable TraversableCondition where
  f `traverse` TraversableCondition a = TraversableCondition <$> g a where
    g (Var c) = Var <$> f c
    g (Lit c) = pure $ Lit c
    g (CNot c) = CNot <$> g c
    g (COr c d) = COr <$> g c <*> g d
    g (CAnd c d) = CAnd <$> g c <*> g d
