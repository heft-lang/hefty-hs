{-# LANGUAGE LambdaCase #-}
module Hefty.Elab where

import Hefty.Free
import Hefty.Hefty
import Data.Kind (Type)

type Elab h f = Alg h (Freer f)

elaborate :: (HFunctor h) => Elab h f -> Hefty h a -> Freer f a
elaborate = foldH return

type Lift :: (Type -> Type) -> (Type -> Type) -> Type -> Type
newtype Lift f m a = Lift (f a)

instance HFunctor (Lift f) where
  hmap _ (Lift op) = Lift op

eLift :: forall f g. f < g => Elab (Lift f) g
eLift = Alg $ \case Lift op -> Do (inj op)

liftH :: Lift f << h => f a -> Hefty h a
liftH op = Op (injH $ Lift op) Return
