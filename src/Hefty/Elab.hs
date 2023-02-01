{-# LANGUAGE LambdaCase #-}
module Hefty.Elab where

import Hefty.Free
import Hefty.Hefty
import Data.Kind (Type)

type Elab h f = Alg h (Freer f)

elaborate :: (HFunctor h) => Elab h f -> Hefty h a -> Freer f a
elaborate = foldH return

type Lift :: (Type -> Type) -> (Type -> Type) -> Type -> Type
data Lift f h k = forall c. Lift (f c, c -> k)

deriving instance Functor (Lift f h)

instance Functor f => HFunctor (Lift f) where
  hmap _ (Lift x) = Lift x

eLift :: forall f g. f < g => Elab (Lift f) g
eLift = Alg $ \case Lift (op, k) -> Do (inj op) k

liftH0 :: forall f h.
          Lift f << h
       => (Hefty h () -> f (Hefty h ())) -> Hefty h ()
liftH0 f = Op $ injH $ Lift (f (Return ()), id)

liftH :: Lift f << h => f a -> Hefty h a
liftH op = Op $ injH $ Lift (op, Return)
