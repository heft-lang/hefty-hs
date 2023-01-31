{-# LANGUAGE LambdaCase #-}
module Hefty.Elab where

import Hefty.Free
import Hefty.Hefty
import Data.Kind (Type)

type Elab h f = Alg h (Free f)

elaborate :: (HFunctor h, Functor f)
          => Elab h f -> Hefty h a -> Free f a
elaborate = foldH return

type Lift :: (Type -> Type) -> (Type -> Type) -> Type -> Type
newtype Lift f h k = Lift (f k)
  deriving Functor

instance Functor f => HFunctor (Lift f) where
  hmap _ (Lift x) = Lift x

eLift :: forall f g. f < g => Elab (Lift f) g
eLift = Alg $ \case Lift x -> Do $ inj x

liftH0 :: forall f h.
          Lift f << h
       => (Hefty h () -> f (Hefty h ())) -> Hefty h ()
liftH0 f = Op $ injH $ Lift $ f (Return ())

liftH :: Lift f << h
      => ((a -> Hefty h a) -> f (Hefty h a)) -> Hefty h a
liftH f = Op $ injH $ Lift $ f Return
