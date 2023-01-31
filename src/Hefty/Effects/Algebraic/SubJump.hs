{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
module Hefty.Effects.Algebraic.SubJump where

import Hefty

data SubJump ref k
  = forall t. Sub (Either (ref t) t -> k)
  | forall t. Jump (ref t) t

deriving instance forall ref. Functor (SubJump ref)

sub :: SubJump ref < f
    => (ref t -> Free f a)
    -> (t -> Free f a)
    -> Free f a
sub sc k = Do $ inj $ Sub \case
  Left  r -> sc r
  Right x -> k x

jump :: SubJump ref < f
     => ref t -> t -> Free f a
jump r x = Do $ inj $ Jump r x

newtype Cont f b a = Cont { cont :: a -> Free f b }

hSubJump :: Functor f
         => Free (SubJump (Cont f a) + f) a
         -> Free f a
hSubJump = fmap (fmap unId) . handle $ Handler (pure . Id) \case
  Sub k -> k (Left $ Cont $ fmap unId <$> k . Right)
  Jump r x -> Id <$> cont r x