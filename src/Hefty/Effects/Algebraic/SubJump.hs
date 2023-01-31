{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
module Hefty.Effects.Algebraic.SubJump where

import Hefty
import Hefty.Algebraic

data SubJump ref k
  = forall t. Sub (Either (ref t) t -> k)
  | forall t. Jump (ref t) t

deriving instance forall ref. Functor (SubJump ref)

sub :: In eff (SubJump ref) f
    => (ref t -> eff f a)
    -> (t -> eff f a)
    -> eff f a
sub sc k = lift $ const $ Sub \case
  Left  r -> sc r
  Right x -> k x

jump :: In eff (SubJump ref) f
     => ref t -> t -> eff f a
jump r x = lift $ const $ Jump r x

newtype Cont f b a = Cont { cont :: a -> Free f b }

hSubJump :: Functor f
         => Free (SubJump (Cont f a) + f) a
         -> Free f a
hSubJump = fmap (fmap unId) . handle $ Handler (pure . Id) \case
  Sub k -> k (Left $ Cont $ fmap unId <$> k . Right)
  Jump r x -> Id <$> cont r x