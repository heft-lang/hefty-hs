{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GADTs #-}
module Hefty.Effects.Algebraic.SubJump where

import Hefty
import Hefty.Algebraic

data SubJump ref a where
  Sub :: SubJump ref (Either (ref t) t)
  Jump :: ref t -> t -> SubJump ref a

-- deriving instance forall ref. Functor (SubJump ref)

sub :: In eff (SubJump ref) f
    => (ref t -> eff f a)
    -> (t -> eff f a)
    -> eff f a
sub sc k = lift Sub >>= \case
  Left  r -> sc r
  Right x -> k x

jump :: In eff (SubJump ref) f
     => ref t -> t -> eff f a
jump r x = lift (Jump r x)

newtype Cont f b a = Cont { cont :: a -> Freer f b }

hSubJump :: Functor f
         => Freer (SubJump (Cont f a) + f) a
         -> Freer f a
hSubJump = handle $ Handler pure \op k -> case op of
  Sub -> k (Left $ Cont $ k . Right)
  Jump r x -> cont r x