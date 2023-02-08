{-# LANGUAGE LambdaCase #-}
module Hefty.Effects.HigherOrder.Except where

import Hefty
import Hefty.Effects.Algebraic.Abort

data Except m a where
  Catch :: m a -> m a -> Except m a
  Throw :: Except m a

instance HFunctor Except where
  hmap f (Catch m1 m2) = Catch (f m1) (f m2)
  hmap _ Throw = Throw

catch :: Except << h
      => Hefty h a -> Hefty h a -> Hefty h a
catch m1 m2 = Op (injH $ Catch m1 m2) Return

throw :: ( HFunctor h
         , Except << h )
      => Hefty h a
throw = Op (injH Throw) Return


-- elaboration into Abort

eExcept :: forall f. (Functor f, Abort < f) => Elab Except f
eExcept = Alg $ \op k -> case op of
  Catch m1 m2 -> do
    v <- hup (handle hAbort) m1
    case v of
      Just x -> k x
      Nothing -> m2 >>= k
  Throw -> abort