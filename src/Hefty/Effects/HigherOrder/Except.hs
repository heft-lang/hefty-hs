{-# LANGUAGE LambdaCase #-}
module Hefty.Effects.HigherOrder.Except where

import Hefty
import Hefty.Effects.Algebraic.Abort

data Except f k
  = forall a. Catch (f a) (f a) (a -> k)
  | Throw

deriving instance forall f. Functor (Except f)

instance HFunctor Except where
  hmap f (Catch m1 m2 k) = Catch (f m1) (f m2) k
  hmap _ Throw = Throw

catch :: Except << h
      => Hefty h a -> Hefty h a -> Hefty h a
catch m1 m2 = Op $ injH $ Catch m1 m2 Return

throw :: ( HFunctor h
         , Except << h )
      => Hefty h a
throw = Op (injH Throw)


-- elaboration into Abort

eExcept :: forall f. (Functor f, Abort < f) => Elab Except f
eExcept = Alg $ \case
  Catch m1 m2 k -> do
    v <- hup (handle hAbort) m1
    case v of
      Just x -> k x
      Nothing -> m2 >>= k
  Throw -> abort