{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ExplicitNamespaces #-}
module Hefty.Algebraic where
import Data.Kind
import Hefty.Elab ( Lift, liftH )
import Hefty.Free ( type (<), Free(..), inj )
import Hefty.Hefty ( type (<<), Hefty, HFunctor )

class Monad (eff h) => In (eff :: k -> Type -> Type) (f :: Type -> Type) (h :: k) where
  lift :: ((a -> eff h a) -> f (eff h a)) -> eff h a

instance (Functor h, f < h) => In Free f h where
  lift op = Do (inj (op Pure))

instance (HFunctor h, Lift f << h) => In Hefty f h where
  lift = liftH