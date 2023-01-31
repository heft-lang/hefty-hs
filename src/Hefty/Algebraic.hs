{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE QuantifiedConstraints #-}
module Hefty.Algebraic where
import Data.Kind
import Hefty.Elab ( Lift, liftH )
import Hefty.Free ( type (<), Free(..), inj )
import Hefty.Hefty ( type (<<), Hefty )

class Algebraic (eff :: k -> Type -> Type) where
  type In eff (f :: Type -> Type) (h :: k) :: Constraint
  lift :: In eff f h => ((a -> eff h a) -> f (eff h a)) -> eff h a

instance Algebraic Free where
  type In Free f h = f < h
  lift op = Do (inj (op Pure))

instance Algebraic Hefty where
  type In Hefty f h = Lift f << h
  lift = liftH