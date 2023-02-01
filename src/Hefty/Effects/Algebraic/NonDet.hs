{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE GADTs #-}
module Hefty.Effects.Free.NonDet where


import Hefty
import Hefty.Algebraic

data NonDet a where
  Or :: NonDet Bool

or :: In eff NonDet h => eff h a -> eff h a -> eff h a
or m1 m2 = lift Or >>= \b -> if b then m1 else m2 

hNonDet :: Handler NonDet a f [a]
hNonDet = Handler
  (\ x -> return [x])
  \ op k -> case op of
    Or -> do
      xs <- k True
      ys <- k False
      return (xs ++ ys)

runNonDet :: Freer (NonDet + f) a -> Freer f [a]
runNonDet = handle hNonDet