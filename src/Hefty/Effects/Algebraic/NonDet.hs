module Hefty.Effects.Free.NonDet where


import Hefty
import Hefty.Algebraic

newtype NonDet k = Or (Bool -> k)
  deriving Functor

or :: In eff NonDet h => eff h a -> eff h a -> eff h a
or m1 m2 = lift $ \ r -> Or $ \ b -> if b then m1 >>= r else m2 >>= r

hNonDet :: Functor f
        => Handler NonDet a f [a]
hNonDet = Handler
  (\ x -> return [x])
  (\ (Or k) -> do
      xs <- k True
      ys <- k False
      return (xs ++ ys))

runNonDet :: Functor f => Free (NonDet + f) a -> Free f [a]
runNonDet = handle hNonDet


-- type Tactic = NonDet + Abort + Nop

-- falso :: Tactic < f => Free f a
-- falso = Do $ inj @Tactic $ R $ L $ Abort

-- disj :: Tactic < f => Free f a -> Free f a -> Free f a
-- disj m1 m2 = Do $ inj @Tactic $ L $ Or $ \ b -> if b then m1 else m2

-- hTactic :: Functor f => Free (Tactic + f) a -> Free f [a]
-- hTactic = handle $ Handler
--   (\ x -> return [x])
--   (\ x -> case x of
--       L (Or k) -> do
--         xs <- k True
--         ys <- k False
--         return (xs ++ ys)
--       R (L Abort) -> return []
--       R (R op) -> case op of)
