module Hefty.Effects.Algebraic.State where

import Hefty
import Hefty.Algebraic

data State s k = Put s k | Get (s -> k)
  deriving Functor

put :: (Algebraic eff, In eff (State s) h) => s -> eff h ()
put s = lift $ \k -> Put s (k ())

get :: (Algebraic eff, In eff (State s) h) => eff h s
get = lift Get

hState :: Functor f'
       => Handler_ (State s) a s f' (s, a)
hState = Handler_
  (\ x s -> return (s, x))
  (\ op s -> case op of
      (Put s' k) -> k s'
      (Get k)   -> k s s)

-- hState :: Functor f => s -> Free (State s + f) a -> Free f (a, s)
-- hState s (Pure x) = return (x, s)
-- hState _ (Do (L (Put s k))) = hState s k
-- hState s (Do (L (Get k))) = hState s (k s)
-- hState s (Do (R op)) = Do (fmap (hState s) op)

