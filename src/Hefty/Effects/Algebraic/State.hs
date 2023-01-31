module Hefty.Effects.Algebraic.State where

import Hefty

data State s k = Put s k | Get (s -> k)
  deriving Functor

put :: State s < f => s -> Free f ()
put s = Do $ inj $ Put s $ Pure ()

get :: State s < f => Free f s
get = Do $ inj $ Get Pure

putH :: Lift (State s) << h => s -> Hefty h ()
putH s = liftH0 $ Put s

getH :: Lift (State s) << h => Hefty h s
getH = liftH Get

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

