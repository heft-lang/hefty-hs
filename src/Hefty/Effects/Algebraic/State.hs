{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE GADTs #-}
module Hefty.Effects.Algebraic.State where

import Hefty
import Hefty.Algebraic

data State s a where
  Put :: s -> State s ()
  Get :: State s s

put :: In eff (State s) h => s -> eff h ()
put s = lift (Put s)

get :: In eff (State s) h => eff h s
get = lift Get

hState :: Functor f'
       => Handler_ (State s) a s f' (s, a)
hState = Handler_
  (\ x s -> return (s, x))
  \ op k s -> case op of
      Put s' -> k () s'
      Get    -> k s s