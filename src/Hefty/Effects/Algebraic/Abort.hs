module Hefty.Effects.Algebraic.Abort where

import Hefty
import Hefty.Algebraic

data Abort k = Abort
  deriving Functor

abort :: (Algebraic eff, In eff Abort f) => eff f a
abort = lift $ const Abort

hAbort :: Functor f => Handler Abort a f (Maybe a)
hAbort = Handler
  (return . Just)
  (\ _ -> return Nothing)

runAbort :: Functor f => Free (Abort + f) a -> Free f (Maybe a)
runAbort = handle hAbort