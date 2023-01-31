module Hefty.Effects.Algebraic.Abort where

import Hefty

data Abort k = Abort
  deriving Functor

abort :: Abort < f => Free f a
abort = Do $ inj Abort

abortH :: Lift Abort << h => Hefty h a
abortH = liftH $ const Abort

hAbort :: Functor f => Handler Abort a f (Maybe a)
hAbort = Handler
  (return . Just)
  (\ _ -> return Nothing)

runAbort :: Functor f => Free (Abort + f) a -> Free f (Maybe a)
runAbort = handle hAbort