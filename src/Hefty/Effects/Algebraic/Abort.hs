{-# LANGUAGE BlockArguments #-}
module Hefty.Effects.Algebraic.Abort where

import Hefty
import Hefty.Algebraic

data Abort a where
  Abort :: Abort a

abort :: In eff Abort f => eff f a
abort = lift Abort

hAbort :: Handler Abort a f (Maybe a)
hAbort = Handler
  (return . Just)
  \ op _ -> case op of
    Abort -> return Nothing

runAbort :: Freer (Abort + f) a -> Freer f (Maybe a)
runAbort = handle hAbort