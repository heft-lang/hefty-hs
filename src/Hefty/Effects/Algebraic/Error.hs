module Hefty.Effects.Algebraic.Error where

import Hefty
import Hefty.Algebraic

newtype Error e k = Error e
  deriving Functor

err :: (Algebraic eff, In eff (Error e) f) => e -> eff f a
err e = lift $ const $ Error e

hErr :: Functor f
     => Handler (Error e) a f (Either e a)
hErr = Handler
  (return . Right)
  (\ (Error e) -> return $ Left e)
