module Hefty.Effects.Algebraic.Error where

import Hefty
import Hefty.Algebraic

newtype Error e a where
  Error :: e -> Error e a

err :: In eff (Error e) f => e -> eff f a
err e = lift $ Error e

hErr :: Functor f
     => Handler (Error e) a f (Either e a)
hErr = Handler
  (return . Right)
  (\ (Error e) _ -> return $ Left e)