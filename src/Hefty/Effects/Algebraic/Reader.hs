{-# LANGUAGE GADTs #-}
module Hefty.Effects.Algebraic.Reader where

import Hefty
import Hefty.Algebraic

data Reader r a where
  Ask :: Reader r r

reader :: In eff (Reader r) h => eff h r
reader = lift Ask


---------------
--- HANDLER ---
---------------

hReader :: Handler_ (Reader r) a r f a
hReader = Handler_ {
    ret_ = \ x _ -> return x
  , hdl_ = \ op k r -> case op of
      Ask -> k r r
  }
