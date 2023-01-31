module Hefty.Effects.Algebraic.Reader where

import Hefty
import Hefty.Algebraic

newtype Reader r k = Reader (r -> k)
  deriving Functor

reader :: In eff (Reader r) h => eff h r
reader = lift Reader


---------------
--- HANDLER ---
---------------

hReader :: Functor f
        => Handler_ (Reader r) a r f a
hReader = Handler_ {
    ret_ = \ x _ -> return x
  , hdl_ = \ f r -> case f of
      Reader k -> k r r
  }
