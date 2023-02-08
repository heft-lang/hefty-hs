{-# LANGUAGE LambdaCase #-}
module Hefty.Effects.HigherOrder.Local where

import Hefty

import Hefty.Effects.Algebraic.Reader

data Local r m a where
  Local :: (r -> r) -> m a -> Local r m a

instance HFunctor (Local r) where
  hmap f (Local g m) = Local g (f m)


-------------------
--- ELABORATION ---
-------------------

eLocal :: forall r f.
          ( Functor f
          , Reader r < f )
       => Elab (Local r) f
eLocal = Alg $ \op k -> case op of
  Local g m -> do
    (r :: r) <- reader
    v <- hup (flip (handle_ hReader) (g r) . fmap Id) m
    k (unId v)


