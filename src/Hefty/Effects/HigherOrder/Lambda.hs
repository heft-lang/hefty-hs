{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GADTs #-}
module Hefty.Effects.HigherOrder.Lambda where

import Hefty
import Unsafe.Coerce

import Hefty.Effects.Algebraic.State

data Lambda c fun m a where
  Lambda :: (c t1 -> m t2) -> Lambda c fun m (fun (c t1) t2)
  Var :: c t -> Lambda c fun m t
  Apply :: fun (c t1) t2 -> m t1 -> Lambda c fun m t2

instance HFunctor (Lambda c fun) where
  hmap f (Lambda body) = Lambda (f . body)
  hmap _ (Var x) = Var x
  hmap f (Apply fun arg) = Apply fun (f arg)

lambda :: forall fun c h t1 t2.
          Lambda c fun << h
       => (c t1 -> Hefty h t2)
       -> Hefty h (fun (c t1) t2)
lambda body = Op (injH $ Lambda body) Return

var :: forall fun c h t. Lambda c fun << h => c t -> Hefty h t
var x = Op (injH @(Lambda c fun) $ Var x) Return

apply :: forall fun c h t1 t2.
         Lambda c fun << h
      => fun (c t1) t2 -> Hefty h t1 -> Hefty h t2
apply fun arg = Op (injH $ Apply fun arg) Return


-- call-by-value interpretation

newtype Fun f t1 t2 = Fun { app :: t1 -> Freer f t2 }

eLambdaCBV :: forall f.
              Functor f
           => Elab (Lambda Id (Fun f)) f
eLambdaCBV = Alg $ \op k -> case op of
  Lambda body -> k (Fun body)
  Var x -> k (unId x)
  Apply fun arg -> do
    v <- arg
    app fun (Id v) >>= k
           

-- call-by-name interpretation

eLambdaCBN :: forall f.
              Functor f
           => Elab (Lambda (Freer f) (Fun f)) f
eLambdaCBN = Alg $ \op k -> case op of
  Lambda body -> k (Fun body)
  Var x -> x >>= k
  Apply fun arg -> app fun arg >>= k


-- call-by-need interpretation

newtype Thunk f a = Thunk { force :: (Int, Freer f a) }

data Pack = forall v. Pack (Maybe v)

update :: Thunk f v -> v -> [Pack] -> [Pack]
update _ _ [] = undefined
update (Thunk (0, _)) v (_:p) = Pack (Just v) : p
update (Thunk (i, m)) v (t:p) | i > 0 = t:update (Thunk (i-1,m)) v p
                              | otherwise = undefined

insert :: Freer f v -> [Pack] -> (Thunk f v, [Pack])
insert m p = (Thunk (length p, m), p ++ [Pack Nothing])

eLambdaCBN' :: forall f.
               ( Functor f
               , State [Pack] < f )
            => Elab (Lambda (Thunk f) (Fun f)) f
eLambdaCBN' = Alg $ \op k -> case op of
  Lambda body -> k (Fun body)
  Var x -> do
    (st :: [Pack]) <- get
    let (i, m) = force x
    case st !! i of
      Pack Nothing  -> do
        v <- m
        let v' = unsafeCoerce v
        (st' :: [Pack]) <- get
        put (update x v' st')
        k v'
      Pack (Just v) -> k (unsafeCoerce v)
  Apply fun arg -> do
    st <- get
    let (t, st') = insert arg st
    put st'
    app fun t >>= k