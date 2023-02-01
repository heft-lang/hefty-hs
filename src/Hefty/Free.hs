{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE LambdaCase #-}
module Hefty.Free where

import Control.Monad ( ap, liftM, (>=>) )
import Control.Natural
import Control.Category
import Prelude hiding ((.), id)

data Freer f a
  = Pure a
  | forall c. Do (f c) (c -> Freer f a)

instance Applicative (Freer f) where pure = Pure; (<*>) = ap
instance Functor (Freer f) where fmap = liftM
instance Monad (Freer f) where
  Pure x >>= k = k x
  Do op k1 >>= k2 = Do op (k1 >=> k2)


-- functor sum

infixr 6 +
data (f + g) a = L (f a) | R (g a)
  deriving Functor

sum_ :: (f a -> b) -> (g a -> b) -> (f + g) a -> b
sum_ f _ (L x) = f x
sum_ _ g (R x) = g x

-- isomorphisms

data Iso f g = Iso { to :: f :~> g, from :: g :~> f }

type f <~> g = Iso f g

(<~>) :: (f :~> g) -> (g :~> f) -> Iso f g
(<~>) = Iso

isoRefl :: f <~> f
isoRefl = id <~> id

isoSym :: f <~> g -> g <~> f
isoSym iso = from iso <~> to iso

isoTrans :: f <~> g -> g <~> h -> f <~> h
isoTrans iso1 iso2 = (to iso2 . to iso1) <~> (from iso1 . from iso2)

isoSumCong :: g <~> h -> (f + g) <~> (f + h)
isoSumCong iso = NT (sum_ L (R . ($$) (to iso))) <~> NT (sum_ L (R . ($$) (from iso)))

isoSumSwap :: (f + (g + h)) <~> (g + (f + h))
isoSumSwap = NT (sum_ (R . L) (sum_ L (R . R)))
             <~> NT (sum_ (R . L) (sum_ L (R . R)))


-- injection/toFore pack,
-- which existentially packages `h` and a witness that `g <~> f + h`
data Forephism f g =
  forall h. Functor h => Forephism { forephism :: g <~> (f + h) }


-- functor subsumption

infixr 5 <
class f < g where
  witness :: Forephism f g

-- short-hand

inj :: forall f g a. f < g => f a -> g a
inj x = case witness @f @g of Forephism iso -> from iso $$ L x

proj :: forall f g a. f < g => g a -> Maybe (f a)
proj x = case witness @f @g of
  Forephism iso -> sum_ Just (const Nothing) $ to iso $$ x

-- sum instances

instance f < f where
  witness = Forephism (NT L <~> NT (sum_ id (\ (x :: Nop k) -> case x of)))

instance Functor g => f < f + g where
  witness = Forephism isoRefl

instance (Functor h, f < g) => f < h + g where
  witness = case witness @f @g of
    Forephism iso ->
      Forephism (isoTrans (isoSumCong iso) isoSumSwap)


-- id functor

newtype Id a = Id { unId :: a } deriving ( Functor , Eq )

instance Monad Id where
  Id a >>= k = k a

instance Applicative Id where
  pure = Id
  (<*>) = ap

deriving instance Show a => Show (Id a)


-- ubiquitous "no effect" (used as final row entry)

data Nop k
  deriving Functor

un :: Freer Nop a -> a
un (Pure x) = x
un (Do op _) = case op of


-- folding trees, paramorphically

parafold :: (a -> b)
         -> (forall c. f c -> (c -> (Freer f a, b)) -> b)
         -> Freer f a
         -> b
parafold gen _   (Pure a) = gen a
parafold gen alg (Do op k) = alg op (\c -> let k' = k c in (k', parafold gen alg k'))

-- folding trees, catamorphically

fold :: (a -> b)
     -> (forall c. f c -> (c -> b) -> b)
     -> Freer f a
     -> b
fold gen alg = parafold gen (\op k -> alg op $ fmap snd k)


-- simple handler

data Handler f a f' b
  = Handler { ret :: a -> Freer f' b
            , hdl :: forall c. f c -> (c -> Freer f' b) -> Freer f' b }

handle :: Handler f a f' b
       -> Freer (f + f') a
       -> Freer f' b
handle h = fold (ret h) (sum_ (hdl h) Do)


-- parameterized handler

data Handler_ f a p f' b
  = Handler_ { ret_ :: a -> p -> Freer f' b
             , hdl_ :: forall c. f c -> (c -> p -> Freer f' b) -> p -> Freer f' b }

handle_ :: Handler_ f a p f' b
        -> Freer (f + f') a
        -> p
        -> Freer f' b
handle_ h = fold (ret_ h)
                 (sum_ (hdl_ h) (\ op k p -> Do op (\c -> k c p)))


-- paramorphic simple handler

data ParaHandler f f' g a
  = ParaHandler { pararet :: a -> Freer f' (g a)
                , parahdl :: forall c. f c -> (c -> ( Freer (f + f') a
                               , Freer f' (g a) )) -> Freer f' (g a) }

parahandle :: ParaHandler f f' g a
           -> Freer (f + f') a
           -> Freer f' (g a)
parahandle h = parafold (pararet h) (sum_ (parahdl h) (\op k -> Do op (fmap snd k)))


-- paramorphic parameterized handler

data ParaHandler_ f f' p g a
  = ParaHandler_ { pararet_ :: a -> p -> Freer f' (g a)
                 , parahdl_ :: forall c. f c -> (c -> (Freer (f + f') a
                                 , p -> Freer f' (g a))) -> p -> Freer f' (g a) }

parahandle_
  :: ParaHandler_ f f' p g a
  -> Freer (f + f') a
  -> p
  -> Freer f' (g a)
parahandle_ h = parafold (pararet_ h)
                         (sum_ (parahdl_ h) (\op k p -> Do op (\c -> snd (k c) p)))


-- convert a tree using a natural transformation

convert :: (f :~> g)
        -> Freer f a -> Freer g a
convert g = fold return (Do . ($$) g)


-- effect masking

mask :: Freer g a -> Freer (f + g) a
mask = fold return (Do . R)


-- apply a handler and mask that the effect was handled

hup :: forall f g m a.
       ( f < g )
    => (forall h. Functor h => Freer (f + h) a -> Freer h (m a))
    -> Freer g a -> Freer g (m a)
hup h = case witness @f @g of
  Forephism iso -> convert (from iso) . mask . h . convert (to iso)


-- apply an identity function modulo an insertion witness

hid :: forall f g a.
       ( f < g )
    => (forall h. Functor h => Freer (f + h) a -> Freer (f + h) a)
    -> Freer g a -> Freer g a
hid h = case witness @f @g of
  Forephism iso -> convert (from iso) . h . convert (to iso)


-- free algebra

newtype FreeAlg f a 
  = FreeAlg { freeAlg :: f a -> a }

infixr 7 +~
(+~) :: FreeAlg f1 a -> FreeAlg f2 a -> FreeAlg (f1 + f2) a
a1 +~ a2 = FreeAlg $ \case
  L f1 -> freeAlg a1 f1
  R f2 -> freeAlg a2 f2
