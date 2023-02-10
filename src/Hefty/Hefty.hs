{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DataKinds #-} -- needed for 'type Effect' in GHC 9.2.5
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE BlockArguments #-}

module Hefty.Hefty where

import Control.Monad
import Data.Kind (Type)
import Control.Category (Category (..))
import Prelude hiding ((.), id)
import Control.Natural ( type (~>) )

type Effect = (Type -> Type) -> (Type -> Type)

type Hefty :: Effect -> Type -> Type
data Hefty h a
  = Return a
  | forall c. Op (h (Hefty h) c) (c -> Hefty h a)

class HFunctor h where
  hmap :: (forall x. f x -> g x) -> h f a -> h g a

instance HFunctor h => Applicative (Hefty h) where pure = Return; (<*>) = ap
instance HFunctor h => Functor (Hefty h) where fmap = liftM
instance HFunctor h => Monad (Hefty h) where
  Return x >>= k = k x
  Op f k1  >>= k2 = Op f (k1 >=> k2)

-- hfunctor sum

infixr 6 ++
type (++) :: Effect -> Effect -> Effect
data (h1 ++ h2) f a = LH (h1 f a) | RH (h2 f a)
  deriving Functor

sumH_ :: (h1 f a -> b) -> (h2 f a -> b) -> (h1 ++ h2) f a -> b
sumH_ f _ (LH x) = f x
sumH_ _ g (RH x) = g x

-- hfunctor subsumption

newtype (:~~>) h1 h2 = NTH { ($$$) :: forall f. h1 f ~> h2 f }

instance Category (:~~>) where
  id = NTH id
  (.) (NTH f) (NTH g) = NTH (f . g)

data (<~~>) f g = IsoH { toH :: f :~~> g, fromH :: g :~~> f }

(<~~>) :: (f :~~> g) -> (g :~~> f) -> f <~~> g
(<~~>) = IsoH

isoReflH :: f <~~> f
isoReflH = id <~~> id

isoSymH :: f <~~> g -> g <~~> f
isoSymH iso = fromH iso <~~> toH iso

isoTransH :: f <~~> g -> g <~~> h -> f <~~> h
isoTransH iso1 iso2 = (toH iso2 . toH iso1) <~~> (fromH iso1 . fromH iso2)

isoSumCongH :: g <~~> h -> (f ++ g) <~~> (f ++ h)
isoSumCongH iso = NTH (sumH_ LH (RH . ($$$) (toH iso)))
             <~~> NTH (sumH_ LH (RH . ($$$) (fromH iso)))

isoSumSwapH :: (f ++ (g ++ h)) <~~> (g ++ (f ++ h))
isoSumSwapH = NTH (sumH_ (RH . LH) (sumH_ LH (RH . RH)))
         <~~> NTH (sumH_ (RH . LH) (sumH_ LH (RH . RH)))


-- injection/toFore pack,
-- which existentially packages `h` and a witness that `g <~~> f ++ h`
data ForephismH f g =
  forall h. HFunctor h => ForephismH { forephismH :: g <~~> (f ++ h) }


-- functor subsumption

infixr 5 <<
class f << g where
  witnessH :: ForephismH f g

-- short-hand

injH :: forall h1 h2 f a. h1 << h2 => h1 f a -> h2 f a
injH x = case witnessH @h1 @h2 of 
  ForephismH iso -> fromH iso $$$ LH x

projH :: forall h1 h2 f a. h1 << h2 => h2 f a -> Maybe (h1 f a)
projH x = case witnessH @h1 @h2 of
  ForephismH iso -> sumH_ Just (const Nothing) $ toH iso $$$ x

-- sum instances

data NopH m a

instance HFunctor NopH where
  hmap _ = \case

unH :: Hefty NopH a -> a
unH (Return x) = x
unH (Op f k) = case f of

nopAlg :: Alg NopH f
nopAlg = Alg \case

instance h << h where
  witnessH = ForephismH (NTH LH <~~> NTH (sumH_ id (\(x :: NopH f k) -> case x of)))

instance {-# OVERLAPPING #-} HFunctor g => f << f ++ g where
  witnessH :: HFunctor g => ForephismH f (f ++ g)
  witnessH = ForephismH isoReflH

instance (HFunctor h, f << g) => f << h ++ g where
  witnessH = case witnessH @f @g of
    ForephismH iso ->
      ForephismH (isoTransH (isoSumCongH iso) isoSumSwapH)


instance (HFunctor h1, HFunctor h2) => HFunctor (h1 ++ h2) where
  hmap f (LH x) = LH $ hmap f x
  hmap f (RH x) = RH $ hmap f x

newtype Alg h g = Alg { alg :: forall c a. h g c -> (c -> g a) -> g a }

foldH :: forall g h a.
         HFunctor h
      => (forall x. x -> g x)
      -> Alg h g
      -> Hefty h a
      -> g a
foldH gen _ (Return a) = gen a
foldH gen a (Op f k)   = alg a (hmap (foldH gen a) f) (foldH gen a . k)

infixr ++~
(++~) :: Alg h1 g -> Alg h2 g -> Alg (h1 ++ h2) g
a1 ++~ a2 = Alg \case
  LH x -> alg a1 x
  RH x -> alg a2 x

injAlg :: h << g => Alg h (Hefty g)
injAlg = Alg (Op . injH)

send :: f << h => f (Hefty h) a -> Hefty h a
send op = Op (injH op) Return