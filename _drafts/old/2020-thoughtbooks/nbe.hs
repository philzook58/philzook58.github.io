{-# LANGUAGE GADTs, NoImplicitPrelude, StandaloneDeriving, RankNTypes #-}

module NBE where

import Data.Monoid
import Control.Category
import Prelude hiding ((.), id, fst, snd)
import Control.Arrow ((&&&))
data FM a = Pure a | Mappend (FM a) (FM a) | Mempty deriving (Eq, Show)

instance Semigroup (FM a) where
   (<>) = Mappend
instance Monoid (FM a) where
   mempty = Mempty


lift :: FM a -> (FM a -> FM a)
lift (Pure x) = \y -> (Pure x) <> y
lift (Mappend x y) = (lift x) . (lift y) 
lift Mempty = id

-- using Endo is kind of less clear
-- lift' :: FM a -> Endo (FM a)
-- lift' (Pure x) = Endo $ \y -> (Pure x) <> y
-- lift' (Mappend x y) = (lift' x) <> (lift' y) 
-- lift' Mempty = mempty

lift' :: Monoid b => (a -> b) -> (FM a -> b)
lift' f (Pure x) = f x
lift' f (Mappend x y) = (lift' f x) <> (lift' f y) 
lift' _ Mempty = mempty

lift'' = lift' Endo

normalize :: FM a -> FM a
normalize x = lift x Mempty

eq' :: Eq a => FM a -> FM a -> Bool
eq' x y = (normalize x) == (normalize y)


{-
This isn't quite a great replica of a monoid considered as a category
Instead of having a single object, it feels like we have the same objects as Hask
however only morphisms going from each object to itself
-}

data MonoidCat m a b where
   MonoidCat :: m -> MonoidCat m a a


deriving instance Eq m => Eq (MonoidCat m a b)
deriving instance Show m => Show (MonoidCat m a b)

instance Monoid m => Category (MonoidCat m) where
   id = MonoidCat mempty
   (MonoidCat x) . (MonoidCat y) = MonoidCat (x <> y)


{-

Normalizing Polynomial exressions / Ring?
Ring a => a -> a  
FreeRing a = Mul | Add | Pure | One | Zero | Neg
???? 


-}

data FreeCCC a b where
   Id :: FreeCCC a a -- possibly FreeCCC () () ?
   Comp :: FreeCCC b c -> FreeCCC a b -> FreeCCC a c
   Fst :: FreeCCC (a,b) a
   Snd :: FreeCCC (a,b) b
   Fan :: FreeCCC a b -> FreeCCC a c -> FreeCCC a (b,c)
   -- Curry :: FreeCCC (a,b) c -> FreeCCC a (FreeCCC b c)
   -- Uncurry :: FreeCCC a (FreeCCC b c) -> FreeCCC (a,b) c
   -- Apply :: FreeCCC (a , FreeCCC a b) b
   -- Pure' :: k a b -> FreeCCC a b

-- deriving instance (Eq a, Eq b) => Eq (FreeCCC a b)
deriving instance Show (FreeCCC a b)


{-
data FreeCCC k a b where
   Id :: FreeCCC k a a
   Comp :: FreeCCC k b c -> FreeCCC k a b -> FreeCCC k a c
   Fst :: FreeCCC k (a,b) a
   Snd :: FreeCCC k (a,b) b
   Fan :: FreeCCC k a b -> FreeCCC k a c -> FreeCCC k a (b,c)
   Pure' :: k a b -> FreeCCC k a b

analog of Endo?
newtype Yoneda :: forall b. (a -> b) -> f b
YonedaEmbed k = forall s. (k s a) -> (k s b)

instance Category k => Category (YonEm k) where
   id = id
   
instance Cartesian k => Cartesian (YonEmb k)

interpccc :: CCC k => (k a b -> k' a b) -> FreeCCC k a b -> (k' a b)
interpccc m Id = id
interpccc m (Comp f g) = (interpccc m f) . (interpccc m g)
interpccc 


interpccc :: (YonEmb Id) -> FreeCCC -> 




-}


instance Category FreeCCC where
   id = Id
   (.) = Comp

class Category k => CartesianCategory k where
   fst :: k (a,b) a 
   snd :: k (a,b) b
   fanin :: k a b -> k a c -> k a (b,c)

instance CartesianCategory FreeCCC where
   fst = Fst
   snd = Snd
   fanin = Fan

instance CartesianCategory (->) where
   fst (x,_) = x
   snd (_,y) = y
   fanin = (&&&)

data Ty f a where
   Tup :: Ty f a -> Ty f b -> Ty f (a,b)
   -- Arr :: (Tup f a -> Tup f b) -> Tup f (a -> b)
   PureTy :: f a -> Ty f a


par :: CartesianCategory k => k a b -> k c d -> k (a,c) (b,d)
par f g = fanin (f . fst) (g . snd)

dup :: CartesianCategory k => k a (a,a)
dup = fanin id id
 
interp :: FreeCCC a b -> Ty (FreeCCC s) a -> Ty (FreeCCC s) b
interp Id x = x
interp (Comp f g) x = (interp f) $ (interp g) $ x
interp Fst (Tup x y) = x
interp Fst (PureTy x) = PureTy $ Fst . x
interp Snd (Tup x y) = y
interp Snd (PureTy x) = PureTy $ Snd . x
interp (Fan f g) x = Tup (interp f x) (interp g x)
-- interp (Pure' k)

build :: (forall s. Ty (FreeCCC s) a -> Ty (FreeCCC s) b) -> FreeCCC a b
build f = flup r
   where 
   r = f (PureTy Id)
   flup :: Ty (FreeCCC a) b -> FreeCCC a b
   flup (Tup x y) = Fan (flup x) (flup y)
   flup (PureTy x) = x


normalizeCCC :: FreeCCC a b -> FreeCCC a b
normalizeCCC f = build (interp f)

{-
   Curry :: FreeCCC (a,b) c -> FreeCCC a (FreeCCC b c)
   Uncurry :: FreeCCC a (FreeCCC b c) -> FreeCCC (a,b) c
   Apply :: FreeCCC (a , FreeCCC a b) b



liftccc :: FreeCCC a b -> (s -> a) -> (s -> b)
--  liftccc :: Category k => FreeCCC a b -> (k s a) -> (k s b)
--- liftccc :: FreeCCC a b -> (FreeCCC s a -> FreeCCC s b)
liftccc Id = id
liftccc (Comp f g) = \q -> liftccc f $ liftccc g $ q
liftccc Fst = \q s -> fst (q s)
liftccc Snd = \q s -> snd (q s)
liftccc (Fan f g) = \q s -> ((liftccc f id) &&& (liftccc g id)) (q s)


liftccc :: FreeCCC a b -> FreeCCC s a -> (s -> a) -> (s -> b)
--  liftccc :: Category k => FreeCCC a b -> (k s a) -> (k s b)
--- liftccc :: FreeCCC a b -> (FreeCCC s a -> FreeCCC s b)
liftccc Id = id
liftccc (Comp f g) = \q -> liftccc f $ liftccc g $ q
liftccc Fst = \q s -> fst (q s)
liftccc Snd = \q s -> snd (q s)
liftccc (Fan f g) = \q s -> ((liftccc f id) &&& (liftccc g id)) (q s)

ex1 = liftccc (Comp Fst (Fan Id Id))


(Tup s -> Tup a) -> (Tup s -> Tup b)

FreeCCC a b -> FreeCCC s a -> FreeCCC s b
flup Id = id
flup (Comp f g) = (flup f) . (flup g)
flup Fst = fst  
flup Snd = snd
 Fan 

flup (Curry a) = curry 




FreeCCC a b -> (Tup (Free s a) -> (Tup Free s b)
Id = id

flup Fst (Tup x y) = x
flup Fst (Pure (x,y)) = x 
flup Snd (Tup x y) = y
-- a singletonized tuple tree thing
-- we need to bring evidence that we have a lcosed universe of types
data Tup f a where
   Tup :: Tup f a -> Tup f b -> Tup f (a,b)
   Arr :: (Tup f a -> Tup f b) -> Tup f (a -> b)
   PureT :: f a -> Tup f a

FreeCCC a b -> Tup (k s) a -> Tup (k s) b
flup Fst (Tup x y) = x
flup Fst (Pure k) = fst . k
flup Snd (Tup x y) = y
flup Snd (Pure k) = snd . k
flup (Fan f g) = fanin (flup f) (flup g)


flup Apply (Tup x f) = (flup f) x
flup Apply (PureT x) = apply . x
(Tup x y) = (flup f (Tup x y))

flup (Fan f g) (Tup )
flup Fst (Tup x y) = x
flup Fst (Pure k) = fst . k


:: (forall s. Tup (Free s) a ->  Tup (Free s) b) -> FreeCCC a b
 extract $ f (PureT Id) where
 rebuild :: Tup (FreeCCC a) b -> FreeCCC a b
 rebuild (Tup f g) = Fan (rebuild f) (rebuild g)
 rebuild (PureT x) = x 

 rebuild (Arr f) = f
-}