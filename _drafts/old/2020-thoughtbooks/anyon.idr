module Anyon


data V2 a = V2Con a a



x : V2 Double
x = V2Con 3.0 7.8


interface Functor v => Additive (v : Type -> Type) where
    vplus : Num a => v a -> v a -> v a

infixr 7 ^*

(^*) : (Num a, Functor v) => a -> v a -> v a
s ^* v = map (* s) v  


Functor V2 where
    map f (V2Con x y) = V2Con (f x) (f y)
Additive V2 where
    vplus (V2Con a b) (V2Con x y) = V2Con (a + x) (b + y) 

y : (Type -> Type, Type -> Type)
y = (V2, V2)
{-
data V21 : Type 1 -> Type 1 where
    V21Con : a -> a -> V21 a
-}
{-
Num Type where
    a + b = Either a b
    a * b = (a , b)
    fromInteger 0 = Void
    fromInteger 1 = ()
    fromInteger n = () + fromInteger (n - 1)
-}
-- Interesting. We do get doubles in the type system
-- *anyon> the (1.41421356237309510 = 1.41421356237309512) Refl
data Prod : (Type -> Type) -> (Type -> Type) -> (Type -> Type) where
    Prod' : (f a) -> (g a) -> Prod f g a

data Comp : (Type -> Type) -> (Type -> Type) -> (Type -> Type) where
    Comp' : f (g a) -> Comp f g a

implementation (Functor f, Functor g) => Functor (Comp f g) where
    map f (Comp' x) = Comp' (map (map f) x)
implementation (Functor f, Functor g) => Functor (Prod f g) where
    map f (Prod' x y) = Prod' (map f x) (map f y)
{- implementation (Additive f, Additive g) => Functor (Comp f g) where
map f (Comp' x) = Comp' (map (map f) x) -}
implementation (Additive f, Additive g) => Additive (Prod f g) where
    vplus (Prod' x y) (Prod' a b) = Prod' (vplus x a) (vplus y b)

{- Vect : ?wha
Vect = Type -> Type
-}
Num (Type -> Type) where
    a + b = Prod a b
    a * b = Comp a b
    fromInteger = believe_me "We'll figure it out later"

dot : Num a => V2 a -> V2 a -> a
dot (V2Con a b) (V2Con x y) = a * x + b * y

data V2' : (Type -> Type) -> Type -> Type where
    V2C' : f a -> f a -> V2' f a

kron : (Num a, Functor f, Functor g) => f a -> g a -> f (g a)
kron f g = map (\s -> s ^* g)  f
