{-# LANGUAGE FlexibleInstances #-}
module Diff where






data Expr = X | Plus Expr Expr | Times Expr Expr | Lit Double | Exp Expr


diff :: Expr -> Expr
diff X = Lit 1
diff (Lit _) = Lit 0
diff (Plus x y) = Plus (diff x) (diff y)
diff (Times x y) = Plus (Times (diff x) y) (Times x (diff y))
diff (Exp x) = Times (diff x) (Exp x)

interp :: Expr -> Double -> Double
interp X x = x
interp (Lit x) _ = x
interp (Plus f g) x = (interp f x) + (interp g x)
interp (Times f g) x = (interp f x) * (interp g x)
interp (Exp f) x = exp (interp f x)

interpdiff = interp . diff


class ExprF a where
    plus :: a -> a -> a
    lit :: Double -> a
    exp' :: a -> a
    times :: a -> a -> a
    x :: a

instance ExprF Expr where
    plus = Plus
    lit = Lit
    exp' = Exp
    times = Times
    x = X

instance ExprF (Double -> Double) where
    plus f g x = (f x) + (g x)
    times f g x = (f x) + (g x)
    x y = y
    exp' f x = exp (f x)
    lit = const


{-
Finally tagless representation of Vectors

v2 :: a -> a -> repr a




class Basis n v where
    e :: v

instance Basis 0 (Double -> Double) where
    e = id
instance basis => Basis 0 (Double -> b) where
    e = \x -> x
instance Basis n b => Basis (S n) (Double -> b) where
    e = const (e @n)


e @1


read 


try transitioning to state monad
try to understand yallop machines
try to replace Call / remove Call altogether.


I gue


-}