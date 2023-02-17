
-- Use and abuse of instance parameters in the Lean mathematical library
-- https://arxiv.org/pdf/2202.01629.pdf

class GoodNum (n : Int) where

instance : GoodNum 3 where
instance : GoodNum 4 where

#check (inferInstance : GoodNum 4)

-- set_option in

--variable (mylist : Type)
def mylist := Type
--variable (cons : Int -> mylist -> mylist) --(nil : mylist)
--variable (myappend : mylist -> mylist -> mylist -> Prop)
axiom nil : mylist
axiom cons : Int -> mylist -> mylist
class MyAppend (x : Type) (y : Type) (z : Type) where






#check MyAppend Int Int Int 
instance myfoo (x : mylist) : MyAppend nil x x where
instance [MyAppend xs ys zs] : MyAppend (cons x xs) (ys) (cons x zs) where
#check myfoo
#check inferInstance
#check (inferInstance : MyAppend nil nil nil)
#synth (MyAppend nil nil nil)
#check exists x, x
--theorem mytest : (Σ z, MyAppend (cons 7 nil) nil z) := by
--  exists
--  exact inferInstance


--#print mytest

-- instance : MyAppend (cons x xs) (ys) (cons x zs) where

axiom A : Type
axiom B : Type
axiom C : Type
axiom D : Type

class R (a : Type) (b : Type) where

instance I1 : R A B where
instance I2 : R A C where
instance I3 : R C D where
instance I4 {X Y Z : Type} [R X Y] [R Y Z] : R X Z where
#check (inferInstance :  R A D)
set_option trace.Meta.synthInstance true
#synth R A D


class Quant (a : Type) where
class Foo (a : Type) where
class Biz (a : Type) where
-- https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/quantified_constraints.html
instance [Biz a] : Quant a where
instance biz [forall a, [Biz a] : Quant a] : Foo Int where
#check biz
#synth Foo Int

-- unification hints

