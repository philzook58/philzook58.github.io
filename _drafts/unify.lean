import Lean
open Lean
#eval Expr.const `zero []
#eval mkConst `zero
#eval Expr.app (mkConst `zero) (.const `zero [])
#eval Expr.lam `x (.const `Nat []) (.bvar 0) BinderInfo.default

#eval Lean.Meta.isDefEqNat (mkConst `zero) (mkConst `zero)


def Ctx := List (Name × Expr)

structure IsType where
    ctx : Ctx
    A : Expr

structure IsEqType where
    ctx : Ctx
    A : Expr
    B : Expr

structure EqTerm where
    Γ : Ctx
    a : Expr
    b : Expr
    A : Expr

#eval 1
-- #eval Meta.eval 2

-- https://leanprover-community.github.io/lean4-metaprogramming-book/main/03_expressions.html


def myeq (p e : Expr) : Bool :=
    match p, e with
    | .const n _, .const n' _ => n == n'
    | .app f x, .app f' x' =>
        if f == f' then
            myeq x x'
        else
            false
    | _, _ => false


def z := mkConst `zero
def s := mkConst `succ
#eval myeq (mkConst `zero) (mkConst `one)
#eval myeq (mkApp s z) (mkApp s z)
#eval Expr.eqv (mkApp s z) (mkApp s z) -- alpha equal
#eval Lean.Meta.isDefEq (mkApp s z) (mkApp s z)
#eval Lean.Meta.reduce (mkApp s z)
#eval do
    let x <- Meta.mkFreshExprMVar (mkConst `Nat)
    let _ <- Lean.Meta.isDefEq (mkApp s x) (mkApp s z)
    return ()


-- yeah, I'm not reusing lean type gets us much delta

inductive MyTerm : Type where
    | Fn : Name -> List MyTerm -> MyTerm
deriving BEq, Repr

#eval MyTerm.Fn `zero []


--#eval sizeOf (MyTerm.Fn `zero [])

def size (e : MyTerm) : Nat :=
    match e with
    | .Fn _ xs => Id.run do
        let mut acc := 0
        for x in xs do
            acc := acc + size x
        return acc + 1
partial def pmatch (p e : MyTerm) : Bool :=
    match p, e with
    | .Fn f xs, .Fn f' xs' =>
        if f == f' && xs.length == xs'.length then
            xs.zipWith (pmatch) xs' |>.all id
        else
            false
--termination_by p e => (size p, size e)

def succ x := MyTerm.Fn `succ [x]
def zero := MyTerm.Fn `zero []

#eval size (succ (succ zero))

#eval 1.26
#eval (1 : Rat)
