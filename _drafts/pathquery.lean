

-- Hmm. Tree decomposition in lean?
/-
Having HOAS + rewriting, would that help?

-/

namespace RealSimp

axiom R : Type
axiom mul : R -> R -> R
axiom add : R -> R -> R
noncomputable instance : Add R where
  add := add



axiom sin : R -> R
axiom cos : R -> R
axiom integ : (R -> R) -> R -> R -> R
axiom deriv : (R -> R) -> (R -> R)

structure C where
  re : R
  im : R



@[simp] axiom add_comm : forall x y : R, x + y = y + x
@[simp] axiom add_assoc : forall x y z : R, (x + y) + z = x + (y + z)




end RealSimp



inductive Expr where
  | Atom : String -> Expr
  | Seq : Expr -> Expr -> Expr
  | Star : Expr -> Expr
deriving Repr, BEq

abbrev DB := Std.HashMap String (HashSet (Nat × Nat))

def eval (e : Expr) (db : DB) :=
  match e with
  | Atom s => db.get! s
  | Seq a b => let a := eval a db
               let b := eval b db
               {a,c for (x,y) in }
  | Star a =>


def to_sql : Expr -> String
| .Atom s => ""
| .Seq a b => ""
| .Star a => ""
