import Lean
-- import Lean.Expr
/-
Ok how about this perversity.

Programming lean like python.

I could also even make a macro thing that replicates python syntax.

It already uses def! What's the difference?

Do a python tutorial.



-/


def myfib (n : Nat): Nat := IO.run do
  let mut acc := 0
  for

#check Lean.Expr
#print "hello"

#check Lean.Expr

structure Proof where
  fm : Lean.Expr
  reasons : List Lean.Expr

def ax (fm : Lean.Expr) : Proof :=
  { fm := fm, reasons := [] }

--#eval panic! "ehhlo world"
#eval assert! false; "fail"

def call_z3 (smt2 : String) : IO String := do
  let fname := "/tmp/leany.smt2"
  IO.FS.writeFile fname smt2
  let cmd := "z3"
  let args := #[fname]
  let output ← IO.Process.run  {
    cmd,
    args
  }
  return output

#eval call_z3 "
(declare-fun x () Int)
 (declare-fun y () Int)
(assert (= x y)) (check-sat)"

def foo (x : Int) : Int :=
  if x > 0 then x else panic! "x must be positive"

#eval foo -5


unsafe def head1 (xs : List α) : α :=
  match xs with
  | x::_ => x
  | _ => panic! "head1: empty list"

def doit (x : α)  : IO α  :=  do
  return x

#eval! doit (head1 [1, 2, 3])

/-
partial def expr_smt (e : Lean.Expr) : IO String :=
  match e with
  | Lean.Expr.const n _ => n.toString
  | Lean.Expr.app f a  => s!"({expr_smt f} {expr_smt a})"
  | Lean.Expr.forallE n b _ _ => s!"(forall {n} {expr_smt b})"
  | Lean.Expr.eq a b _ => s!"(= {expr_smt a} {expr_smt b})"




partial def modus (a ab : Proof) : Proof :=  Id.run do
  assert! (a.fm == ab.fm)
  --a.fm.equal ab.fm.
  --{ fm := Lean.mkApp a.fm ab.fm, reasons := a.reasons ++ ab.reasons }
-/
