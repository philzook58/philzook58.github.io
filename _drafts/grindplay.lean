
import Lean.Expr

def x :=  Lean.Expr.const `x []
def y := Lean.Expr.const `y []
def z := Lean.Expr.const `z []
def f := Lean.Expr.const `f []
#check Lean.Expr.app x x
#eval f.app x
#eval f

def is_x (e : Lean.Expr) : Bool :=
  match e with
  | .const `x _ => true
  | _ => false
#eval is_x x
#eval is_x y

#eval x == y

#eval Std.HashMap.ofList [(x, 1), (y, 2)]
#eval Std.HashSet.ofArray #[x, y]

def vs := Std.HashSet.ofArray #[x,y]

#eval vs.contains z
#eval vs.size

#check Option.some
def unify (vs : Std.HashSet Lean.Expr) e1 e2 :=
  if e1 == e2 then some []
  else if vs.contains e1 then some [(e1, e2)]
  else if vs.contains e2 then  some [(e2, e1)]
  else none

#eval unify vs z y


#eval #[1,2,3].push 4
def makeset (uf : Array Nat) := uf.push (uf.size)
partial def find (uf : Array Nat) (x : Nat) :=
  let y := uf[x]!
  if y == x then y else find uf y
def union (uf : Array Nat) (x y : Nat) :=
  let x := find uf x
  let y := find uf y
  if x == y then uf
  else uf.set! x y

#eval union #[0, 1, 2] 1 2

-- sexp parser to expr
-- to tptp. Hmm.
-- use metavariables?
/-
def pmatch vs pat e subst :=
  if vs.contains pat then
      match subst.get e with
      | none => subst.add
      | some e2 => e == e2
    else

-- it's a fold.
def substitute subst e :=
  match subst.get e with
  | none =>
      if e.isApp then
      map (subsitute subst)
  | some e1 => e1

-/
