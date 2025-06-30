import Lean

#eval Lean.Expr.const `hello []

#eval Lean.Name.mkSimple "Hello"

--#eval Lean.Name.mk


partial def find (uf : Array Nat) (x : Nat) : Nat :=
if uf[x]! == x then x else find uf uf[x]!

--   if x >= uf.size then x else
def makeset (uf : Array Nat) : Array Nat :=
  uf.push uf.size

def empty : Array Nat :=
  Array.mkEmpty 0

def union (uf : Array Nat) (x y : Nat) : Array Nat :=
  let x' := find uf x
  let y' := find uf y
  if x' == y' then uf else
    uf.set! x' y'

#eval let uf := makeset empty
      let uf := makeset uf
      let uf := union uf 0 1
      find uf 2

example : forall x y : Nat, x + y = y + x :=
