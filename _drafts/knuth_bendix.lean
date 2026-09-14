/-
String knuth bendix + proofs
Termination. Fairness. Completeness

-/

namespace StrKB
abbrev Str a := Array a


-- total :str, left : Nat, right : Nat
-- Don't have to make new string? a slice.
structure StrCtx a where
  left : Str a
  right : Str a
deriving Repr, BEq

def plug (x : Str a) (ctx : StrCtx a) : Str a :=
  ctx.left ++ x ++ ctx.right

-- hmm. extract. Ok
def find [BEq a] (x : Str a) (pat : Str a) : Option (StrCtx a) := Id.run do
  for i in 0...(x.size - pat.size + 1) do
    if pat.isPrefixOf (x.extract i x.size) then
      return some { left := x.extract 0 i, right := x.extract (i + pat.size) x.size }
  return none

#guard find #[4,1,2,3] #[1,2,3] == some {left := #[4], right := #[]}


def overlaps [BEq a] (x : Str a) (y : Str a) : List (StrCtx a) := Id.run do
  let (x, y) := if x.size <= y.size then (x, y) else (y, x)
  let mut result := []
  for i in 0...y.size - x.size + 1 do
    if x.isPrefixOf (y.extract i y.size) then
      result := { left := y.extract 0 i, right := y.extract (i + x.size) y.size } :: result
  for n in 1...x.size do
    if y.extract (y.size - n) y.size == x.extract 0 n then
      result := { left := y.extract 0 (y.size - n), right := #[] } :: result
    if x.extract (x.size - n) x.size == y.extract 0 n then
      result := { left := #[], right := y.extract n y.size } :: result
  return result.reverse


structure Rewrite a where
  lhs : Str a
  rhs : Str a
deriving Repr, BEq

def simplify [BEq a] (t : Str a) (rws : List (Rewrite a)) :=
  for (rw : Rewrite a) in rws do
    if let some ctx := find t rw.lhs then
      return plug rw.rhs ctx |>.simplify rws
  return t


structure MyEq a where
  lhs : Str a
  rhs : Str a
deriving Repr, BEq

def naive (eqs : List (MyEq a)) : :=


end StrKB
