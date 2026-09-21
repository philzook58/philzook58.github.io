import Aesop


#check BitVec 64

example (x y : BitVec 64) : x ^^^ y ^^^ x = y := by
  --simp -- simp made no progress
  bv_decide


example : α → α :=
  by aesop

example : forall a b, a -> b -> a ∧ b := by
  intros a b h1 h2
  split


def hello := "world"

/-
pow example.
bv_decide

-/
