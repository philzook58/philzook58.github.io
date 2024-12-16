import Aesop


#check BitVec 64

example (x y : BitVec 64) : x ^^^ y ^^^ x = y := by
  --simp -- simp made no progress
  bv_decide


example : α → α :=
  by aesop



def hello := "world"

/-
pow example.
bv_decide

-/
