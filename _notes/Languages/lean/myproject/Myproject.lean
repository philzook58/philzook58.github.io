import Std.Data.List.Basic
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.Linarith

theorem foo : 1 = 1 := by
  -- library_search
  exact _root_.trans rfl rfl
#check _root_.trans

theorem bar : x <= 7 + 3*x := by
  linarith

#print bar
def hello := "world"

theorem and_commutative (p q : Prop) : p ∧ q → q ∧ p :=
  fun hpq : p ∧ q =>
  have hp : p := And.left hpq
  have hq : q := And.right hpq
  have pq : p /\ q -> q /\ p := by library_search
  show q ∧ p from And.intro hq hp


theorem plus_comm : forall a b, a + b + 0 = b + a := by
  intros a b
  have mycomm : a + b = b + a := by exact IsSymmOp.symm_op a b