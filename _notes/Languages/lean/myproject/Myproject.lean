import Std.Data.List.Basic
import Mathlib.Tactic.LibrarySearch
import Mathlib.Tactic.Linarith
import Aesop

-- aesop is an auto tactic
example : α → α :=
  by aesop



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
  show q ∧ p from And.intro hq hp


theorem plus_comm : forall a b, a + b + 0 = b + a := by
  intros a b
  have c : a + b = b + a := by exact IsSymmOp.symm_op a b
  rw [c]
  have d : forall x, x + 0 = x := by intros; exact namedPattern rfl rfl rfl
  rw [d]

-- ok, so unification variables can be made by apply, or explicit ?x maybe?
theorem existstry : exists x, x = 11 := by
  apply Exists.intro
  rfl

example : exists x, x = 11 := by
  exists ?x
  exact 11
  rfl

-- simp?

/-

repeat (apply r1 | apply r2 | apply r3 <;> simp)

-/

#check existstry

