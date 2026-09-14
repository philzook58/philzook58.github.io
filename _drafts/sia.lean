
namespace SIA
axiom R : Type
axiom add : R -> R -> R
axiom mul : R -> R -> R
noncomputable instance : Add R where
  add := add
noncomputable instance : Mul R where
  mul := mul

axiom add_comm : forall x y : R, x + y = y + x
axiom add_assoc : forall x y z : R, (x + y) + z = x + (y + z)

axiom zero : R
axiom one : R

noncomputable instance : OfNat R 0 where
  ofNat := zero

noncomputable instance : OfNat R 1 where
  ofNat := one

@[simp] axiom add_zero : forall x : R, x + 0 = x
@[simp] theorem add_zero_l (x : R) :  0 + x = x := by
  rw [add_comm, add_zero]


axiom mul_comm : forall x y : R, x * y = y * x
axiom mul_assoc : forall x y z : R, (x * y) * z = x * (y * z)

@[simp] axiom mul_one : forall x : R, x * 1 = x

@[simp] theorem one_mul (x : R) : 1 * x = x := by
  rw [mul_comm, mul_one]

@[simp] axiom mul_zero : forall x : R, x * 0 = 0
@[simp] theorem zero_mul (x : R) : 0 * x = 0 := by
  rw [mul_comm, mul_zero]

-- instance : Ring R where
axiom lt : R -> R -> Prop
instance : LT R where
  lt := lt





end SIA

/-
DumbReals
DIY Ring tactic
Pendulum?

-/
