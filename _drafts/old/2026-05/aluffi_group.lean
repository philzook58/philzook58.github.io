
import Plausible

class Group (G : Type) extends Add G, Zero G, Neg G where
  mul_assoc : ∀ a b c : G, a + b + c = a + (b + c)
  one_mul : ∀ a : G, 0 + a = a
  mul_one : ∀ a : G, a + 0 = a
  mul_left_inv : ∀ a : G, -a + a = 0

instance intGroup : Group Int where
  mul_assoc := by exact Int.add_assoc
  one_mul := by exact Int.zero_add
  mul_one := by exact Int.add_zero
  mul_left_inv := by exact Int.add_left_neg

instance booladd : Add Bool where
  add := xor

instance boolZero : Zero Bool where
  zero := false

instance boolNeg : Neg Bool where
  neg := id


#check Bool.xor_assoc
instance boolGroup : Group Bool where
  mul_assoc := by decide -- exact Bool.xor_assoc
  one_mul := by decide
  mul_one := by decide
  mul_left_inv := by decide
-- infer instances?

-- group morphisms
