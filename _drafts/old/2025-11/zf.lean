axiom ZFSet : Type
axiom elem : ZFSet → ZFSet → Prop
infix:50 " ∈ " => elem
axiom extensionality : ∀ {x y : ZFSet}, (∀ z : ZFSet, z ∈ x ↔ z ∈ y) → x = y
theorem ext {x y : ZFSet} :  x = y <-> (∀ z : ZFSet, z ∈ x ↔ z ∈ y) := by
  apply Iff.intro
  · intro h; rw [h]; intro z; apply Iff.refl
  · intro h; apply extensionality; exact h

axiom emp : ZFSet
axiom elem_emp : ∀ {x : ZFSet}, ¬ (x ∈ emp)

def elts (x : ZFSet) : ZFSet → Prop := λ y => y ∈ x
axiom upair : ZFSet → ZFSet → ZFSet
axiom elem_upair : ∀ {x y z : ZFSet}, z ∈ upair x y ↔ (z = x ∨ z = y)

theorem upair_not_emp {x y : ZFSet} : upair x y ≠ emp := by
  intro h
  have h1 : x ∈ upair x y := by rw [elem_upair]; left; rfl
  rw [h] at h1
  grind [elem_emp]

theorem upair_comm {x y : ZFSet} : upair x y = upair y x := by
  apply extensionality; intro z
  rw [elem_upair, elem_upair]
  grind

theorem upair_inj {x1 x2 y1 y2 : ZFSet} : upair x1 y1 = upair x2 y2 →
  (x1 = x2 ∧ y1 = y2) ∨ (x1 = y2 ∧ y1 = x2) := by
  intro h
  rw [ext] at h
  specialize h x1





axiom sep : (ZFSet → Prop) → ZFSet → ZFSet
axiom elem_sep : ∀ {P : ZFSet → Prop} {x y : ZFSet}, y ∈ sep P x ↔ (y ∈ x ∧ P y)

noncomputable def sing (x : ZFSet) : ZFSet := upair x x
theorem elem_sing {x y : ZFSet} : y ∈ sing x ↔ y = x := by
  rw [sing, elem_upair]
  grind

def sing_not_emp {x : ZFSet} : sing x ≠ emp := upair_not_emp

axiom bigunion : ZFSet → ZFSet
axiom elem_bigunion : ∀ {x y : ZFSet}, y ∈ bigunion x ↔ ∃ z : ZFSet, (z ∈ x ∧ y ∈ z)

noncomputable def pair (x y : ZFSet) : ZFSet := upair (sing x) (upair x y)

axiom power : ZFSet → ZFSet
axiom elem_power : ∀ {x y : ZFSet}, y ∈ power x ↔ ∀ z : ZFSet, z ∈ y → z ∈ x
