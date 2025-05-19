

def myinv (A : Type) (x y : A) (p : x = y) : y = x := by
  rw [p]
  done
-- https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/

#check Eq.casesOn
#check Eq.recOn
#check Eq.rec
def myinv' (A : Type) (x y : A) (p : x = y) : y = x :=
  Eq.casesOn p (Eq.refl x)

--def minv' (A : Type) (x y : A) (p : x = y) : y = x := Eq.induction


#print myinv
-- https://lean-lang.org/theorem_proving_in_lean4/quantifiers_and_equality.html#equality
#check congrArg
#check Eq.refl
#check Eq.symm

-- https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#HEq
#check HEq
