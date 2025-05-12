

def myinv (A : Type) (x y : A) (p : x = y) : y = x := by
  rw [p]
  done

#print myinv
-- https://lean-lang.org/theorem_proving_in_lean4/quantifiers_and_equality.html#equality
#check congrArg
#check Eq.refl
#check Eq.symm

-- https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#HEq
#check HEq
