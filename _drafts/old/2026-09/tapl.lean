

/-


https://www.cl.cam.ac.uk/teaching/1415/L28/materials.html
https://github.com/yallop/fomega




https://homes.cs.washington.edu/~mernst/teaching/6.883/readings/reynolds-polylambda.pdf reynold 1990
Introuction to part II polymprphic lambda calculsu


https://dl.acm.org/doi/10.1145/3729308 Daan Ye

inferno

simple and easy


subjects are unsanitized
citizens are sanitized



-/



inductive typ where
  base : typ
  arr : typ -> typ -> typ


inductive cterm where
  | lam : cterm -> sterm
  | annot : sterm -> ty -> cterm

inductive cterm where
  app


inductive aexp where
  | add : aexp -> aexp -> aexp
  | lit : Nat -> aexp


def eval : aexp -> Nat
  | .add x y => (eval x) + (eval y)
  | .lit z => z

#eval eval (.add (.lit 3) (.lit 2))


/--/
inductive evalR : aexp -> Nat -> Prop where
  | add_step : evalR x z -> eval y w -> eval (add x y) (z + w)
  | add_lit : evalR (lit q) q
-/
