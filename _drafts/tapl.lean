


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
