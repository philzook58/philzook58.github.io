
-- https://www.csl.sri.com/~tiwari/papers/thesis.pdf

/-
Atomic abstract congruence?

-/

-- https://github.com/codyroux/traat-lean/blob/main/Traat/chapter2.lean

inductive term where
  | app : term -> term -> term
  | sym : String -> term -> term
deriving Repr, DecidableEq
