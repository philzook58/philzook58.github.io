/-

Lean has a powerful rewriting engine inside it

How can I use it to programmatically rewrite an expression and return it?

Screw proofs. That;s a cherry.

Blast in axioms as simp rules.


I think what I like most is _calculating_, which is adjacent to proving and computing
but is a little different.


Compare with dedukti, isabelle, maude

Examples:
KAT as rewrite rules (?)
Deriv
basic integrals?

Look at my rulesets post



-/
import Smt

theorem addition (p q : Bool) : p → p || q := by
  smt_show
  simp_all
