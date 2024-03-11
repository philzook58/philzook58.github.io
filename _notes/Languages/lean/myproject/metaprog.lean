


/-
So we're interested in metaprogramming in lean.
Metaprogramming is a really interesting and useful topic.

- Can we do partial evaluation in lean?
- Building reflective tactics

There's a lean community book
https://leanprover-community.github.io/lean4-metaprogramming-book/

Beyond Notations: Hygienic Macro Expansion for Theorem Proving Languages
https://link.springer.com/chapter/10.1007/978-3-030-51054-1_10

The lean system paper

Qq library


# Proof by reflection
http://adam.chlipala.net/cpdt/html/Reflection.html

-/
#print Nat

inductive isEven : Nat → Prop where
  | even_0 : isEven 0
  | even_ss : isEven n → isEven (.succ (.succ n)) -- 2 + n doesn't unify as well

example : isEven 2 := by
  apply?

example : isEven 2 := by
  apply isEven.even_ss
  apply isEven.even_0

example : isEven 2 := by
  simp [isEven.even_ss, isEven.even_0]

example : isEven 2 := by
  repeat constructor


-- https://coq.inria.fr/doc/V8.11.1/refman/addendum/ring.html#how-does-it-work
inductive pexpr : Type where
  | const : ℂ -> pexpr
  | var : Nat -> pexpr
  | add : pexpr -> pexpr -> pexpr
  | sub : pexpr -> pexpr -> pexpr
  | mul : pexpr -> pexpr -> pexpr
  | opp : pexpr -> pexpr
  | pow : pexpr -> Nat -> pexpr
