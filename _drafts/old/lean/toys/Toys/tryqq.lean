import Qq
open Qq


def a := q([42 + 1, 10])

#print a


/-
def mypow (n : Nat) : Q(Nat -> Nat) :=
match n with
| 0 => q(λ x => 1)
| 1 => q(λ x => x)
| _ => q(λ x => x * $(mypow (n - 1)) x)
-/
