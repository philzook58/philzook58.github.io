import Qq
import Lean
import Mathlib
-- import Lean.Meta.Grind
open Lean Qq Meta

--example [CommSemiring α] (x : α) : x^2 + 1 = x -> x^7 = x := by
--  grind


#check List.Assoc

namespace LA

structure Counter (a : Type) where
  data : List (a × Nat)
deriving Repr, BEq, Inhabited

def bump (l : Counter a) (x : a) (n : Nat) :=
  List.AssocList.set x (List.AssocList.getD l.data 0 + n)


def combine (x y : Counter a) :=
  x.data.foldl (fun acc (z,n) => bump acc z n) y.data



end LA


#check  Lean.Meta.Grind.Arith.CommRing.superposeWith
-- cancellative semirings injectively embed?
/-
What is this construction
@[local simp] def r : (α × α) → (α × α) → Prop
  | (a, b), (c, d) => ∃ k, a + d + k = b + c + k

Ok. That's pretty cool.
"Grothendieck style ring envelope"
Is this an encoding I can use to use a regular buchberger solver?
https://en.wikipedia.org/wiki/Grothendieck_group

p - q = sum h(l - r) given
p + h- * l + h+ r = q + h+ l + h- r
C1 = h- l + h+ r =  = C2
p + C1 = p + c2 = q + C2
p = q by cancellation of C1/C2
p + C1 --> q + C2 by pure semring + final cancellation
Guessing C1 or C2 is tough.

so concellative semiring proof objects
are h expresions
~ (h+, h-) tuples

WHich are equivalent to C1,C2 + semrinig proof
exists C1 C2, p + C1 = q + C2
Semring needs C1/C2 = 0
(proof of C1/C2 = 0 iterate using same method?
but h might be wrong choice.
C1 = 0

Maybe we can compress stages into a sequence of
[(h0+,h0-),(h1+,h1-), ...] ?

https://www.sciencedirect.com/science/article/pii/S0001870815300815?via%3Dihub
https://www.sciencedirect.com/science/article/pii/S0747717103001159?via%3Dihub
reduction relations for monoid semirings


What are proof objects of multset rewriting? Similar issue
Petri nets.. Hmm.
parallel multiset rewriting
modular multiset rewriting https://www.cs.cmu.edu/~iliano/papers/lpar15.pdf

)

partially commutative categories? Doesn't even make sense
f.g ~ m.s
[{set of all equiv paths}, {set of all equiv paths}, ...]
is a compressed / canonicallized representation
Kind of quotiented out the f.g vs m.s choice
Kind of pushing choices down in an egraph kind of way?
pushing congruence down as much a possible?
(f.g | b.a)  try to push "|" "or" down
 | | | | top level or is just a expanded set of all paths
or comp / trans rules push them as high as possilbe?

Congreucne proof trees with explicit or

q : a = b    p : a = b
-------------- or
  or(p,q) : a = b


Cancellative semiring is very close to ring but als semiring.
Good example to investiaget semiring proof objects?

3x + 4y  is [3 4]
but also x,y |-> 3x + 4y a homomorphism (matrix ish?)
or 3x + 4y is () |-> 3x + 4y


Proof objects for strings or terms
Independent parts can be pushed down

monoidal category otimes and comp for strings
string diagrams indeed

https://arxiv.org/pdf/math/0612088 petri nets and polygraogs


The parallel "or" of a proof object  becomes + for semirings.

Completely non overlapping rewrites work via cong. But it is possible to have overlapping rewrites if a rule
matches on but leaves a structure alone. Which is a little weird, but does show up in guarded rules.
C[a,l] -> C[a,r]
C[l1,b] -> C[r1, b]

aaa -> aa    its a bit ocnfusing whether the a on the left are the same as the a on the right. Which one?

concat(r1, id(a), r2) string proofs can be horizontally and vertically composed. Monoidal category.
Monoidal groupoid?
Strings of operators. Noncommutative polynomials. Put coefficients on the strings. Yeah. It doesn't look quantumy then

egraph string rewriting. Don't bake in assoc.
anyons. associators


Because the structure of a semiring term is a bit mushy, it isn't clear?

deepcong( C[.,-] : rule1, C[-,.] rule2 )
promise(C[.,-], rule1)  - works in l->r position but promises we're in C context
par(promosie(C1,r1), promoise(C2, r2)) if C1 C2 are

some kind of continuation inversion thing?

subst(C, rule) its basically this? ... nooo.


-/
#check Lean.Grind.Ring.OfSemiring.Q

-- https://lean-lang.org/doc/reference/latest/The--grind--tactic/Algebraic-Solver-_LPAR_Commutative-Rings___-Fields_RPAR_/#AddRightCancel
-- good lord
/-
Nat + 0 = Nat + 1 does not imply 0 = 1
Ok. Interesting.

That's like cardinal arithmetic
Ordinals are non commutative


-/

example {α : Type} [CommSemiring α] [IsRightCancelAdd α]
    (x : α) (h : 1 + x*x = x) : x^7 = x := by
  grind

#check Expr.getAppFn
def a := q(1 + 2) -- by_elabq?
#eval a
#eval a.getAppFn
#check Expr.appFn!
#check Lean.Meta.Grind.Arith.CommRing.reifyCore?
#check Mathlib.Tactic.Ring.Common.evalAdd
-- Based on <http://www.cs.ru.nl/~freek/courses/tt-2014/read/10.1.1.61.3041.pdf> .

namespace Mono

inductive MonoE (a : Type) where
  | atom : a -> MonoE a
  | add : MonoE a -> MonoE a -> MonoE a
  -- | eps : MonoE a
deriving Repr, BEq, Inhabited

def isPlus (e : Expr) : Option (MonoE Expr) :=
  match_expr e with
  | HAdd.hAdd _ _ _ _inst a b => some <| .add (.atom a) (.atom b)
  | _ => none

partial def toMono (e : Expr) : MonoE Expr :=
  match_expr e with
  | HAdd.hAdd _ _ _ _inst a b => .add (toMono a) (toMono b)
  | _ => .atom e

partial def reassoc {a : Type} : MonoE a -> MonoE a
| .atom x => .atom x
| .add (.add a b) c => reassoc (.add a (.add b c))
| .add (.atom a) b => .add (.atom a) (reassoc b)
#check Std.Associative
def monoToExpr (e : MonoE Expr) : Elab.TermElabM Expr :=
  match e with
  | .add a b => do
                let a <- monoToExpr a
                let b <- monoToExpr b
                mkAdd a b
                --mkAppM ``HAdd.hAdd #[a, b]
  | .atom a => return a

#eval isPlus q(1 + 2)
#check by_elab monoToExpr (reassoc (toMono q(1 + 2 + 3 + 4)))
#check 1 + 2 + 3 + 4

/-
Reflection of addition expressions.
A la grind, a la mathlib?

match_expr
let_expr
Q?

getFn that unwraps all funs?

Is monoid simplest version?
Patterns for proof carrying?
Make combinators you want in surface lean.
So personal little proof dsl. Interesting.

-/

-- #check match_expr


end Mono


namespace Semi
--- Semiring completion in Lean
-- If it could work over type isomorphisms, that'd be sweet

-- https://leanprover-community.github.io/theories/sets.html#multisets Hmm. Is it worth using this?

structure MultiSet a where
  data : Array a
deriving Repr, BEq

def mkMultiSet (x : Array Nat) : MultiSet Nat :=
  { data := x.mergeSort }

instance [LE a] : LE (MultiSet a) where
  le x y :=
    let rec worker x y :=
                match x,y with
                | #[], _ => True
                | _, #[] => False
                | a :: xs, b :: ys => a <= b || le xs ys
    worker x.data y.data


end Semi
