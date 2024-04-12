-- import Init.Data.Nat
/-
A key piece of describing mathematical logic is the distinction between the object logic and the metalogic. This distinction is hard to keep clear in english sentences.
I don't know the good way to make the leap of understanding. I think I have the spark of it, but not a full grokking.

How does baby come to some understanding of words?
How does a gradeschooler come to understand a "variable" or "polynomial". It's a gradual soak
-/
-- #print Nat
example (x y : Nat) : x + y = y + x := by
  --omega
  -- apply?
  --exact?
  exact Nat.add_comm x y
  -- rw [Nat.add_comm]

example (x y : Nat) : x + y = y + x + 0 := by
  exact Nat.add_comm x y


inductive Term where
  | app : String -> Array Term -> Term

inductive PeanoTerm where
  | zero : PeanoTerm
  | succ : PeanoTerm -> PeanoTerm
  | plus : PeanoTerm -> PeanoTerm -> PeanoTerm

-- numeral (sometimes an underbard, sometimes a little circle)
def numeral ℕ -> PeanoTerm
 | 0 => PeanoTerm.zero
 | n + 1 => PeanoTerm.succ (numeral n)


-- permute can freshen variables.
def permute (x : String) (y : String) : Term -> Term
  | Term.var z -> if z == x then Term.var y else if z == y then Term.var x else Term.var z
  | Term.app f args => Term.app f (args.map (permute x y))

-- chained permutations are a
-- agda one that kmett referenced.


/-
It seems doofy, some forgettable shuffling. But it _is_ unavoidable (?)
-/

def interp : PeanoTerm -> Nat
  | PeanoTerm.zero => 0
  | PeanoTerm.succ n => 1 + interp n
  | PeanoTerm.plus n m => interp n + interp m

/-
We can convert meta nat to object nat, but meta plus can't really be "seen" in the same way. And how much of this is special to how lean works.
-/


-- This is a set of terms.
def is_zero (t : PeanoTerm) : Prop := interp t = 0





partial def nat_interp : Term ->  Nat
  | Term.app "+" args => args.foldl (init := 0) (fun acc arg => acc + nat_interp arg)
  | Term.app "*" args => args.foldl (init := 1) (fun acc arg => acc * nat_interp arg)
  | Term.app n _ => n.toNat!

inductive Pf where
  | ax : Term -> Pf
  | mp : Pf -> Pf -> Pf

/-
"Truth" is a metalogical notion


Carnap diagonalization
Lob

-/

def true (p : Term) : Prop := true

-- quoting

-- trut predicate.



def main : IO Unit := return ()

/-
model thoery

finite subsets of formulas to models

Finstruct

cerosible up arrow

nonempty

choice : Nonempty T -> T

hint (hint)

What would be something simpler to do with thi

finite model of a group

database? |=

![x,y] : Fin n -> x
overspill = transfer

suffices


pra
dialectica in coq
proof mning in lean

rca0. you don't have iduction



bhk interrpetation

tarski
interp (And a b) = interp a /\ interp b

Instead we need to define a notion of programs
inductive program
| and
| or


They could be turing machines.
They could

run : program -> evidence -> bool

Enumerable sets. What does that mean? We need a particular language we're wroking in
Computable functions. What does that mean?
If we have an signature extension, then there is a natrual notion of comparing theories,
but otherwise we really need to define what it means to compare two systems

Systems are already comparable in that they live in the same metalogic (lean)

And they can be compared via the lean intermediary if you've given them semantics in lean

If you bottow your host powers, you kind of don't know what you're borrowing
That's the beauty and danger of it


-/
