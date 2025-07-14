



#eval not true

theorem flum : not ∘ not = id := by
  ext x
  simp

#print flum

#print axioms flum


def sec {A B} (f : A -> B) : Prop :=
  exists (g : B -> A), f ∘ g = id

def retr {A B} (f : A -> B) : Prop :=
  exists (g : B -> A), g ∘ f = id

def isequiv {A B} (f : A -> B) : Prop :=
  sec f ∧ retr f


/-
def eqsig {A} {B : A -> Prop} : (exists (x : A), B x)
-> (exists (y : A), B y) -> Prop
| s t => exists α, Eq.subst α (snd s) = snd t
-/

-- Hott ought to be a meta language compileable to proofsa about ordinary encodings of
-- paths and stuff. Hmm.

-- Is this the same thing as |- Bool type? Not exactly.
#check (Bool : Type)
#check Bool -- Hmm. Maybe this is better. Is it well formed or not?
#check (rfl : 1 + 2 = 3)
#check (rfl : 1 + 2 = 4)


#check fun f => (rfl: id ∘ f = f)
#check Nat.recAux
#check Nat.rec

def myadd : Nat -> Nat -> Nat
| 0, b => b
| .succ a, b => .succ (myadd a b)

#check Sum.inl

#check Eq.rec
#print Eq.propIntro

def myconcat {x y z : A} : (x = y) -> (y = z) -> (x = z)
| rfl, rfl => rfl

def myconcat1 (x : A) : forall y z : A, (x = y) -> (y = z) -> (x = z) :=
  let D x y p := forall z, forall q : y = z, x = z
  let E (x z : A) (q : x = z) := x = z
  let e x : E x x rfl := rfl
  let d : forall x z, forall q : x = z, E x z q := Eq.rec (motive := E)
  Eq.rec (motive := D) d

#print Eq
