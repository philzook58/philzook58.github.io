



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

#check (Bool : Type)
