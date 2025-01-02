---
title: Translating Cody's Lean Sheffer Stroke Proof to Knuckledragger with ChatGPT
date: 2025-01-01
---

I translated my friend [Cody Roux](https://www.kleene.church/)'s Lean proof <https://github.com/teorth/equational_theories/pull/708> that the axioms of [Sheffer stroke](https://en.wikipedia.org/wiki/Sheffer_stroke) imply it is a boolean algebra into [knuckledragger](https://github.com/philzook58/knuckledragger), my low barrier python proof assistant. Pretty much it is a close one to one translation. I have not even really attempted to understand the proofs at all and was running quite unthinkingly.

Mentally speaking, translating between the lean notation and from the names `commut1` and `commut2` to `sup_comm` and `inf_comm` (a name change I shouldn't have done) was super confusing as trivial as it sounds. All told I think it took me about 3 hours.

Not to toot my own (and Z3's) horn, but I was pretty impressed with Knuckledragger's performance here. A pure algebraic question like this is about as in it's wheelhouse as it comes though. A nice thing is that eventually Cody's proofs looked a little less declarative, but I could just dump the lemmas he used in `kd.lemma` and that papered over it.

I also used ChatGPT to help me. <https://chatgpt.com/share/6776116b-c4d4-8008-b3d0-d73c401feb05> It sometimes was good, sometimes not. Of course ChatGPT doesn't know much if anything about knuckledragger, so I did the first bits to get it started. I am curious if another LLM would do better. I did not use the fancy new o1 model.

I gave it a giant dump of Cody's file, and then the first bits of my translation. As with my experience translation between programming languages it was so so. It worked better going lemma by lemma. I hope as the LLMs trawl my repo, they might get better at this. The fancy new OpenAI interactive editing mode might help, but I don't really know how to use it.

I also have github copilot and was hoping it having the nearby proofs and access to cody's file below would work well. It again was so-so. Sometimes copilot fills out a whole line, but there's often something a bit off.

One interesting thing was that the LLM invented a small feature I didn't have. It tried to applied universally quantified proof objects to arguments to instantiate them, but I had never made that particular `__call__` operator overloading. I added it in, both because I think it's kind of cute, but also so I didn't have to fix the LLM output when it did that. ChatGPT seemed quite confused about the different capabilities of `kd.Lemma` and `kd.Calc`. Maybe there's something there that I should unify them more. The differences exist because `Calc` is much simpler and both have organically evolved. There is a possibility that the mistakes or assumptions ChatGPT make might be the same as a user who is not me. Kind of interesting.

```python
# The following knuckledragger python proof is derived from the lean proofs below
from kdrag.all import *

simp = []
Stroke = smt.DeclareSort("Stroke")
x,y,z,a,b,d = smt.Consts("x y z a b d", Stroke)
nand = smt.Function("nand", Stroke, Stroke, Stroke)
kd.notation.or_.register(Stroke, nand)

# prime is "not"
invert = kd.define("inv", [x],  x | x)
kd.notation.invert.register(Stroke, invert)

sh1 = kd.axiom(smt.ForAll([a], ~(~a) == a))
sh2 = kd.axiom(smt.ForAll([a,b],  a | (b | ~b) == ~a))
sh3 = kd.axiom(smt.ForAll([a,b,d], ~(a | (b | d)) == (~b | a) | (~d | a)))

c = kd.Calc([a,b], a | b)
c.eq(~(~(a | b)), by=[sh1])
c.eq(~(~(a | (~ (~b)))),by=sh1)
c.eq(~~(~~b | a),by=[sh3, invert.defn])
c.eq(b | a, by=[sh1])
commut = c.qed()

c = kd.Calc([a,b], a | ~a)
c.eq(~~(a | ~a), by=sh1)
c.eq(~((a | ~a) | (b | ~b)),by=sh2)
c.eq(~((b | ~b) | (a | ~a)),by=commut)
c.eq(~~(b | ~b),by=sh2)
c.eq(b | ~b, by=sh1)
all_bot = c.qed()



inf = kd.define("inf", [a,b], ~a | ~b)
sup = kd.define("sup", [a,b], ~(a | b))

bot = kd.define("bot", [], a | ~a)
top = kd.define("top", [], ~bot)

inf_comm = kd.lemma(smt.ForAll([a,b], inf(a,b) == inf(b,a)), by=[inf.defn, commut])
sup_comm = kd.lemma(smt.ForAll([a,b], sup(a,b) == sup(b,a)), by=[sup.defn, commut])

ident1 = kd.lemma(smt.ForAll([a], sup(a,bot) == a), by=[sup.defn, bot.defn, sh1, sh2])
ident2 = kd.lemma(smt.ForAll([a], inf(a,top) == a), by=[inf.defn, top.defn, bot.defn, sh1, sh2])


distrib1 = kd.lemma(smt.ForAll([a,b,d], sup(a, inf(b,d)) == inf(sup(a,b), sup(a,d))), by=[inf.defn, sup.defn, sh1, sh3, commut])
distrib2 = kd.lemma(smt.ForAll([a,b,d], inf(a, sup(b,d)) == sup(inf(a,b), inf(a,d))), by=[inf.defn, sup.defn, sh1, sh3, commut])

compl1 = kd.lemma(smt.ForAll([a], sup(a, ~a) == top), by=[sup.defn, top.defn, bot.defn, sh1, sh2, all_bot])
compl2 = kd.lemma(smt.ForAll([a], inf(a, ~a) == bot), by=[inf.defn, bot.defn, sh1, sh2, all_bot])

simp += [ident1, ident2, compl1, compl2]

c = kd.Calc([a], sup(a, top))
c.eq(inf(sup(a,top), top), by=ident2)
c.eq(inf(top, sup(a,top)), by=inf_comm)
c.eq(inf(sup(a, ~a), sup(a,top)), by=compl1)
c.eq(sup(a, inf(~a, top)), by=distrib1)
c.eq(sup(a, ~a), by=ident2)
c.eq(top, by=compl1)
bound1 = c.qed()

# this is where I first started talking to chatgpt

c = kd.Calc([a], inf(a, bot))
c.eq(sup(inf(a,bot), bot), by=ident1)
c.eq(sup(bot, inf(a,bot)), by=sup_comm)
c.eq(sup(inf(a, ~a), inf(a,bot)), by=compl2)
c.eq(inf(a, sup(~a, bot)), by=distrib2)
c.eq(inf(a, ~a), by=ident1)
c.eq(bot, by=compl2)
bound2 = c.qed()

c = kd.Calc([a, b], sup(a, inf(a, b)))
c.eq(sup(inf(a, top), inf(a, b)), by=ident2)         
c.eq(inf(a, sup(top, b)), by=distrib2)            
c.eq(inf(a, sup(b, top)), by=sup_comm) 
c.eq(inf(a, top), by=bound1)                      
c.eq(a, by=ident2)                                 
absorb1 = c.qed()

c = kd.Calc([a, b], inf(a, sup(a, b)))
c.eq(inf(sup(a, bot), sup(a, b)), by=ident1)  
c.eq(sup(a, inf(bot, b)), by=distrib1)  
c.eq(sup(a, inf(b, bot)), by=inf_comm)       
c.eq(sup(a, bot), by=bound2)                    
c.eq(a, by=ident1)                            
absorb2 = c.qed()

c = kd.Calc([a], a)
c.eq(inf(a, sup(a, bot)), by=absorb2)  # Rewrite using absorb2: a ⊓ (a ⊔ bot) = a
c.eq(inf(a, a), by=ident1)                     # Simplify sup(a, bot) = a using ident1
idemp2 = c.qed()

simp += [bound1, bound2, absorb1, absorb2, idemp2]

l = kd.Lemma(kd.QForAll([a,b], sup(a,b) == top, inf(a,b) == bot, b == ~a))
_a, _b = l.intros()
l.intros()
l.symm()
l.eq(inf(_b,top), by=[ident2])
l.eq(inf(_b, sup(_a, ~_a)), by=[compl1])
l.eq(sup(inf(_b,_a), inf(_b, ~_a)), by=[distrib2])
l.eq(sup(inf(_a, _b), inf(~_a, _b)), by=[inf_comm])
l.eq(sup(bot, inf(~_a, _b)))
l.eq(sup(inf(_a, ~_a), inf(~_a, _b)), by=[compl2])
l.eq(sup(inf(~_a, _a), inf(~_a, _b)), by=[inf_comm])
l.eq(inf(~_a, sup(_a, _b)), by=[distrib2])
l.eq(inf(~_a, top))
l.eq(~_a, by=[ident2])
l.auto()
inv = l.qed()

l = kd.Lemma(kd.QForAll([a], ~~a == a))
_a = l.intros()
l.symm()
l.apply(inv)
l.auto(by=[inf_comm, sup_comm, compl1, compl2])
dne = l.qed()

l = kd.Lemma(kd.QForAll([a,b], ~a == ~b,  a == b))
_a, _b = l.intros()
l.intros()
l.have(~~_a == ~~_b)
l.rw(dne, at=-1)
l.auto(by=dne(_a))
inv_elim = l.qed()

l = kd.Lemma(kd.QForAll([a,b], sup(a, ~b) == top, inf(a, ~b) == bot, a == b))
_a, _b = l.intros()
l.intros()
l.have(~_b == ~_a, by=[inv])
l.apply(inv_elim)
l.auto()
cancel = l.qed()

c = kd.Calc([a, b], sup(a, sup(~a, b)))
c.eq(inf(sup(a, sup(~a, b)), top), by=ident2)          # Rewrite: a ⊔ (¬a ⊔ b) = (a ⊔ (¬a ⊔ b)) ⊓ u
c.eq(inf(top, sup(a, sup(~a, b))), by=inf_comm)         # Commute: u ⊓ (a ⊔ (¬a ⊔ b)) -> (a ⊔ (¬a ⊔ b)) ⊓ u
c.eq(inf(sup(a, ~a), sup(a, sup(~a, b))), by=compl1)   # Replace a ⊔ ¬a = u
c.eq(sup(a, inf(~a, sup(~a, b))), by=distrib1)         # Distribute sup over inf
c.eq(sup(a, ~a), by=[absorb2, compl1])                # Simplify: ¬a ⊓ (¬a ⊔ b) = ¬a
c.eq(top, by=compl1)                                   # Simplify a ⊔ ¬a = u
A1 = c.qed()


#c = kd.Calc([a,b], inf(a, sup(~a, b)) == bot)
c = kd.Calc([a, b], inf(a, inf(~a, b)))
c.eq(sup(inf(a, inf(~a, b)), bot), by=ident1)          # Rewrite: a ⊓ (¬a ⊓ b) = (a ⊓ (¬a ⊓ b)) ⊔ z
c.eq(sup(bot, inf(a, inf(~a, b))), by=sup_comm)         # Commute: z ⊔ (a ⊓ (¬a ⊓ b)) -> (a ⊓ (¬a ⊓ b)) ⊔ z
c.eq(sup(inf(a, ~a), inf(a, inf(~a, b))), by=compl2)   # Replace a ⊓ ¬a = z
c.eq(inf(a, sup(~a, inf(~a, b))), by=distrib2)         # Distribute inf over sup
c.eq(inf(a, ~a), by=[absorb1, compl2])                # Simplify: ¬a ⊔ (¬a ⊓ b) = ¬a
c.eq(bot, by=compl2)                                   # Simplify a ⊓ ¬a = z
A2 = c.qed()

simp += [A1, A2]

c = kd.Lemma(smt.ForAll([a, b], ~sup(a, b) == inf(~a, ~b)))
_a, _b = c.intros()
c.symm()
c.apply(cancel) # Hmm. apply should already apply split?
c.split()

# First case
c.rw(dne)
c.rw(sup_comm)
c.rw(distrib1)
#c
c.auto(by=[dne(_a), dne(_b), A1, inf_comm, sup_comm, ident2])

#c.rw(distrib2)
#from kdrag.solvers import VampireSolver, TweeSolver, EProverTHFSolver


c.auto(by=[A1, A2, inf_comm, distrib2, sup_comm, ident1] + simp)
dm1 = c.qed()

l = kd.Lemma(smt.ForAll([a,b], ~inf(a, b) == sup(~a, ~b)))
_a, _b = l.intros()
l.symm()
l.apply(cancel)
l.split()

l.auto(by=[A1, A2, inf_comm, distrib2, sup_comm, ident1] + simp)
l.auto(by=[dne(_a), dne(_b), A2, inf_comm, distrib2, sup_comm, ident1] + simp)
dm2 = l.qed()


simp += [dm1, dm2]

D1 = kd.lemma(smt.ForAll([a,b,d], sup(sup(a, sup(b, d)), ~a) == top), by=[sup_comm, ident2, distrib1, compl1] + simp)

E1 = kd.lemma(smt.ForAll([a,b,d], inf(b, sup(a, sup(b,d))) == b),  by=[distrib2, absorb2, sup_comm, absorb1])

E2 = kd.lemma(smt.ForAll([a,b,d], sup(b, inf(a, inf(b,d))) == b),  by=[distrib1, absorb1, inf_comm, absorb2])

c = kd.Calc([a, b, d], sup(sup(a, sup(b, d)), ~b))
c.eq(sup(~b, sup(a, sup(b, d))), by=sup_comm)                    # Commute: (a ⊔ (b ⊔ c)) ⊔ bᶜ -> bᶜ ⊔ (a ⊔ (b ⊔ c))
c.eq(inf(top, sup(~b, sup(a, sup(b, d)))), by=[inf_comm] + simp)          # Rewrite: u ⊓ (bᶜ ⊔ (a ⊔ (b ⊔ c)))
c.eq(inf(sup(b, ~b), sup(~b, sup(a, sup(b, d)))), by=simp)      # Substitute u = b ⊔ bᶜ
c.eq(inf(sup(~b, b), sup(~b, sup(a, sup(b, d)))), by=sup_comm)   # Commute: (b ⊔ bᶜ) -> (bᶜ ⊔ b)
c.eq(sup(~b, inf(b, sup(a, sup(b, d)))), by=distrib1)           # Distribute inf over sup
c.eq(sup(~b, b), by=E1)                                         # Simplify using E₁: b ⊓ (a ⊔ (b ⊔ c)) = b
c.eq(top, by=[sup_comm] + simp)                                           # Substitute: bᶜ ⊔ b = u
F1 = c.qed()


c = kd.Calc([a, b, d], sup(sup(a, sup(b, d)), ~d))
c.eq(sup(sup(a, sup(d, b)), ~d), by=sup_comm)  # Apply commutativity to reorder (b ⊔ c) -> (c ⊔ b)
                                  # Apply F₁: (a ⊔ (c ⊔ b)) ⊔ cᶜ = u
c.eq(top, by=F1)                  # Substitute: cᶜ ⊔ (a ⊔ (c ⊔ b)) = u
G1 = c.qed()

c = smt.Const("c", Stroke)

d = kd.Calc([a, b, c], inf(~sup(sup(a, b), c), a))
d.eq(inf(a, inf(inf(~a, ~b), ~c)), by=simp+[inf_comm])  
d.eq(sup(inf(a, inf(inf(~a, ~b), ~c)), bot), by=ident1)               # Rewrite using identity
d.eq(sup(bot, inf(a, inf(inf(~a, ~b), ~c))), by=sup_comm)             # Commute bot ⊔ (...) -> (...) ⊔ bot
d.eq(sup(inf(a, ~a), inf(a, inf(inf(~a, ~b), ~c))), by=compl2)        # Substitute a ⊓ ¬a = z
d.eq(inf(a, sup(~a, inf(inf(~a, ~b), ~c))), by=distrib2)              # Distribute inf over sup
d.eq(inf(a, sup(~a, inf(~c, inf(~a, ~b)))), by=inf_comm)              # Reorder terms: (~b ⊓ (~a ⊓ ~c)) -> (~a ⊓ (~c ⊓ ~b))
d.eq(inf(a, ~a), by=E2)                                               # Apply E₂: ¬a ⊔ (¬a ⊓ (¬c ⊓ ¬b)) = ¬a
d.eq(bot, by=compl2)                                                  # Simplify a ⊓ ¬a = z
H1 = d.qed()

d = kd.Calc([a, b, c], inf(~sup(sup(a, b), c), b))
d.eq(inf(~sup(sup(b, a), c), b), by=sup_comm)  # Reorder: (a ⊔ b ⊔ c) -> (b ⊔ a ⊔ c)
d.eq(bot, by=H1)                                    # Apply \( H₁ \): \( \neg (b \lor a \lor c) \land b = z \)
I1 = d.qed()


d = kd.Calc([a, b, c], inf(~sup(sup(a, b), c), c))

J1 = kd.lemma(smt.ForAll([a,b,c], inf(~sup(sup(a, b), c), c) == bot), by=[sup_comm, inf_comm] + simp)

l = kd.Lemma(smt.ForAll([a,b,c], sup(a,sup(b,c)) == sup(sup(a,b),c)))
_a, _b, _c = l.intros()
l.apply(cancel)
l.split()

l.auto(by=[distrib1, D1, F1, G1] + simp)
l.auto(by=[distrib2, inf_comm, H1, I1, J1] + simp)
assoc1 = l.qed()

simp += [assoc1]

assoc2 = kd.lemma(smt.ForAll([a,b,c], inf(a, inf(b,c)) == inf(inf(a,b),c)), by=[inv_elim] + simp)

le = kd.define("le", [a,b], a == inf(b,a))
kd.notation.le.register(Stroke, le)

le_trans = kd.lemma(kd.QForAll([a,b,c], a <= b, b <= c, a <= c), by=[assoc2, le.defn])

le_antisym = kd.lemma(kd.QForAll([a,b], a <= b, b <= a, a == b), by=[le.defn, inf_comm])


```

```python
c = kd.Calc([a, b, d], inf(~sup(a, sup(b, d)), a))

# Step-by-step proof
c.eq(inf(a, inf(~a, inf(~b, ~d))), by=simp+[inf_comm])                          # Substitute: ¬(a ⊔ b) = ¬a ⊓ ¬b
c.eq(sup(inf(a, inf(~a, inf(~b, ~d))), bot), by=ident1)               # Rewrite using identity
c.eq(sup(bot, inf(a, inf(~a, inf(~b, ~d)))), by=sup_comm)             # Commute bot ⊔ (...) -> (...) ⊔ bot
c.eq(sup(inf(a, ~a), inf(a, inf(~a, inf(~b, ~d)))), by=compl2)        # Substitute a ⊓ ¬a = z
c.eq(inf(a, sup(~a, inf(~a, inf(~b, ~d)))), by=distrib2)              # Distribute inf over sup
c.eq(inf(a, sup(~a, inf(~d, inf(~a, ~b)))), by=inf_comm)              
c.eq(inf(a, ~a), by=E2)                                               # Apply E₂: ¬a ⊔ (¬c ⊓ (¬a ⊓ ¬b)) = ¬a
c.eq(bot, by=compl2)                                                  # Simplify a ⊓ ¬a = z

# Conclude the proof
H1 = c.qed()
```

Here is cody's proof for comparison

```lean
import equational_theories.Magma
import Mathlib.Order.BooleanAlgebra

section ShefferLaws

-- Taking notations from https://www.cs.unm.edu/~mccune/papers/basax/v12.pdf and
-- the original Sheffer paper, "A set of five independent postulates for Boolean algebras,
-- with application to logical constants"
class Stroke (α : Type*) where
  stroke : α → α → α

infix:80 " | " => Stroke.stroke

def prime {α} [Stroke α] (a : α) := a | a

postfix:max " ′ " => prime

-- The three laws axiomatize the Sheffer stroke, or NAND, entirely.
-- The remainder of this file is dedicated to that proof.
class ShefferAlgebra (α : Type*) extends Stroke α where
-- We need to assume α is nonempty
elt : α
sh₁ : ∀ a : α, a′′ = a
sh₂ : ∀ a b : α, a | (b | b′) = a′
sh₃ : ∀ a b c : α, (a | (b | c))′ = (b′ | a) | (c′ | a)

variable {α : Type*}

variable [ShefferAlgebra α]

open ShefferAlgebra

lemma commut (a b : α) : a | b = b | a := by
  calc
    a | b = (a | b)′′ := by rw [sh₁]
    _     = (a | (b′′))′′ := by rw [sh₁ b]
    _     = (b′′ | a)′′ := by conv => left; arg 1; arg 1; simp [prime]
                              conv => left; arg 1; rw [sh₃]
                              rfl
    _     = b | a := by repeat rw [sh₁]

lemma all_bot (a b : α) : a | a′ = b | b′ := by
  calc
    a | a′ = (a | a′)′′ := by rw [sh₁]
    _      = ((a | a′) | (b | b′))′ := by rw [sh₂]
    _      = ((b | b′) | (a | a′))′ := by rw [commut]
    _      = (b | b′)′′ := by rw [sh₂]
    _      = b | b′     := by rw [sh₁]

instance : Min α where
  min a b := (a′ | b′)

lemma inf (a b : α) : a ⊓ b = (a′ | b′) := rfl

instance : Max α where
 max a b := (a | b)′

lemma sup (a b : α) : a ⊔ b = (a | b)′ := rfl

instance : HasCompl α where
  compl a := a′

lemma comple (a : α) : aᶜ = a′ := rfl

def z : α := elt | elt′

def u : α := z′

lemma commut₁ (a b : α) : a ⊔ b = b ⊔ a := by simp only [sup, commut]

lemma commut₂ (a b : α) : a ⊓ b = b ⊓ a := by simp only [inf, commut]

@[simp]
lemma ident₁ (a : α) : a ⊔ z = a := by simp only [sup, z, sh₁, sh₂]

@[simp]
lemma ident₂ (a : α) : a ⊓ u = a := by simp only [inf, u, z, sh₁, sh₂]

lemma distrib₁ (a b c : α) : a ⊔ (b ⊓ c) = (a ⊔ b) ⊓ (a ⊔ c) := by
  simp only [sup, inf, sh₁, sh₃, commut]

lemma distrib₂ (a b c : α) : a ⊓ (b ⊔ c) = (a ⊓ b) ⊔ (a ⊓ c) := by
  simp only [sup, inf, sh₁]
  conv => left; exact (sh₁ _).symm
  rw [sh₃]
  exact congr rfl (congr (congr rfl (commut ..)) (commut ..))

@[simp]
lemma compl₁ (a : α) : a ⊔ aᶜ = u := by
  simp only [sup, u, z, comple]
  exact congr rfl (all_bot a elt)

@[simp]
lemma compl₂ (a  : α) : a ⊓ aᶜ = z := by
  simp only [inf, z, u, comple, sh₁, commut]
  exact all_bot a elt

@[simp]
lemma bound₁ (a : α) : a ⊔ u = u := by
  calc
    a ⊔ u = (a ⊔ u) ⊓ u        := by rw [ident₂]
    _     = u ⊓ (a ⊔ u)        := by rw [commut₂]
    _     = (a ⊔ aᶜ) ⊓ (a ⊔ u) := by rw [compl₁]
    _     = a ⊔ (aᶜ ⊓ u)       := by rw [distrib₁]
    _     = a ⊔ aᶜ             := by rw [ident₂]
    _     = u                  := compl₁ a

@[simp]
lemma bound₂ (a : α) : a ⊓ z = z := by
  calc
    a ⊓ z = (a ⊓ z) ⊔ z        := by rw [ident₁]
    _     = z ⊔ (a ⊓ z)        := by rw [commut₁]
    _     = (a ⊓ aᶜ) ⊔ (a ⊓ z) := by rw [compl₂]
    _     = a ⊓ (aᶜ ⊔ z)       := by rw [distrib₂]
    _     = a ⊓ aᶜ             := by rw [ident₁]
    _     = z                  := compl₂ a

@[simp] -- This simp is a little overeager.
lemma absorb₁ (a b : α) : a ⊔ (a ⊓ b) = a := by
  calc
    a ⊔ (a ⊓ b) = (a ⊓ u) ⊔ (a ⊓ b) := by rw [ident₂]
    _           = a ⊓ (u ⊔ b)       := by rw [distrib₂]
    _           = a ⊓ (b ⊔ u)       := by conv => lhs; rw [commut₁]
    _           = a ⊓ u             := by rw [bound₁]
    _           = a                 := ident₂ a

-- it would be nice to have a "dualization" tactic. This might be some work though.
@[simp] -- This simp is a little overeager.
lemma absorb₂ (a b : α) : a ⊓ (a ⊔ b) = a := by
  calc
    a ⊓ (a ⊔ b) = (a ⊔ z) ⊓ (a ⊔ b) := by rw [ident₁]
    _           = a ⊔ (z ⊓ b)       := by rw [distrib₁]
    _           = a ⊔ (b ⊓ z)       := by conv => lhs; rw [commut₂]
    _           = a ⊔ z             := by rw [bound₂]
    _           = a                 := ident₁ a

@[simp]
lemma idemp₂ (a : α) : a ⊓ a = a := by
  symm
  calc
    a = a ⊓ (a ⊔ z) := Eq.symm (absorb₂ a z)
    _ = a ⊓ a       := by rw [ident₁]

lemma inv (a a' : α) : a ⊔ a' = u → a ⊓ a' = z → a' = aᶜ := by
  intro h₁ h₂
  calc
    a' = a' ⊓ u               := Eq.symm (ident₂ a')
    _  = a' ⊓ (a ⊔ aᶜ)        := by rw [compl₁]
    _  = (a' ⊓ a) ⊔ (a' ⊓ aᶜ) := by rw [distrib₂]
    _  = (a' ⊓ a) ⊔ (aᶜ ⊓ a') := by conv => left; right; exact commut₂ a' aᶜ
    _  = (a ⊓ a') ⊔ (aᶜ ⊓ a') := by conv => left; left; exact commut₂ a' a
    _  = z ⊔ (aᶜ ⊓ a')        := by rw [h₂]
    _  = (a ⊓ aᶜ) ⊔ (aᶜ ⊓ a') := by rw [compl₂]
    _  = (aᶜ ⊓ a) ⊔ (aᶜ ⊓ a') := by conv => left; left; exact commut₂ a aᶜ
    _  = aᶜ ⊓ (a ⊔ a')        := by rw [distrib₂]
    _  = aᶜ ⊓ u               := by rw [h₁]
    _  = aᶜ                   := ident₂ aᶜ

lemma dne (a : α) : aᶜᶜ = a := by
  symm
  apply inv
  . rw [commut₁]; exact compl₁ a
  . rw [commut₂]; exact compl₂ a

lemma inv_elim (a b : α) : aᶜ = bᶜ → a = b := by
  intro h
  have h' : aᶜᶜ = bᶜᶜ := congrArg compl h
  simp only [dne] at h'
  trivial

lemma cancel (a b : α) : a ⊔ bᶜ = u → a ⊓ bᶜ = z → a = b := by
  intro h₁ h₂
  have h : bᶜ = aᶜ := by apply inv <;> trivial
  apply inv_elim; symm; trivial

@[simp]
lemma A₁ (a b : α) : a ⊔ (aᶜ ⊔ b) = u := by
  calc
    a ⊔ (aᶜ ⊔ b) = (a ⊔ (aᶜ ⊔ b)) ⊓ u := by rw [ident₂]
    _            = u ⊓ (a ⊔ (aᶜ ⊔ b)) := by rw [commut₂]
    _            = (a ⊔ aᶜ) ⊓ (a ⊔ (aᶜ ⊔ b)) := by rw [compl₁]
    _            = a ⊔ (aᶜ ⊓ (aᶜ ⊔ b)) := by rw [distrib₁]
    _            = a ⊔ aᶜ := by rw [absorb₂, compl₁]
    _            = u := by rw [compl₁]

@[simp]
lemma A₂ (a b : α) : a ⊓ (aᶜ ⊓ b) = z := by
  calc
    a ⊓ (aᶜ ⊓ b) = (a ⊓ (aᶜ ⊓ b)) ⊔ z := by rw [ident₁]
    _            = z ⊔ (a ⊓ (aᶜ ⊓ b)) := by rw [commut₁]
    _            = (a ⊓ aᶜ) ⊔ (a ⊓ (aᶜ ⊓ b)) := by rw [compl₂]
    _            = a ⊓ (aᶜ ⊔ (aᶜ ⊓ b)) := by rw [distrib₂]
    _            = a ⊓ aᶜ := by rw [absorb₁, compl₂]
    _            = z := by rw [compl₂]


@[simp]
lemma dm₁ (a b : α) : (a ⊔ b)ᶜ = aᶜ ⊓ bᶜ := by
  symm
  apply cancel <;> simp [dne]
  . rw [commut₁, distrib₁]
    conv => left; left; rw [commut₁]; right; left; exact Eq.symm (dne a)
    rw [A₁, commut₂, ident₂, commut₁]
    conv => left; right; rw [commut₁]; left; exact Eq.symm (dne b)
    simp
  . rw [distrib₂]
    conv => left; left; rw [commut₂]
    rw [A₂, commut₁, ident₁]
    rw [commut₂]; conv => left; right; rw [commut₂]
    simp

@[simp]
lemma dm₂ (a b : α) : (a ⊓ b)ᶜ = aᶜ ⊔ bᶜ := by
  symm
  apply cancel <;> simp [dne]
  . rw [commut₂, distrib₁]
    conv => left; left; rw [commut₁]; right; rw [commut₁]
    rw [A₁, commut₂, ident₂]
    rw [commut₁]
    rw [A₁]
  . rw [commut₂, distrib₂]
    conv => left; left; rw [commut₂]; right; left; exact Eq.symm (dne a)
    rw [A₂, commut₁, ident₁]
    rw [commut₂]; conv => left; right; rw [commut₂]; left; exact Eq.symm (dne b)
    rw [A₂]

lemma D₁ (a b c : α) : (a ⊔ (b ⊔ c)) ⊔ aᶜ = u := by
  rw [commut₁]
  conv => left; right; left; exact Eq.symm (dne a)
  simp

lemma E₁ (a b c : α) : b ⊓ (a ⊔ (b ⊔ c)) = b := by rw [distrib₂, absorb₂, commut₁, absorb₁]

lemma E₂ (a b c : α) : b ⊔ (a ⊓ (b ⊓ c)) = b := by rw [distrib₁, absorb₁, commut₂, absorb₂]

lemma F₁ (a b c : α) : (a ⊔ (b ⊔ c)) ⊔ bᶜ = u := by
  calc
    (a ⊔ (b ⊔ c)) ⊔ bᶜ = bᶜ ⊔ (a ⊔ (b ⊔ c)) := by rw [commut₁]
    _                  = u ⊓ (bᶜ ⊔ (a ⊔ (b ⊔ c))) := by rw [commut₂]; simp
    _                  = (b ⊔ bᶜ) ⊓ (bᶜ ⊔ (a ⊔ (b ⊔ c))) := by simp
    _                  = (bᶜ ⊔ b) ⊓ (bᶜ ⊔ (a ⊔ (b ⊔ c))) := by rw [commut₁]
    _                  = bᶜ ⊔ (b ⊓ (a ⊔ (b ⊔ c))) := by rw [distrib₁]
    _                  = bᶜ ⊔ b := by rw [E₁]
    _                  = u := by rw [commut₁]; simp

lemma G₁ (a b c : α) : (a ⊔ (b ⊔ c)) ⊔ cᶜ = u := by
  conv => left; left; right; rw [commut₁]
  apply F₁

lemma H₁ (a b c : α) : (a ⊔ b ⊔ c)ᶜ ⊓ a = z := by
  simp; rw [commut₂]
  calc
    a ⊓ (aᶜ ⊓ bᶜ ⊓ cᶜ) = (a ⊓ (aᶜ ⊓ bᶜ ⊓ cᶜ)) ⊔ z := by rw [ident₁]
    _                  = z ⊔ (a ⊓ (aᶜ ⊓ bᶜ ⊓ cᶜ)) := by rw [commut₁]
    _                  = (a ⊓ aᶜ) ⊔ (a ⊓ (aᶜ ⊓ bᶜ ⊓ cᶜ)) := by rw [compl₂]
    _                  = a ⊓ (aᶜ ⊔ (aᶜ ⊓ bᶜ ⊓ cᶜ)) := by rw [distrib₂]
    _                  = a ⊓ (aᶜ ⊔ (cᶜ ⊓ (aᶜ ⊓ bᶜ))) := by conv => left; right; right; rw [commut₂]
    _                  = a ⊓ aᶜ := by rw [E₂]
    _                  = z := by rw [compl₂]

lemma I₁ (a b c : α) : (a ⊔ b ⊔ c)ᶜ ⊓ b = z := by
  conv => left; left; arg 1; left; rw [commut₁]
  exact H₁ ..

lemma J₁ (a b c : α) : (a ⊔ b ⊔ c)ᶜ ⊓ c = z := by
  simp
  rw [commut₂]
  conv => left; right; rw [commut₂]
  simp

-- Incredibly, these are derivable
@[simp]
lemma assoc₁ (a b c : α) : a ⊔ (b ⊔ c) = (a ⊔ b) ⊔ c := by
  apply cancel; simp
  . calc
      (a ⊔ (b ⊔ c)) ⊔ (aᶜ ⊓ bᶜ ⊓ cᶜ) = ((a ⊔ (b ⊔ c)) ⊔ (aᶜ ⊓ bᶜ)) ⊓ ((a ⊔ (b ⊔ c)) ⊔ cᶜ) := by rw [distrib₁]
      _ = ((a ⊔ (b ⊔ c) ⊔ aᶜ) ⊓ ((a ⊔ (b ⊔ c) ⊔ bᶜ))) ⊓ ((a ⊔ (b ⊔ c)) ⊔ cᶜ) := by rw [distrib₁]
      _ = (u ⊓ u) ⊓ u := by rw [D₁, F₁, G₁]
      _ = u := by simp
  . rw [commut₂]
    rw [distrib₂]; rw [distrib₂]
    calc
      (a ⊔ b ⊔ c)ᶜ ⊓ a ⊔ ((a ⊔ b ⊔ c)ᶜ ⊓ b ⊔ (a ⊔ b ⊔ c)ᶜ ⊓ c) = z ⊔ (z ⊔ z) := by rw [H₁, I₁, J₁]
      _ = z := by repeat rw [ident₁]

-- We don't try to dualize the proof here, that's too painful, we apply de Morgan liberally
@[simp]
lemma assoc₂ (a b c : α) : a ⊓ (b ⊓ c) = (a ⊓ b) ⊓ c := by
  apply inv_elim
  simp

instance ShefferLE : LE α := ⟨ λ a b ↦ a = b ⊓ a ⟩

lemma Sheffer.le_refl (a : α) : a ≤ a := by simp [ShefferLE]

lemma Sheffer.le_trans (a b c : α) : a ≤ b → b ≤ c → a ≤ c := by
  rw [ShefferLE]
  intro h₁ h₂
  calc
    a = b ⊓ a       := h₁
    _ = (c ⊓ b) ⊓ a := by conv => lhs; rw [h₂]
    _ = c ⊓ (b ⊓ a) := Eq.symm (assoc₂ c b a)
    _ = c ⊓ a       := by rw [← h₁]

lemma Sheffer.le_antisymm (a b : α) : a ≤ b → b ≤ a → a = b := by
  simp [ShefferLE]
  intro h₁ h₂
  calc
    a = b ⊓ a := h₁
    _ = a ⊓ b := commut₂ ..
    _ = b     := id (Eq.symm h₂)


instance ShefferToBooleanAlg : BooleanAlgebra α where
  sup := (. ⊔ .)
  le_refl := fun a ↦ Sheffer.le_refl a
  le_trans := fun a b c a_1 a_2 ↦ Sheffer.le_trans a b c a_1 a_2
  le_antisymm := Sheffer.le_antisymm
  le_sup_left := by
    intro a b
    simp only [ShefferLE, Sup.sup]
    rw [commut₂]
    exact Eq.symm (absorb₂ a b)
  le_sup_right := by
    intro a b
    simp only [ShefferLE]
    rw [commut₂, commut₁]
    exact Eq.symm (absorb₂ b a)
  sup_le := by
    intro a b c
    simp only [ShefferLE]
    intro h₁ h₂
    calc
      a ⊔ b = (c ⊓ a) ⊔ b       := by conv => left; left; rw [h₁]
      _     = (c ⊓ a) ⊔ (c ⊓ b) := by conv => left; right; rw [h₂]
      _     = c ⊓ (a ⊔ b)       := Eq.symm (distrib₂ ..)
  inf := (. ⊓ .)
  inf_le_left := by
    intro a b; simp [ShefferLE]
  inf_le_right := by
    intro a b; simp only [ShefferLE]
    calc
      a ⊓ b = a ⊓ (b ⊓ b) := by rw [idemp₂]
      _     = a ⊓ b ⊓ b   := assoc₂ a b b
      _     = b ⊓ a ⊓ b   := by conv => left; left; rw [commut₂]
      _     = b ⊓ (a ⊓ b) := Eq.symm (assoc₂ ..)
  le_inf := by
    intro a b c h₁ h₂
    simp only [ShefferLE]
    calc
      a = b ⊓ a       := h₁
      _ = b ⊓ (c ⊓ a) := by conv => left; right; rw [h₂]
      _ = b ⊓ c ⊓ a  := by exact assoc₂ b c a
  le_sup_inf := by intro a b c; simp; rw [distrib₁]; exact Sheffer.le_refl ..
  top := u
  bot := z
  inf_compl_le_bot := by intro a; simp only [compl₂]; exact Sheffer.le_refl ..
  top_le_sup_compl := by intro a; simp only [compl₁]; exact Sheffer.le_refl ..
  le_top := by intro a; simp only [ShefferLE]; rw [commut₂]; exact Eq.symm (ident₂ a)
  bot_le := by intro a; simp [ShefferLE]

end ShefferLaws

section BooleanToSheffer

variable {α : Type*}
variable [BooleanAlgebra α]

-- This is intentionally not an instance to avoid creating an instance cycle
-- Boolean Algebra -> Sheffer Algebra -> Boolean Algebra.
def BooleanAlgToSheffer : ShefferAlgebra α where
  stroke x y := (x ⊓ y)ᶜ
  elt := ⊥
  sh₁ := by intro a; simp [prime]
  sh₂ := by intro a b; simp [prime]
  sh₃ := by intro a b c; simp [prime]; rw [inf_sup_left]
            conv => left; left; rw [inf_comm]
            conv => left; right; rw [inf_comm]

end BooleanToSheffer
```

# Bits and Bobbles

I need to line profile this thing. It's zippy enough for now, but I'm curious where I'm losing time.

A huge punt in knuckledragger is that I don't have a notion of typeclass or algebraic hierarchy. I've prototyped that a bunch and not liked any of it. Too verbose, too arcane, kind of fishy, non pythonic. I had a latest idea I was kind of intrigued by "declclass"

I should read that mccune et all paper. Seems neat <https://www.cs.unm.edu/~mccune/papers/basax/v12.pdf>

using a regular list for domain specific simp is ok.
I should probably make it so rewrite accepts failure and multiple axioms.

Actually chatgpt's mistakes are kind of interesting.
I _could_ make my proof objects have a call notation to apply them to arguments
Is there any other notation that might be nice?
