---
layout: post
title: Lean
---

- [Logic and Mechanical Reasoning](https://avigad.github.io/lamr/) [Logic and Mechanized Reasoning](https://avigad.github.io/lamr/logic_and_mechanized_reasoning.pdf)
- [Theorem proving in lean4](https://leanprover.github.io/theorem_proving_in_lean4/)
- [functional programming in lean](https://leanprover.github.io/functional_programming_in_lean/hello-world.html) Christianson

[Theorem prover lab: applications in programming languages](https://github.com/IPDSnelting/tba-2021)

[Lambda the Ultimate SSA: Optimizing Functional Programs in SSA](https://arxiv.org/abs/2201.07272)

Numerical packages in lean

- [numlean](https://github.com/arthurpaulino/NumLean)
- [lean karray](https://github.com/lecopivo/lean4-karray)
- <https://github.com/lecopivo/SciLean>
Webserver example. Custom syntax
<https://github.com/leanprover/lean4/blob/master/tests/playground/webserver/Webserver.lean>

novice friendly induction tactic
<https://arxiv.org/pdf/2012.08990.pdf>

metaprogramming framework for formal verification
<https://dl.acm.org/doi/pdf/10.1145/3110278>

<http://leanprover.github.io/papers/lean4.pdf> lean4

"The Lean typeclass resolution procedure can be viewed as a
simple λ-Prolog interpreter [8], where the Horn clauses are the user declared
instances."
That sounds fun

- [lean 4 Advent of Code 2021](https://github.com/alcides/AoC2021Lean4)
- [lean4 raytracer](https://github.com/kmill/lean4-raytracer)
- [balance car](https://github.com/galoisinc/lean4-balance-car)
- [lean 4 talk overview](https://www.youtube.com/watch?v=UeGvhfW1v9M) [second half](https://www.youtube.com/watch?v=vy4JWIiiXSY&ab_channel=leanprovercommunity)

- [lean 4 manual](https://leanprover.github.io/lean4/doc/)
- [lean 3 logic and proof](https://leanprover.github.io/logic_and_proof/)

- [theorme prover lab](https://github.com/IPDSnelting/tba-2022)
- [MA 208: Proof and Programs](http://math.iisc.ac.in/~gadgil/proofs-and-programs-2023/index.html)
- [lean learning group](https://www.maths.ed.ac.uk/~pkinnear/leancourse/)
[Aesop (Automated Extensible Search for Obvious Proofs) i](https://github.com/JLimperg/aesop)

[lean for the curious mathematician 2020](https://github.com/leanprover-community/lftcm2020)

[mathlib 4 docs](https://leanprover-community.github.io/mathlib4_docs/) but also std lib docs

[lean forward](https://lean-forward.github.io/)
[a hitchiker's guide to formal verification](https://lean-forward.github.io/logical-verification/2022/) Still on Lean 3 fyi

[lean update ipam 2023](https://www.youtube.com/watch?v=BY78oZYMGCk&ab_channel=InstituteforPure%26AppliedMathematics%28IPAM%29)

[lean chat](https://github.com/zhangir-azerbayev/lean-chat) openai codex tranlate natural language to lean statements

[](https://proofassistants.stackexchange.com/questions/1964/setting-up-lean-4-on-a-server) <https://lean.math.hhu.de/> lean4 web editor
[lean 4 metaprgramming book](https://github.com/arthurpaulino/lean4-metaprogramming-book)
[metaprogramming in lean 4](https://www.youtube.com/watch?v=hxQ1vvhYN_U&ab_channel=leanprovercommunity)

<https://github.com/yatima-inc> hmm. Lean company?

<https://github.com/search?q=language%3ALean&type=Repositories&ref=advsearch&l=Lean&l=>

[lean 4 tagged stuff on github](https://github.com/topics/lean4)
[makig lean cli tools - arg parsing and whatnot](https://github.com/mhuisi/lean4-cli)
<https://github.com/GaloisInc/reopt-vcg>
<https://github.com/opencompl/lean-mlir>

[do unchained](https://leanprover.github.io/papers/do.pdf) - a description of the extensions to monad syntax like for, break, mut that lean offer

<https://github.com/ccodel/verified-encodings>

[a big twitter thread on lean software verification stuff](https://twitter.com/mukesh_tiwari/status/1667848032128499714?s=12&t=pdj9jytXGvxDOXHWwx4_mg)

[mathematics in lean course](https://github.com/leanprover-community/mathematics_in_lean)
[iris lean](https://github.com/leanprover-community/iris-lean)

[lean 4 hackers](https://agentultra.github.io/lean-4-hackers/)

[lean 4 released](https://news.ycombinator.com/item?id=37429938)

[lean dojo](https://leandojo.org/) LeanDojo: Theorem Proving with Retrieval-Augmented Language Models

[euclidean geometry](https://github.com/jjdishere/EG)

### Build

`elan` tool

`leanpkg`

[`lake`](https://github.com/leanprover/lake) is a new build tool on the horizon. analog of cargo
Making a lake project is a way to get the standard lib?
<https://github.com/leanprover-community/mathlib4/blob/master/lakefile.lean> mathlib4 lakefile

```lake
require std from git "https://github.com/leanprover/std4" @ "main"
require Qq from git "https://github.com/gebner/quote4" @ "master"
require aesop from git "https://github.com/JLimperg/aesop" @ "master
```

Using nix is kind of a pain. I haven't done it.

Ah. I need to open my lake project in it's own window for vscode to work right resolving paths. That is weird. Hmm.

LEAN_PATH for libraries? Probably I'm fighting the Lake experience which is bad.

`[@inline]`
`[@reduced]`
`[@simp]`

# Lean Src

<https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html> prelude is interesting

[simp tactic](https://github.com/leanprover/lean4/tree/master/src/Lean/Meta/Tactic/Simp)

[discrimination tree](https://github.com/leanprover/lean4/blob/master/src/Lean/Meta/DiscrTree.lean)
[disctree types](https://github.com/leanprover/lean4/blob/master/src/Lean/Meta/DiscrTreeTypes.lean)

[Expr](https://github.com/leanprover/lean4/blob/master/src/Lean/Expr.lean)

IR - somehow this is what I need to look at to implement new backend?

# Stuff

```bash
echo '
def main := IO.println "hello world"
' > /tmp/test.lean
lean --run /tmp/test.lean

```

```lean
def main := IO.println "hello world"

#eval 1 + 1 -- it's a nat
#eval String.append "hello" "world"
#eval if 1 > 2 then "yes" else "no"
#eval (1 + 1 : Int)

/- block comment -/
def hello := "hello"
def Str : Type := String

abbrev N : Type := Nat
#check 1.2

structure Point where
  x : Float
  y : Float
deriving Repr

#check ({x := 1, y := 2} : Point)

inductive MyBool where
  | MyTrue : MyBool
  | MyFalse : MyBool

#check MyBool.MyTrue

#eval Lean.versionString

#check fun (x : Nat) => x
#check λ x => x
#eval let y := 2; y + y

theorem foo : p -> q -> p /\ q :=
  by intros x y
     apply And.intro
     apply x
     apply y
     done

inductive aexp where
    | Plus : aexp -> aexp -> aexp
    | Lit : Nat -> aexp

-- dot notation to go into aexp scope
def interp : aexp -> Nat
    | .Plus x y => interp x + interp y
    | .Lit n => n

#eval interp (aexp.Plus (aexp.Lit 4) (aexp.Lit 3))

#check (("a",1) : Prod String Nat )
#eval (1,(2,34,5)) == (1,2,34,5)


#print axioms Nat.add_comm

#eval ! true || (false && true)
--example : True := by
--    decide
```

```lean
{% include_relative lean/myproject/Myproject.lean %}
```

```lean
{% include_relative lean/myproject/leanlog.lean %}
```

```lean
-- Brzowksisksis derivatives for regex
-- https://www.ccs.neu.edu/home/turon/re-deriv.pdf
inductive regex where
    | empty : regex
    | eps : regex -- empty string
    | lit : Char -> regex
    | seq : regex -> regex -> regex
    | and : regex -> regex -> regex
    | star : regex -> regex

#check regex.lit 'a'

def null : regex -> regex
    | .empty => .empty
    | .eps => .eps
    | .lit _ => .eps
    | .seq a b => .and (null a) (null b)
    | .and a b => .and (null a) (null b)
    | .star _ => .eps

def deriv a 
    | .empty => .empty
    | .eps => .eps
    | .lit b => if a == b then .eps else .empty 
    | .seq a' b => .alt (.seq (deriv a a') b) (.seq a' (deriv a b))
    | .and a b => .and (null a) (null b)
    | .star _ => .eps
def main : IO Unit := pure ()
```

# Typeclass

```lean
{% include_relative lean/myproject/typeclass.lean %}
```

# IMP

```lean
{% include_relative lean/myproject/IMP.lean %}
```
