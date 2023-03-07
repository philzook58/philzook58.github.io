---
layout: post
title: Lean
---

- [Logic and Mechanical Reasoning](https://avigad.github.io/lamr/) [Logic and Mechanized Reasoning](https://avigad.github.io/lamr/logic_and_mechanized_reasoning.pdf)
- [Theorem proving in lean4](https://leanprover.github.io/theorem_proving_in_lean4/)
- [functional programming in lean](https://leanprover.github.io/functional_programming_in_lean/hello-world.html) Christianson

[Theorem prover lab: applications in programming languages ](https://github.com/IPDSnelting/tba-2021)

[Lambda the Ultimate SSA: Optimizing Functional Programs in SSA](https://arxiv.org/abs/2201.07272)

Numerical packages in lean
- [numlean](https://github.com/arthurpaulino/NumLean)
- [lean karray](https://github.com/lecopivo/lean4-karray)
- https://github.com/lecopivo/SciLean
Webserver example. Custom syntax
https://github.com/leanprover/lean4/blob/master/tests/playground/webserver/Webserver.lean

novice friendly induction tactic
https://arxiv.org/pdf/2012.08990.pdf

metaprogramming framework for formal verification
https://dl.acm.org/doi/pdf/10.1145/3110278

http://leanprover.github.io/papers/lean4.pdf lean4

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
- [MA 208: Proof and Programs ](http://math.iisc.ac.in/~gadgil/proofs-and-programs-2023/index.html)
- [lean learning group](https://www.maths.ed.ac.uk/~pkinnear/leancourse/)
[Aesop (Automated Extensible Search for Obvious Proofs) i](https://github.com/JLimperg/aesop)

[lean for the curious mathmtician 2020](https://github.com/leanprover-community/lftcm2020)


[mathlib 4 docs](https://leanprover-community.github.io/mathlib4_docs/) but also std lib docs

[lean forward](https://lean-forward.github.io/)
[a hitchiker's guide to formal verification](https://lean-forward.github.io/logical-verification/2022/) Still on Lean 3 fyi

[lean update ipam 2023](https://www.youtube.com/watch?v=BY78oZYMGCk&ab_channel=InstituteforPure%26AppliedMathematics%28IPAM%29)

[lean chat](https://github.com/zhangir-azerbayev/lean-chat) openai codex tranlate natural language to lean statements

[](https://proofassistants.stackexchange.com/questions/1964/setting-up-lean-4-on-a-server) https://lean.math.hhu.de/ lean4 web editor
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
[simp tactic](https://github.com/leanprover/lean4/tree/master/src/Lean/Meta/Tactic/Simp)

[discrimination tree](https://github.com/leanprover/lean4/blob/master/src/Lean/Meta/DiscrTree.lean)
[disctree types](https://github.com/leanprover/lean4/blob/master/src/Lean/Meta/DiscrTreeTypes.lean)

[Expr](https://github.com/leanprover/lean4/blob/master/src/Lean/Expr.lean)
# Stuff

```lean
def main := IO.println "hello world"
```

```lean
{% include_relative lean/basics.lean %}
```

```lean
{% include_relative lean/myproject/Myproject.lean %}
```


# Typeclass
```lean
{% include_relative lean/myproject/typeclass.lean %}
```

# IMP
```lean
{% include_relative lean/myproject/IMP.lean %}
```