---
layout: post
title: Coq
---

- [Coq is Normal](#coq-is-normal)
    - [Interesting commands](#interesting-commands)
  - [Inductive Types](#inductive-types)
  - [Coinductive Types](#coinductive-types)
  - [Reflection](#reflection)
  - [What are Proofs](#what-are-proofs)
    - [match annotations](#match-annotations)
- [Kernel](#kernel)
  - [VM](#vm)
- [Ocaml](#ocaml)
- [Plugins](#plugins)
- [Iris](#iris)
- [SSReflect](#ssreflect)
- [Stdlibs](#stdlibs)
- [Prolog](#prolog)
- [Compcert](#compcert)
  - [Coq hackthan 2022](#coq-hackthan-2022)
  - [dune](#dune)
- [Examples](#examples)
- [Misc](#misc)

See also:
- Type theory
- Proof theory
- HOTT
- Higher order unification

# Coq is Normal
Coq has all sorts of crazy stuff in it, but the core of it can be used as a normal-ish functional programming language.

See my [Coq in Y Minutes tutorial](https://learnxinyminutes.com/docs/coq/)

[Cody's intro to coq](https://www.youtube.com/watch?v=5e7UdWzITyQ) https://github.com/codyroux/broad-coq-tutorial

```coq
Inductive weekday :=
 | monday
 | tuesday.
```

### Interesting commands
- `Drop` vernacular - srops you into an ocaml toplevel
- [Register](https://coq.github.io/doc/master/refman/proof-engine/vernacular-commands.html#coq:cmd.Register) making names accessible to ocaml
- [Primitive] - register an ocaml primitive
- [`Show`](https://coq.inria.fr/refman/proofs/writing-proofs/proof-mode.html#requesting-information) gives infromation during proof. `Show Proof` shows intermediate stuff.
- `Search`. Very important. Lots of features.

## Inductive Types
Inductive types are prolog

Eliminators and pattern matching

What should be primitive anyway?

## Coinductive Types


## Reflection
You can use domain specific ADTs to describe a class of problems. You can use coq as an ordinary programming language


## What are Proofs

### match annotations
The `as` annotation is a realtive of the ocaml `as` annotation. It is a binding form.
Likewise for the `in` annotation. This is a pattern matching annotation that binds pattern variables. The scope of the bindings is only over the return clause of the match.
These annotations bring the match closer or exactly equivalent to the "recursor" formulation of pattern matching. This is a higher order function that you give a function specify what to do in each case. In the dependent context, you also give it a return type function.

In any sense does this 

# Kernel

## VM
There is a coq vm with a bytecode. The instructions are defined [here](https://github.com/coq/coq/blob/master/kernel/vmbytecodes.mli)

Is this bytecode interpreter described anywhere?

Cody suggests Benjamin Gregoire

Sometimes is feels like cody knows a lot
<https://cstheory.stackexchange.com/questions/18777/is-compiler-for-dependent-type-much-harder-than-an-intepreter>
[leroy gergoire paper bytecode interpreter](https://xavierleroy.org/publi/strong-reduction.pdf)
[full reduction at full throttle](https://hal.inria.fr/file/index/docid/650940/filename/full_throttle.pdf)
# Ocaml
There are plugin tutorials
Coq is available as a library. coq-core. Note the Ocam API documentation https://coq.github.io/doc/

- [coq-simple-io](https://github.com/Lysxia/coq-simple-io)
- [coqffi](https://github.com/coq-community/coqffi) generates ffi boilerplate for ocaml functions

# Plugins
[plugin tutorials](https://github.com/coq/coq/tree/master/doc/plugin_tutorial)

.mlg files huh? Those are weird
I don't know that any of this is documented except in these tutorials

coqpp is the tool that turns .mlg into .ml files



# Iris
Higher order separation logic. Kind of modelling concurrent ML in Coq I think? 

# SSReflect
SSReflect emphasizes proof by reflection. It is a really succinct inscrutable looking syntax.



# Stdlibs

# Prolog

```coq


```


# Compcert
<https://github.com/AbsInt/CompCert>
[manual](https://compcert.org/man/index.html)
The long form compcert paper seems the most useful 

An interpreter of C. It stops if it hits undefined behavior? That's cool. This seems really useful even for a non verified version

![](https://compcert.org/man/manual001.svg)
C -> Clight -> C#minor -> Cminor -> CminoSel -> RTL -> LTL -> Linear 0> Mach


Individual folders for each architecture. Interesting.

- backend


## Coq hackthan 2022
https://github.com/coq/coq/tree/master/dev/doc
https://github.com/coq/coq/wiki/DevelSetup coq devel setup


- dev helpful information and scripts
- kernel
- interp
- vernac - all sorts of files implementing vernacular commands fixpoint, indcutive, define search etc
- tactics - ocaml code implementing some built in tactics like auto, autorewrite,
- pretyping? Is this elaboration from surface syntax to kernel.
- plugins - some native plugins are implemented. Extraction, btauto. Possibly a good place to look if you want to implement your own plguin. ssr. ring. micromega, ltac, ltac2
- kernel. I'll try to list these in a dependency order
  + names.ml
  + univ.ml
  + sorts.ml
  + constr.ml - internal syntax of terms. "constructions" 
  + native*.ml stuff related to native compilation to ocaml for normalization
  + 

- testuite
- ide - coq ide
- boot

types
- constr
- unsafe_judgement
- evar_map
- glob_constr
- 

You can build coq using dune
make -f Makefile.dune

https://github.com/ejgallego/coq/tree/simple_compiler

stm

parse
resolution of names
interpret
type inferrance


compiler/scoq.c
vernac com* are implementationso f that vernac
vernacexpr.ml vernac as
VerancExtend constructor is where extension points hook in

using serapi to probe coq ast
camlp5
mlg files. you can find them in _build
vernacentires - interpeter out of vernac
vernacextend.mli  a typed dsl for vernac
vernax_interp
vernac_state
declare.mli

Wehen you do a lemma
Proof_info
interp/Constrintern first step of elbation

interp/constrr_expr is surface syntax of coq terms.
pretyping/glob_contr globalized /internalized term name resolution applied
pretyping.mli type inferrence
pretyping/understand_tcc is an important entry point?

evar_map

gramlib?

pretypinggggggggg
evarconv.mli what is this?


libraries
coq_checklib
bool
clib
config
coqpp
top printer
engine 0 actual proof engine
gramlib
interp
kernel
lib
library
parsing
parsing
pretypng
printing
parsing
proofs legacy
sysinti
tactics
tactics
vernac


engine is 2 compoenents in one. pconstr e

https://github.com/ejgallego/coq-serapi/blob/v8.13/FAQ.md#how-many-asts-does-coq-have

## dune
make problmatic

couple of pointers
- build systems a la carte
- podcast about build systems by andrey

language agnostic
language secpfic rules
in dunesrc
dep.mli
memo.mli - memo is important huh. Build monad 
src/dune_rules

1. scan all stanzas
2. build virtual view of file system
3. setup rule
4. build a target

(coq.theory


)

1. we detect dune file with (coq.theory
2. extract generated files
3. setup rules, informrm the build enginer about what _net targets_ are in scope

# Examples

```coq
{% include_relative coq/test.v %}
```

Equality eliminator is rewriting.
```coq

```

# Misc
[](https://github.com/stepchowfun/proofs/tree/main/proofs)
https://github.com/stepchowfun/proofs/blob/main/proofs/Tutorial/Lesson5_Consistency.v in particular

https://github.com/dwarfmaster/commutative-diagrams tactic for categroy proofs

- [coq-ceres](https://github.com/Lysxia/coq-ceres) coq sexp stuff
- QED does something serious.
- Surface coq is desugared
- match annnotations are 
- Note that the judgement `a : A, b : B, c : C |- f : F` is sort of getting Coq to accept `Definition foo (a : A) (b : B) (c : C) : F := f.` It sort of reorders the pieces and make you give a name to the whole judgement `foo`. That's an interesting way of looking at it anyway. Of course the more usual way is that `foo` is a function definition.


[Leroy and Appell caonical binary trees](https://github.com/xavierleroy/canonical-binary-tries) 

[autosubst](https://github.com/coq-community/autosubst)
VCFloat
gappa
flocq
mathematical components
coq platform

[Verified software Toolchain](https://vst.cs.princeton.edu/) higher order separation logic for C
[certigraph](https://github.com/CertiGraph/CertiGraph) graph manipulation programs
[certigc](https://github.com/CertiGraph/CertiGC) verified garbage collector

[Axioms to consider enabling](https://github.com/coq/coq/wiki/CoqAndAxioms)

[ringer pluin tutorial](https://github.com/tlringer/plugin-tutorial)
[talia ringer thesis](https://homes.cs.washington.edu/~djg/theses/ringer_dissertation.pdf) really good explanations

[Modular pre-processing for automated reasoning in dependent type theory](https://arxiv.org/abs/2204.02643) processing for smtcoq
[The pro-PER meaning of "proper"](https://blog.poisson.chat/posts/2022-04-07-pro-per-proper.html)

[magmide](https://github.com/magmide/magmide)

[rewriter](https://github.com/mit-plv/rewriter)

[Discrete Math in Coq](https://cs.pomona.edu/~michael/courses/csci054s18/book/)

[](https://github.com/rikosellic/ZFC-prover-in-Coq)

[metamatix](https://github.com/acorrenson/metamatix) verified implementatyion of metamath checker
https://github.com/acorrenson/WiSE - verified bug finding
https://github.com/acorrenson/minilog - verified implementation of mini prolog

[defaultt](https://github.com/acorrenson/Defaultt) - default logic

https://github.com/acorrenson/SATurne