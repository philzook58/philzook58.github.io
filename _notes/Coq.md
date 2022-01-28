---
layout: post
title: Coq
---

See also:
- Type theory
- Proof theory
- HOTT
- Higher order unification



### Interesting commands
- `Drop` vernacular - srops you into an ocaml toplevel
- [Register](https://coq.github.io/doc/master/refman/proof-engine/vernacular-commands.html#coq:cmd.Register)
- [Primitive] - register an ocaml primitive


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


# misc
- [coq-ceres](https://github.com/Lysxia/coq-ceres) coq sexp stuff
- QED does something serious.
- Surface coq is desugared
- match annnotations are 
- Note that the judgement `a : A, b : B, c : C |- f : F` is sort of getting Coq to accept `Definition foo (a : A) (b : B) (c : C) : F := f.` It sort of reorders the pieces and make you give a name to the whole judgement `foo`. That's an interesting way of looking at it anyway. Of course the more usual way is that `foo` is a function definition.


[Leroy and Appell caonical binary trees](https://github.com/xavierleroy/canonical-binary-tries) 

## Iris
Higher order separation logic. Kind of modelling concurrent ML in Coq I think? 

# Compcert
<https://github.com/AbsInt/CompCert>
[manual](https://compcert.org/man/index.html)
The long form compcert paper seems the most useful 

An interpreter of C. It stops if it hits undefined behavior? That's cool. This seems really useful even for a non verified version

![](https://compcert.org/man/manual001.svg)
C -> Clight -> C#minor -> Cminor -> CminoSel -> RTL -> LTL -> Linear 0> Mach


Individual folders for each architecture. Interesting.

- backend
