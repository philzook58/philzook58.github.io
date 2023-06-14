---
layout: post
title: Ocaml
tags: ocaml
description: my notes about ocaml
---

- [Beginner Material](#beginner-material)
- [Ocaml Guts](#ocaml-guts)
  - [Runtime](#runtime)
    - [Calling Conventions](#calling-conventions)
    - [Exceptions](#exceptions)
    - [The Zinc Abstract Machine (ZAM)](#the-zinc-abstract-machine-zam)
  - [Compiler](#compiler)
- [Ecosystem](#ecosystem)
  - [Debugging](#debugging)
  - [Stdlib](#stdlib)
    - [Obj module](#obj-module)
  - [Multicore](#multicore)
    - [Domains](#domains)
    - [Effects](#effects)
  - [MetaOcaml](#metaocaml)
  - [PPX](#ppx)
  - [Build System](#build-system)
    - [META vs dune vs opam files](#meta-vs-dune-vs-opam-files)
  - [Js\_of\_ocaml](#js_of_ocaml)
    - [WASM](#wasm)
- [Language Features](#language-features)
  - [Object System](#object-system)
    - [Row polymorphism](#row-polymorphism)
  - [Open Recursion](#open-recursion)
  - [Recursive Modules](#recursive-modules)
  - [Extensible Variants](#extensible-variants)
  - [Extensible Functions](#extensible-functions)
  - [Universal Types](#universal-types)
  - [Extensible Records](#extensible-records)
  - [Modules](#modules)
    - [Modules vs Typeclasses](#modules-vs-typeclasses)
  - [First Class Modules](#first-class-modules)
  - [Higher Kinded Polymorphism](#higher-kinded-polymorphism)
  - [GADTs](#gadts)
  - [Registries](#registries)
  - [Typelevel programming](#typelevel-programming)
- [Standard ML](#standard-ml)
- [Misc Resources](#misc-resources)

# Beginner Material
Sometimes there are too many links. These three are really the best IMO.
- <https://cs3110.github.io/textbook/cover.html>
- <https://dev.realworldocaml.org/>
- <https://ocaml.org/manual/>

[Install](https://ocaml.org/docs/install.html): Get opam. Use opam. It's really good. It installs the compiler and packages

I use the ocaml platform vs-code plugin.

Use [dune](https://dune.build/). It is a build system for projects.

Supplementary material
- https://johnwhitington.net/ocamlfromtheverybeginning/
- https://ocaml.org/learn/tutorials/
- https://learnxinyminutes.com/docs/ocaml/
- https://ocaml-sf.org/learn-ocaml-public/
- https://ocamlverse.github.io/content/learning.html
- https://www.philipzucker.com/notes-on-getting-started-in-ocaml/


# Ocaml Guts
## Runtime

You can easily examine the ocaml assembly in <https://godbolt.org/>
[About unboxed float arrays](https://www.lexifi.com/blog/ocaml/about-unboxed-float-arrays/)
[floatarray migration](https://www.lexifi.com/blog/ocaml/floatarray-migration/)
Float arrays have a special representation. It is an odd choice given how uniform representation is generally.
He mentions that lazy has an optimization - when gc runs it removes the indirection of the lazy value. Is this compiler intrinsic? Yes.
<https://stackoverflow.com/questions/56746374/how-does-ocaml-represent-lazy-values-at-runtime>

local variables can be unboxed. However what counts as local? Even arithmetic operations are functions. So this relies on inlining?

I have heard that ocaml is a typed scheme in a sense. 

-nodynlink removes the disconcerting GOT table stuff.



caml<Modulename>__entry I would guess is what gets called when the module is loaded

There is a bit of data called camlModule. The entry code fills in toplevel definitions into this table.

I am not sure what causes mangled versus unmangled names. Somethings are statically built and stored as symbols. The things that can't have their string definition stored at the bottom in `.ascii` fields
The labels at the bottom are connected to the strings at the bottom. I don't know what the clacuatins they are doing are


There are closures that don't have to capture anything. I think those are the __1 __2 __3 things at the top. The environment packing is ` .quad   0x100000000000005` which is some kind of null value?

frametable - for the GC to understand the stack

Hey [@@ocaml.unboxed] actually works. That's cool

A static linked list is just right there. That's neat.
`[0;3;4;5;7]`
```
camlExample__6:
        .quad   1
        .quad   camlExample__5
camlExample__5:
        .quad   7
        .quad   camlExample__4
camlExample__4:
        .quad   9
        .quad   camlExample__3
camlExample__3:
        .quad   11
        .quad   camlExample__2
camlExample__2:
        .quad   15
        .quad   1
```
Hmm. The Nil is represented as 1. Does that make sense?

Integers are 2*n + 1

Inspecting bytecode in a jupyter notebook:
```python
import subprocess
import tempfile
def bytecode(code):
    fp = tempfile.NamedTemporaryFile(prefix="my_module_",suffix='.ml', delete=False)
    fp.write(code.encode())
    name = fp.name
    fp.close()
    print(subprocess.run(["ocamlc", "-dlambda", "-dinstr", "-dcamlprimc", name], capture_output=True).stderr.decode())

bytecode('''
let () = print_endline "hello world"
''')
```
### Calling Conventions
r15 is the minor heap, so adjustments to it are allocations
r14 is a pointer to the Ocaml_state structure [domain state after multicore?](https://github.com/ocaml/ocaml/blob/trunk/runtime/caml/domain_state.tbl)
8(%r14) looks like the heap end information, which triggers a GC
[Conventions here](https://github.com/ocaml/ocaml/blob/trunk/asmcomp/amd64/proc.ml)

[ocaml calling conentions stack overflow](https://stackoverflow.com/questions/11322163/ocaml-calling-convention-is-this-an-accurate-summary) ocaml calling conventions. To quote:
The first 10 integer and pointer arguments are passed in the registers rax, rbx, rdi, rsi, rdx, rcx, r8, r9, r10 and r11
The first 10 floating-point arguments are passed in the registers xmm0 - xmm9
Additional arguments are pushed onto the stack (leftmost-first-in?), floats and ints and pointers intermixed
The trap pointer (see Exceptions below) is passed in r14
The allocation pointer (presumably for the minor heap as described in this blog post) is passed in r15 <https://rwmj.wordpress.com/2009/08/06/ocaml-internals-part-3-the-minor-heap/>
The return value is passed back in rax if it is an integer or pointer, and in xmm0 if it is a float
All registers are caller-save?

### Exceptions
How do they work ata low level?

### The Zinc Abstract Machine (ZAM)
See chapter 2 of ZINC report
Also [From Krivine’s machine to the Caml implementations by Leroy](https://xavierleroy.org/talks/zam-kazam05.pdf)
ZAM1 - Accumulator, argument stack, environment, return stack 

- `Access(n)` - nth thing in env
- 

Dynamic vs persistent part of environment - stack vs heap

ZAM2 - argument and return stack fused. I feel like Dolan was talking about this as being a useful distinction though

push enter - callee receives more or less  push arguments on the stack with marks. over application, underapplication and just right. as seperate dynamic cases
eval-apply - callee receives eactly as many arguments - caller responsible for the differnece.

Wait, so `apply :: Closure -> Arguments -> `?


But this talk is 15 years old. 

[Caml Virtual Machine Instruction Set](http://cadmium.x9c.fr/distrib/caml-instructions.pdf). ocaml 3.11. closer to modern

## Compiler
[A beginners guide to OCaml internals](https://rwmj.wordpress.com/2009/08/04/ocaml-internals/)
[OCaml compiler design and development](https://discuss.ocaml.org/t/ocaml-compiler-design-and-development/5823/4)

The main internal IRs?
- parsetree
- typetree
- lambda
- clambda
- cmm
- mach
- linear

<https://dev.realworldocaml.org/compiler-frontend.html#an-overview-of-the-toolchain>

Let's go backwards.
Native code:
[runtime](https://github.com/ocaml/ocaml/tree/trunk/runtime)
 - main.c `main` calls `caml_main`
 - startup_nat.c  `caml_main` work upto file, the meat happens at `caml_start_program(Caml_state);`
 - `caml_start_program` is in assembly file. It saves registers and stuff and calls `caml_program` 
   which switches over to compiled program code

let max_arguments_for_tailcalls = 10 (* in regs *) + 64 (* in domain state *)

(* C calling conventions under Unix:
     first integer args in rdi, rsi, rdx, rcx, r8, r9
     first float args in xmm0 ... xmm7
     remaining args on stack
     return value in rax or xmm0.
  C calling conventions under Win64:
     first integer args in rcx, rdx, r8, r9
     first float args in xmm0 ... xmm3
     each integer arg consumes a float reg, and conversely
     remaining args on stack
     always 32 bytes reserved at bottom of stack.
     Return value in rax or xmm0. *)

Backends. Both of these receive lambda 
- [asmcomp folder](https://github.com/ocaml/ocaml/tree/trunk/asmcomp)
- [bytecomp folder](https://github.com/ocaml/ocaml/tree/trunk/bytecomp) bytecode compiler backend
    + bytecode insutructions


- [The C bytecode interpreter](https://github.com/ocaml/ocaml/blob/trunk/runtime/interp.c) Interesting. They pre pick a register often for PC and SP.

```
(* Abstract machine instructions *)

type label = int                        (* Symbolic code labels *)

type instruction =
    Klabel of label
  | Kacc of int
  | Kenvacc of int
  | Kpush
  | Kpop of int
  | Kassign of int
  | Kpush_retaddr of label
  | Kapply of int                       (* number of arguments *)
  | Kappterm of int * int               (* number of arguments, slot size *)
  | Kreturn of int                      (* slot size *)
  | Krestart
  | Kgrab of int                        (* number of arguments *)
  | Kclosure of label * int
  | Kclosurerec of label list * int
  | Koffsetclosure of int
  | Kgetglobal of Ident.t
  | Ksetglobal of Ident.t
  | Kconst of structured_constant
  | Kmakeblock of int * int             (* size, tag *)
  | Kmakefloatblock of int
  | Kgetfield of int
  | Ksetfield of int
  | Kgetfloatfield of int
  | Ksetfloatfield of int
  | Kvectlength
  | Kgetvectitem
  | Ksetvectitem
  | Kgetstringchar
  | Kgetbyteschar
  | Ksetbyteschar
  | Kbranch of label
  | Kbranchif of label
  | Kbranchifnot of label
  | Kstrictbranchif of label
  | Kstrictbranchifnot of label
  | Kswitch of label array * label array
  | Kboolnot
  | Kpushtrap of label
  | Kpoptrap
  | Kraise of raise_kind
  | Kcheck_signals
  | Kccall of string * int
  | Knegint | Kaddint | Ksubint | Kmulint | Kdivint | Kmodint
  | Kandint | Korint | Kxorint | Klslint | Klsrint | Kasrint
  | Kintcomp of integer_comparison
  | Koffsetint of int
  | Koffsetref of int
  | Kisint
  | Kisout
  | Kgetmethod
  | Kgetpubmet of int
  | Kgetdynmet
  | Kevent of debug_event
  | Kperform
  | Kresume
  | Kresumeterm of int
  | Kreperformterm of int
  | Kstop
```

- lambda. 
  + matching.mli compiels pattern matches. Very complex
  + tail call modulo optimization - opt in? Is it this https://jamesrwilcox.com/tail-mod-cons.html ? https://arxiv.org/abs/2102.09823
  +https://github.com/ocaml/ocaml/blob/trunk/lambda/translprim.ml primitives

- [file formats](https://github.com/ocaml/ocaml/tree/trunk/file_formats)
 + remarkably simple to see the types of a compilation unit

- typing
 + <https://github.com/ocaml/ocaml/blob/trunk/typing/HACKING.adoc>


Zinc report mentions tha some objects you can statically allocate for in the data section of the binary. This does seem to be the case. Somehow the garbage collector knows not to try to collect these.


Backends

```ocaml
#use "topfind";;
#require "ocaml-compiler-libs.optcomp ctypes.foreign ctypes.top";; 
(* let rax = X86_ast.RAX *)

(* https://ocaml.org/p/ocaml-base-compiler/4.12.1/doc/X86_ast/index.html 
   https://ocaml.org/p/ocaml-base-compiler/4.12.1/doc/X86_dsl/index.html
*)


let print_asm = Ocaml_optcomp.X86_gas.generate_asm Out_channel.stdout
let () = 
let open Ocaml_optcomp.X86_dsl in 
print_asm [
  Comment "Look ma! I'm generatin asm!";
  Global "myfun";
  NewLabel ("myfun", PROC);
  Ins (MOV (rax, int 42));
  Ins RET
  ] 

(* https://github.com/yallop/ocaml-ctypes/wiki/ctypes-tutorial *)
let myfun = 
  let open Ctypes in 
  foreign "myfun" (int @-> returning int)




```
# Ecosystem 

## Debugging
ocamldebug is nice for bytecode debugging

https://ocaml.org/meetings/ocaml/2012/slides/oud2012-paper5-slides.pdf
objdump -t the symbols. The  module entrypoint is probably something like `camlMyModule__entry` You can set a breakpoint there.

[comments on using perf](https://discuss.ocaml.org/t/ann-perf-demangling-of-ocaml-symbols-a-short-introduction-to-perf/7143/5)
## Stdlib
### Obj module
The obj module holds all kinds of nasty introspective goodies. Possibly physical equality `=` deserves to be in here too.
## Multicore
[WIki](https://github.com/ocaml-multicore/ocaml-multicore/wiki) links to papers, discussions and videos

[Parallel Programming in Multicore OCaml](https://github.com/ocaml-multicore/parallel-programming-in-multicore-ocaml)
[a memory model for multicore ocaml](https://kcsrk.info/papers/memory_model_ocaml17.pdf)
[bounding data races in space and time](https://kcsrk.info/papers/pldi18-memory.pdf)
 Interesting formalization of shared memory.

[a tutorial on parallel programming in ocaml 5](https://discuss.ocaml.org/t/a-tutorial-on-parallel-programming-in-ocaml-5/9896)
### Domains
For parallelism not concurrency
Uses system threads. You don't want more domains than cores
Task pools

### Effects
- See also note on continuations and effects
Algebraic effects - related to delimitted continuations
For concurrency, not parallelism

[PLDI talk](https://pldi21.sigplan.org/details/pldi-2021-papers/14/Retrofitting-Effect-Handlers-onto-OCaml) 
[paper](https://arxiv.org/pdf/2104.00250.pdf)
[effect examples](https://github.com/ocaml-multicore/effects-examples)
[Concurrent system programing with effect handlers paper]

OS threads are heavyweight.
async/await, generators, coroutines.
Current method of concurrency - Lwt and Async. Callback oriented with monad syntax. no backtraces, no exceptions, too many closures
- similar languages - go goroutines and ghc hackell thread - lightweight threads

effect handlers, plotkin et al 2009, modular basis of non-local control flow mechaism ~ similar to first class resumable exceptions

```ocaml
effect E : string
let comp () = print_endline (perform E)

let main () = try comp () with
   | effect E k -> continue k "2"
```


Is mechanically it similar to throwing expectins holding callback functions?

When you enter `try`, a new fiber stack is created. It has a pointer to it's parent stack. Starts small (32 words) and dynamically grown. At perform, create cotinuation. This is small, bring ourselfs back up to parent frame.
One shot continations. No frame copying necessary. The pointer back to the fiber frame is nulled once used.
multi shot continuation via explicit copying
Hanlders can be nested. Linear search through handler stack. 

Light threading
```ocaml
effect Fork : (unit -> unit) -> unit
effect Yield : unit
```

The arguemnts to effects are given when performed
The result of the effect is given when continue

You can overload exceptions in match? Huh.

Generators
Can be derived from iterator


Linearity. You canleak resources in legacy code. assume captured continuations are linearly used

backtraces - dwarf stack unwinding support. gdb perf, libunwind.
bespoke swarf bytecode for unwiding across fibers. They used stephen kell's dwarf verifier. That's cool

static semantics - no effect safety. no static gurantee all effects ar handled
effect system - eff link koka, helium
effectiv ocaml - ocaml becomes pure?

dynamic semantics - cek machine. Why? stack layout is complicated.
system stack - where C is executed. fiber 1 is main ocaml. 
ocaml and c functions as different kinds of lambdas. Huh.
"because a cek machine terms are expressions or values" Hmm.
stacks are C stack or ocaml stack

Cancellation contexts from F#
clone_continuation is multi shot.  In Obj module.
"what color is your function" Function color is a concept? This design explicitly avoids this. Generator in javascript are "colored" different
loom conitnuations



## MetaOcaml
See note on:
 - partial evaluaton.

What do the metaocaml patches look like?

[Meta ocaml bibliography](https://github.com/metaocaml/metaocaml-bibliography)


offshoring https://okmij.org/ftp/meta-programming/tutorial/genc.html

cross stage persistance

## PPX
PPX is a preprocessing stage. You get access to the ocaml syntax tree and can modify it

<http://ocamlverse.net/content/metaprogramming.html>



- ppx_sexp is by far the most useful one
- https://opam.ocaml.org/packages/ppx_jane/ ppx_jane has a nice list
- ppx_expect cool for writing tests
- https://github.com/fdopen/ppx_cstubs  helpers for FFI
- string interpolation


```ocaml
#use "topfind";;
#require "ppx_jane";;

let () = print_endline [%string "%{1 + 2 # Int}"]

```


## Build System

I wrote a bit about cma vs cmo files vs cmx files here <https://www.philipzucker.com/bap-js-1/>

I have used dune for a long time. It's great. It's so good that I've never really worked with the raw ocaml build system. This is bad. Stuff doesn't always go right, so it's good to know how things work.

All the ocaml tools: <https://ocaml.org/manual/comp.html>
- ocamlc - batch compiler
- ocaml - a repl
- ocamlrun - runtime system (for bytecode output)
- ocamldep 
- 


ocamlc takes many kind of arguments and does things based on their file suffix
ocamlc needs to take in the modules in their topological order. If you try out of order it will fail

-linkall What is it.

ocamlc main.ml -> main.cmi, main.cmo, a.out
a.out is a bytecode executable. `file` reveals it runs ocamlrun. `head a.out` shows a hash bang for ocamlrun 

ocamlfind, META files. <http://projects.camlcity.org/projects/dl/findlib-1.9.1/doc/guide-html/c74.html>
- `ocamlfind list` all known packages
- `ocamlfind query` 
- `ocamlfind ocamlc -package foo` will add the appropriate includes to ocamlc `-linkpkg` adds also the file names
https://discuss.ocaml.org/t/cmo-specification/4112 cmo file format

ocamlopt main.ml -> main.cmx main.

`-i` print all defined things.
`-S` output assembly

https://ocsigen.org/js_of_ocaml/2.5/manual/overview
js_of_ocaml - i really needed to output it with main.bytes? No no. I needed to give it the byte _exectuable_. This is the result of the ocamlc compiler

<https://www.ocamlpro.com/2021/09/02/generating-static-and-portable-executables-with-ocaml/>


https://github.com/dinosaure/gilbraltar mirageos on pi4

<https://twitter.com/wengshiwei/status/1454128911219003393?s=12> an explanation of the z3 bindings problems and linking diagrams
### META vs dune vs opam files

## Js_of_ocaml
Js_of_ocaml is a compiler from ocaml bytecode to javascript.

### WASM
[state of webassembly](https://discuss.ocaml.org/t/state-of-ocaml-and-web-assembly/2725) some interesting stuff here. emscripten build of C bytecode interpreter. cmm_of_wasm uses ocaml itself as a wasm backend
[ocaml-wasm](https://github.com/corwin-of-amber/ocaml-wasm/tree/wasm-4.11)
[ocaml-to-wasm-overview](https://github.com/sabine/ocaml-to-wasm-overview)

# Language Features

## Object System
Not particularly highly recommended but it puts the O in ocaml.

Objects add subtyping to ocaml. So do polymorphic variants though. And in asense, polymorphism has a subtyping of "more general than"

[ocaml objects](https://roscidus.com/blog/blog/2013/09/28/ocaml-objects/)
[mixins](https://www.lexifi.com/blog/ocaml/mixin/)

[Objective ML: An effective object-oriented extension to ML - 98](https://caml.inria.fr/pub/papers/remy_vouillon-objective_ml-tapos98.pdf)
[Simple Type Inference for Structural Polymorphism ](https://caml.inria.fr/pub/papers/garrigue-structural_poly-fool02.pdf)
### Row polymorphism
[Ivan's answer](https://stackoverflow.com/questions/48092739/what-are-row-types-are-they-algebraic-data-types)
[Advaced Functional Programming notes 2014 - yallop ](https://www.cl.cam.ac.uk/teaching/1415/L28/rows.pdf)
[A Polymorphic Type System for Extensible Records and Variants ](http://www.cs.cmu.edu/~aldrich/courses/819/papers/row-poly.pdf)
[objects and aspects krishnaswami](https://www.cs.cmu.edu/~aldrich/courses/819/slides/rows.pdf)

## Open Recursion
This somewhat is related to objects. `self` is a late bound variable that can be overridden. You can emulate this by having base classes take in later classes as an argument.
Related to the fix form of recursion?
Landin's knot?


[Open Recursion with Modules](https://blag.bcc32.com/shenanigans/2019/07/15/open-recursion-with-modules/)
[](https://whitequark.org/blog/2014/04/16/a-guide-to-extension-points-in-ocaml/)
[Ralk Hinze Close and Open](https://www.cs.ox.ac.uk/people/ralf.hinze/talks/Open.pdf)
[Nystrom - What is “Open Recursion”?](http://journal.stuffwithstuff.com/2013/08/26/what-is-open-recursion/)
## Recursive Modules
https://blog.janestreet.com/a-trick-recursive-modules-from-recursive-signatures/
https://lesleylai.info/en/recursive_modules_in_ocaml/
Manual section

## Extensible Variants
Extensible variants allow you to add new constructors to a data type kind of imperatively. They let data types be open. They are a strong relative of exceptions in ocaml (maybe even the same thing now) which have let you add new exception cases for a long time.
They give a new axis upon which to consider data type definitions problems. Ordinary data types are closed in Ocaml. It is easy enough to check for pattern matching coverage because of that. Going Finally Tagless is a classic technique for achieving a kind of open-ness to the data type.

They are distinct from [polymorphic variants](https://dev.realworldocaml.org/variants.html#scrollNav-4). This is a point that has confused me in the past, although not any more! They are actually pretty different. Wait. Are they that different?

It is extra intriguing or bizarre that they can be GADTs. Because of this, they can be used as type witnesses of various flavors which facilitates a kind of dependently typed programming and/or heterogenous data structures.

Using the first class module system, you can also dynamically add new cases as runtime. How crazy is that!

Basic type witnesses

```ocaml
type _ ty = ..
type _ ty += Int : int ty
type _ ty += Bool : bool ty
type _ ty += List : 'a ty -> 'a list ty
```

<https://okmij.org/ftp/ML/trep.ml> - Oleg Kiselyov describing this technqiue

You can build a heterogenous data structure by packing together with it's type witness
```ocaml
type univ = {ty : 'a ty; x : 'a}
type hlist = univ list

let example : hlist = [ {ty = Int; x = 3}; {ty = Bool; x = true} ]
```

You can similarly build dictionaries and such.

<https://inbox.ocaml.org/caml-list/CALdWJ+wpwafYOddNYhTFY5Zz02k4GcWLBmZLGkekuJSMjrdd6Q@mail.gmail.com> - Oleg Kiselyov proposing a typeclass system using something like this mechanism. Ivan discusses how BAP's version works

You can also have anonymous keys. Instead of destructuring a type like above, you just get the ones that you register.

<https://github.com/janestreet/base/blob/master/src/type_equal.ml> In the Jane-Street Base library you can find some of these techniques embedded. Look in the `Witness` module

- <https://sites.google.com/site/ocamlopen/> - Leo White's page on extensible variants
- <https://www.cs.ox.ac.uk/ralf.hinze/publications/PPDP06.pdf> - Open Data Types and Open Functions
- <https://ocaml.org/manual/extensiblevariants.html> The Ocaml manual is actually quite good.
- [discussion of runtime representation](https://stackoverflow.com/questions/54730373/when-should-extensible-variant-types-be-used-in-ocaml)

## Extensible Functions

As part of extensible data types, you might also desire extensible functions. When you add a new case to the datatype, you need to probably add a new handling case to functions that match over this type. These can be simulated using references and mutation. See the Kiselyov example <https://okmij.org/ftp/ML/trep.ml>

If you have metaocaml activated, you can do some of this type manipulating stuff at compile time. You then have a rather satisfyingly flexible system for typelevel programming.

Question: What is the runtime manifestation of adding a case to a type?
Ref cell techniques let you do some funky looking stuff from the eyes of a pure functional programmer. There is a great deal in SICP using this technique and it is part of lisp tradition. If you close over a a single ref cell with a bunch of closures, this collection of closures becomes in essence a kind of object manipulating an internal protected state. One common use case for this is to implement a counter object, which is useful for generating fresh symbols (sometimes called a gensym).

Extensible variants I suspect actually have a dynamic runtime effect. Declaring an extensible variant creates a runtime representation (a counter and perhaps a table) which gets incremented whenever you declare a new constructor. No it doesn't, unless the call goes into the runtime maybe? But `type foo += Gary` is a runtime effectful thing that does have code.
Declaring an ordinary closed datatype allows everything to pretty much be done at compile time and a great deal is erased


Anyhow

```ocaml
let extensible_function = ref (fun success fail -> fail ())
let add_case g = let f = !extensible_function in
                 extensible_function := fun success fail ->
                  g success (fun () -> f success fail)

```

This is a linked list like lookup table. Not very efficient.
We can instead use perhaps a hashtable or dictionary as our key access.

http://okmij.org/ftp/ML/canonical.html#trep

## Universal Types
- <http://mlton.org/StandardML> some interesting stuff here. The universal type representation is the same as cc-ubes
- strings and Sexp.t
- <https://discuss.ocaml.org/t/types-as-first-class-citizens-in-ocaml/2030/2>
- <https://github.com/janestreet/base/blob/master/src/type_equal.ml>
- <https://github.com/mirage/repr>
- <https://github.com/let-def/distwit>
- <https://github.com/samoht/depyt>
- [Heterogeneous physical equality for references](https://github.com/ocaml/ocaml/issues/7425)

## Extensible Records





## Modules
See note on modules

https://ocaml.org/manual/moduleexamples.html#

What are modules?
- kind of like files
- kind of like records
- "compilation units"

Functors are "dependently typed" in some ways in that the signature of the output can depend on the types in the actual module of the input

Modules are by default a runtime notion actually.? They are literally records that get built by the entrypoint of each file. When I access an external file there is actually an indirection through the record? Well they do dynamic linking? 

### Modules vs Typeclasses

## First Class Modules
http://okmij.org/ftp/ML/first-class-modules/

## Higher Kinded Polymorphism
In Haskell, one is used to parametrizing over (Functor f), (Monad f) etc.
It is not directly possible to refer to an unapplied type constructor in ocaml. 

https://www.cl.cam.ac.uk/~jdy22/papers/lightweight-higher-kinded-polymorphism.pdf
https://discuss.ocaml.org/t/higher-kinded-polymorphism/2192
https://www.cl.cam.ac.uk/teaching/1718/L28/10-monads-notes.pdf


Analogy with typeclasses (not that this is how you should think about it)
- superclass constraints = module inclusion
- type parameters = type in module. Really associated types https://wiki.haskell.org/GHC/Type_families#An_associated_data_type_example
- methods of class = values of module

For two type parameters
Reader s a do we bundle them or not?
module type READER
    type s
    type 'a t
end


## GADTs
- https://www.cl.cam.ac.uk/teaching/1718/L28/07-gadts-notes.pdf

For me this is more familiar territory

## Registries


## Typelevel programming
Here's a fun gizmo.


A thing that disturbs me about OCaml modules compared to Haskell typeclasses is that it is not clear how to use them to build something that manipulates types.
Typeclasses instance declarations are a kind of restricted typelevel prolog.

```haskell
data Nat = Succ Nat | Zero
class Plus(a,b,c) where

instance Plus `Zero y y where
instance Plus x y z => Plus (`Succ x) y (`Succ z) where
```

```prolog
plus(zero, Y, Y).
plus(succ(X),Y,succ(Z)) :- plus(X,Y,Z)
```

You can achieve this in ocaml using gadts.

```ocaml
type 'a succ
type zero
type (_,_,_) plus =
  | PZero : (zero, 'a, 'a) plus
  | PSucc : ('x, 'y, 'z) plus -> ('x succ, 'y, 'z succ) plus
```

Gadts are however unmoving. You will need to build the evidence

```ocaml
type _ snat =
    | SZero : zero snat
    | SSucc : 'a snat -> 'a succ snat
type ('x, 'y) eplus = EPlus of 'z snat * ('x,'y,'z) plus
let plus : forall x y. x snat -> y snat -> (x, y) eplus
```

Modules themselves are kind of their own dependent type system bolted on.
They are dependent in the sense that modules may contain module signatures. A Functor that takes in a module may refer to this module signature in the type of it's result

```coq
Record Wrapper := {
    T : Type
    v : T
}.

Definition unwrap (x : Wrapper) : x.(T) := x.(v).
```

```ocaml
module type Wrapper = sig
    module type T
    module v : T
end

module UnWrap (X : Wrapper) : X.T = X.v
```

We can also use the finally tagless style as an alternative to the GADT style `(_,_,_) plus` above. It is sometimes said that finally tagless achieves what GADTs do in more ordinary ocaml.
The finally tagless signature is the pattern matching function. Actually it isn't quite. We should quantify over repr.

```coq
Inductive Plus : nat -> nat -> nat -> Type :=
    | PZero : forall y, Plus 0 y y
    | PSucc : forall x y z, Plus x y z -> Plus (Succ x) y (Succ z)
    .

Print Plus_rec.
(*   *)

Fixpoint plus_rec (x y z : nat) (repr : nat -> nat -> nat -> Type) (p : Plus x y z) (pzero : repr 0 y y) (psucc : repr -> ) : repr x y z :=
    match p with
    | PZero => repr 0 y y
    | PSucc p => 
    end
```

```ocaml
module type PLUS = sig
    type (_,_,_) repr
    val pzero : (zero, 'y, 'y) repr
    val psucc : ('x, 'y, 'z) repr -> ('x succ, 'y, 'z succ) repr
end

module Gadt : PLUS = struct
    type ('a,'b,'c) repr = ('a,'b,'c) plus
    let pzero = Pzero
    let psucc p = PSucc p
end
```

# Standard ML
MLTon
[MLTon first class threads](https://twitter.com/shwestrick/status/1506291833621688320?s=20&t=-ertSPtY87GogVCFq4f-Rw)

# Misc Resources
[: A compiler and VM for a simple language, in 150 lines of code ](https://gist.github.com/p4bl0-/9f4e950e6c06fbba7e168097d89b0e46)
https://news.ycombinator.com/item?id=32121846

[metapp](https://github.com/thierry-martinez/metapp) compile time ocaml production
https://github.com/ocaml-community/cppo
https://github.com/janestreet/ppx_optcomp

[rel: database lib](https://github.com/dbuenzli/rel)

[magic trace](https://github.com/janestreet/magic-trace)

[Prefetching in functional languages](https://www.cl.cam.ac.uk/~tmj32/papers/docs/ainsworth20-ismm.pdf)
- "resource programming in ocaml" linearity [Resource polymorphism](https://arxiv.org/abs/1803.02796) Is it this? Yes probably [linear types in ocaml](https://stackoverflow.com/questions/15620411/linear-types-in-ocaml) using type state basically? [kiselyov monadic regions](https://okmij.org/ftp/Haskell/regions.html)
- [Towards Automatic Resource Bound Analysis for OCaml - hoffmann et al](http://www.cs.cmu.edu/~janh/papers/HoffmannDW17.pdf)
- [LexiFi blog](https://www.lexifi.com/blog/) some interesting articles
- [Using, Understanding, and Unraveling
The OCaml Language
From Practice to Theory and vice versa](https://caml.inria.fr/pub/docs/u3-ocaml/index.html)
- [postl ink optimizer for ocaml](https://github.com/nandor/llir-opt)
- [duplo](https://www.cl.cam.ac.uk/~nl364/docs/duplo.pdf)


Abstract binding trees
https://github.com/shonfeder/um-abt
https://semantic-domain.blogspot.com/2015/03/abstract-binding-trees.html
https://lepigre.fr/ocaml-bindlib/ bindlib

How to do fancy stuff in ocaml

By fancy I mean:
Gadts

heterogenous collections
modules
higher kinded types - https://www.cl.cam.ac.uk/~jdy22/papers/lightweight-higher-kinded-polymorphism.pdf

module to express girard's paradox https://github.com/lpw25/girards-paradox/blob/master/girard.ml


Maybe:
- finally tagless
- delmitted conitnuations
- extensible variants
- open variants?
- exceptions
- polymorphic variants ~ row types? https://stackoverflow.com/questions/48092739/what-are-row-types-are-they-algebraic-data-types https://www.cl.cam.ac.uk/teaching/1415/L28/rows.pdf


gadt katas
- vector type
- addition is commutative, equality
- hlist http://okmij.org/ftp/ML/ML.html#hlist
- keyed het collections
- byo typeclasses http://okmij.org/ftp/ML/trep.ml https://inbox.ocaml.org/caml-list/CALdWJ+zsz99-rSa3S9JMmGUSWM6_PHTg7RF4+COOGsKDTXsZKw@mail.gmail.com/ 


https://ocaml.org/docs/papers.html - some originals by leroy on modules
https://www.reddit.com/r/ocaml/comments/alzi9r/favorite_ocaml_papers/ - favorite ocaml papers list. Inludes:
- How OCaml type checker works -- or what polymorphism and garbage collection have in common -kiselyov
- A modular module system
- Applicative functors and fully transparent higher-order modules
- 1ML – Core and Modules United
- Understanding and Evolving the ML module system - dreyer thesis
- Modular implicits
- Merlin: A Language Server for OCaml (Experience Report)
- Warnigns for pattern matching
- Eseence of ML type inference (ATTAPL chapter)
- Polymorphic typed defunctionalization, GADT example?
- 
https://arxiv.org/pdf/1905.06546.pdf - yallop dolan first class subtypes
https://arxiv.org/abs/2004.11663 - retrofitting parallelism onto ocaml
https://kcsrk.info/papers/drafts/retro-concurrency.pdf - retorfitting effect handlers onto ocaml
https://arxiv.org/abs/2104.11050 - cameller a deductive verificatiool for ocaml

Trawl the ML workshop  http://www.mlworkshop.org/

People
- Jeremy Yallop - https://www.cl.cam.ac.uk/~jdy22/
- Oleg Kiselyov
- Stephen Dolan
- Sam Lindley
- Leo White
- Gabrei Scherer
- Neel K
- 


Advanced functional programming
- https://www.cl.cam.ac.uk/teaching/1718/L28/materials.html
- https://www.cl.cam.ac.uk/teaching/1617/L28/materials.html


ocamlfdo- https://github.com/gretay-js/ocamlfdo ocaml feedback directed optimizer

[rank N types in ocaml](https://soap.coffee/~lthms/posts/RankNTypesInOCaml.html) - wrap in records and using unboxed annotations

[PPX](https://ocaml.org/docs/metaprogramming) deriving_inline, astexplorer is in vscode

[sherlodoc](https://github.com/art-w/sherlodoc) hoogle like thing

[wasmer](https://wasmer.io/posts/running-wasm-in-ocaml-with-wasmer)

[modular macros](https://www.cl.cam.ac.uk/~jdy22/projects/modular-macros/)

[lower kinded optics](https://github.com/polytypic/loko-ml)