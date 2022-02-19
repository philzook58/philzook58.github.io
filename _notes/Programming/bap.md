---
layout: post
title: Gettin' Bappin' with Bap
---

- [What is Binary Analysis](#what-is-binary-analysis)
    - [Program Analysis](#program-analysis)
    - [How are binaries made](#how-are-binaries-made)
- [Disassembly](#disassembly)
- [Knowledge Base](#knowledge-base)
    - [Classes, Slots](#classes-slots)
    - [Objects and Values](#objects-and-values)
    - [Domains](#domains)
    - [Promises](#promises)
    - [`Record.t` = `Dict.t` + Domains](#recordt--dictt--domains)
    - [Value = Record + Sorts](#value--record--sorts)
- [Core Theory](#core-theory)
    - [Universal Types, Existentials and Packing](#universal-types-existentials-and-packing)
    - [Typed Keys](#typed-keys)
- [Bap Lisp](#bap-lisp)
- [Project Structure](#project-structure)
- [Binary / Program Analysis](#binary--program-analysis)
  - [Other tidbits](#other-tidbits)
  - [Universal Values](#universal-values)

`--print-missing` flag for missing instruction semantics https://github.com/BinaryAnalysisPlatform/bap/pull/1409



https://watch.ocaml.org/videos/watch/8dc2d8d3-c140-4c3d-a8fe-a6fcf6fba988
JVM and C support in the futute
primus lisp - common lisp like
C and python ctypes bindings

semantics - either in
ocaml dsl or primus lisp dsl

(defun rTST (rn rm _ _ )
  "tst rn, rm"
  (let ((rd (logand rn rm))
  (set ZF (is-zero rd))))
  (set NF ())
)

dependency injection
dynamic linking 


framework
inital style insufficient because need to update
extensible variants (GADTS)? no
not abstract. Heavyweight. 
Not serializable
higher kinded



Bap is quite the beast.

To me starting out there was a lot to swallow. First I had to learn Ocaml, second I knew even less about program analysis and binary stuff than I do now.

```C
int main(){
    return 3;
}
```

```
gcc foo.c
objdump -d a.out
```



To make a basic file to explore some binary, first make a dune file

```lisp
( executable
  (name main)
  (libraries bap bap-primus)
  (flags -linkall)
  (preprocess (pps ppx_jane))
)
```


```ocaml
open Core_kernel
open Bap.Std
include Self()

(* Must call init before everything*)
let _ : (unit, Bap_main.error) Stdlib.result = Bap_main.init ()

(* Load a file as a project *)
let myfile = "/home/philip/Documents/ocaml/a.out"
let proj = Project.create (Project.Input.file ~loader:"llvm" ~filename:myfile) |> Or_error.ok_exn

(* Getting the current knowledge base *)
let state = Toplevel.current ()

```

You can view information available about a file by


The bap command line has some stock features available + some plugins.

Ivan has an Ascii Cinema here

Get some info from the Knowledge Base. 
`bap list`

## Bap Lifecycle
We open Bap.Std
open Self()

Call Bap_main.init
Bap_toplevel is in Bap_types. It holds an empty knowledge base at first

Project.create
calls the disassembler
calls the brancher

Core theory holds both the finally tagless module definition, but also a bunch of slots.

https://github.com/BinaryAnalysisPlatform/bap/blob/ef6afa455a086fdf6413d2f32db98fa9ff1b28d8/plugins/bil/bil_ir.mli
Bil.reify
What is this. Why is this in plugins

## The Bap Command
After installing, if you type `bap` you will get a list of information
- Commands
- Plugins

`bap --help` is an overwhelming amount of information.

Useful flags

## Bap Project Directory Structure

It may be the case that the easiest thing to do sometimes is some source code spelunking.

- plugins
- src
- lib


Github search
odoc





### Bap Plugins
> And this is the whole idea of BAP as a framework instead of a library. There are extension points, which enable you to extend bap without having to worry about how to create a project, how to properly find the file, how to specify the architecture and other parameters. You just register a pass that takes a ready project and focus on your analysis instead of writing all this boilerplate. E.g., in the example above it is rightful to assume that you want to get the project before starting enqueing jobs, so you can register a pass that will be called once the project is ready and if the pass is selected,

https://binaryanalysisplatform.github.io/bap/api/master/bap-main/Bap_main/index.html
https://gitter.im/BinaryAnalysisPlatform/bap?at=610c3e322453386b6c373696
https://en.wikipedia.org/wiki/Dependency_injection

The bap main thing



#### Bap api
The flags corresponding to plugins are typically namespace like `--pluginname-pluginoption`


 In order for bap to recover high level function arguments you can supply a header file.
 If you know this plugin is called `api` you can find the options available by 
 `bap --help | grep -C 4 api`

 --api-path=somefolder where somefolder has a folder called C in it.
 --api-show
 --api-list-paths

### Bap Disassemble
Bap disassemble is the default command if you choose no command.
You can use it similar to objdump
`--print-symbol` lets you print just a particular function

[where print flags are defined](https://github.com/BinaryAnalysisPlatform/bap/blob/master/plugins/print/print_main.ml)
-d is dump options to bap diassemble. currently I see 
- knowledge
- cfg
- graph
- asm
- asm.adt
- adm.decoded
- asm.sexp
- bil
- bil.adt
- bil.sexp
- bir
- ogre


### Saving and restroing the knowledge base
-k
--project
--update

### Bap Analyze
https://asciinema.org/a/358996

### Bap Passes

### Bap.Std

Bap.Std 

BIL - Bap Instruction Language.
http://binaryanalysisplatform.github.io/bap/api/master/bap/Bap/Std/index.html




## OCaml and Registries

There is a pattern avialable in OCaml, which has mutable global state avaialable if you need it, to use a pattern where you make a global table with which to 

In this form, this pattern is ubiquitous in bap

## The Knowledge Base
The Knowledge Base is a key value store? Database.
It is also kind of an alternative class (like object oriented classes) system
It is also kind of a

The knowledge base is backed by global tables.
New keys to these tables are generated


# What is Binary Analysis

Dynamic - It feels like you're running the binary in some sense. Maybe on an emulated environment
Static - It feels like you're not running the binary

Fuzzing is definitely dynamic.
Dataflow analysis on a CFG is static
There are greys areas. Symbolic execution starts to feel like a grey area. I would consider it to be largely dynamic, but you are executing in a rather odd way.

Trying to understand a binary
Why?
- Finding vulnerabilities for defense or offense
  + buffer overflows
  + double frees
  + use after frees
  + memory leaks - just bad performance
  + info leaks - bad security
- Verification - Did your compiler produce a thing that does what your code said?
- Reversing/Cracking closed source software. 
- Patching and Code injection. Finding Bugs for use in speed runs. Game Genie.
- Auditing
- Aids for manual RE work. RE is useful because things may be undocumented intentionally or otherwise. You want to reuse a chip, or turn on secret functionality, or reverse a protocol.
- Discovery of patent violation or GPL violations
- Comparing programs. Discovering what has been patched.

I don't want my information stolen or held ransom. I don't want people peeping in on my conversations. I don't want my computer wrecked. These are all malicious actors
We also don't want our planes and rockets crashing. This does not require maliciousness on anyone's part persay.



- Symbol recovery
- Disassembly
- CFG recovery
- Taint tracking
- symbolic execution

<https://github.com/analysis-tools-dev/dynamic-analysis> A list of tools
https://analysis-tools.dev/
[CSE597: Binary-level program analysis	Spring 19 Gang Tan](http://www.cse.psu.edu/~gxt29/teaching/cse597s19/schedule.html)

### Program Analysis
What's the difference? Binaries are less structured than what you'll typically find talked about in program analysis literature.

Binaries are tough because we have tossed away or the coupling has become very loose between high level intent and constructs and what is there. 

### How are binaries made


C preprocessor -> Maintains file number information isn't that interesting

C compiler -> assembly. You can ask for this assembly with `-S`. You can also 
Or more cut up
C -> IR
IR -> MIR (what does gcc do? RTL right? )
MIR -> Asm

# Disassembly
- Linear
- Recursive
- Shingled
- 

[Disasm.Driver](https://binaryanalysisplatform.github.io/bap/api/master/bap/Bap/Std/Disasm/Driver/index.html)
[](https://binaryanalysisplatform.github.io/bap/api/master/bap/Bap/Std/Disasm/index.html)

Delay slots are an annoyance. Some architectures allow instructions to exist in the shadow of jump instructions that logically execute beofre the jump instruction. This makes sense from a micro architectural perspective, but it is bizarre to disassemble

# Knowledge Base

The BAP knowledge base is a centralized store of information meant to hold all the things discovered about a binary. This include properties like the architecture, addresses, and lifted code. User defined analysis may intercommunicate by storing their results into the knowledge base.

The term knowledge base may mean nothing more than database, but to me it implies that it is a combination of a database and mechanisms to automatically derive or populate more information.




`bap list classes` shows a list of classes and slots of those classes.

`Toplevel.current ()` is the implicit current knowledge base. This has the program you've lifted in it

In spirit, each object in the KB is a record. Orindary ocaml records look like


```ocaml
type myrecord = {myint : int; mybool : bool}
```
but this is not acceptable, because the record needs to be user extensible. Hence some fairly sophisticated "extensible record" programming techniques are used.  The Bap type `Dict.t` is an extensible record. <https://github.com/ivg/bap/blob/master/lib/bap_types/bap_value.ml>



### Classes, Slots

A class is a description of the fields (slots) of a record. You can declare a new class with no field via `KB.Class.declare`
A slot os a field of a record. It has a type and name.

You can add another slot to a class by calling `KB.Class.property`

### Objects and Values


### Domains

### Promises

Slots are often lazily filled when something `collects` them. These lazy promises are registered via the `KB.promise` funcion.

### `Record.t` = `Dict.t` + Domains

It is desirable for bap to define a notion of record merging. This is a useful concept if you want to combine information built by different pieces of code into a single record.
One way of doing this is require each field implement the `domain` interface, so that you can merge record by merging each field individually.
The common case is that some code may only fill out certain fields of the record and other code other disjoint fields. The empty fields are represented by ocaml `None` values. Then the merge you want is the record with all the fields filled out. This is the optional domain.
Another common case is to merge a field that is a set by using the union or intersection of those sets. 

### Value = Record + Sorts

[code implementing Knowledge base code](https://github.com/ivg/bap/tree/master/lib/knowledge)

[Discussion of Ivan's talk](https://gitter.im/BinaryAnalysisPlatform/bap?at=614c7f4c1179346966327e8c)

[Jt's notes](https://github.com/jtpaasch/bap-kb)

# Core Theory

Dumping the concrete syntax of core theory <https://gitter.im/BinaryAnalysisPlatform/bap?at=61fd525703f27047821b4c08>
`bap /bin/true --core-theory-herbrand -dknowledge`

Always try `--no-cache`

To describe the operations of different machines, bap lifts into a common intermediate representation. From the common representation you can perform different binary analysis.

The main form representation in previous version of bap was an algebraic data type, BIL. This is to some degree still the case for some purposes, but now there is a different programming construct intended as the primary source. This thing is called the the Core Theory of bap. The word "theory", strange as it sounds to some ears, refers to a common set of typed apis that analysis need to implement to receive lifted code. A "theory" in the context of logic is a set of types, functions/constants, and axioms. We don't really have axioms expressible in ocaml, but we can certainly talk about types and functions.

Instead of having analysis receive a normal ocaml algebraic data type, instead they implement a finally tagless style type signature of core_theory. Instead of registering as a pass to receive the adt, they register their cor_theory instance with a global database that is typically automatically called by other parts of bap.

There is a confusing intertwining of the concepts of the knowledge base and core_theory. This is done I think so that there is a possibility of using arbitrary data tucked away in the knowledge base, which operates as a kind of global state monad. In principle, it is possible to construct an analog of core_theory that has nothing to do with the knowledge base.

It is a curious fact that there is an equivalence between ordinary tree-like and a functional representation of how to use them. The idea being is that the only thing you can do to an algebraic data structure is take it apart and "summarize" it in some way. This taking apart operation is the analog of folding a list. This is related to the concept of a Church encoding.

More concretely, consider the following simple datatype describing arithmetic expressions.
```ocaml
type aexpr = Add of initadd * initadd | Lit of int
```

You can interpret it in different ways

```ocaml
let rec int_interp x = match x with
   | Add (x,y) -> (int_inter x) + (int_interp y)
   | Lit n -> n

let rec string_interp x = match x with
   | Add (x,y) -> sprintf "(%s + %s)" (string_inter x) (string_interp y)
   | Lit n -> int_of_string n

let ex1 = Add (Lit 1, Lit 2)
let ex1_int = int_interp ex1
let ex1_string = string_interp ex1
```

We can completely mechanically turn this type definition into a module signature definition. Every constructor becomes a function in the module signature.

```ocaml
module type AEXPR = sig
  type t
  val lit : int -> t
  val add : t -> t -> t
end
```
Every interpretation becomes a new module that implements this signature

```ocaml
module IntAExpr = struct
  type t = int
  let lit x = x
  let add x y = x + y
end

module StringAExpr = struct
  type t = string
  let lit x = string_of_int x
  let add x y = sprintf "(%s + %s)" x y
end

module Ex1 (S : AExpr) = struct
  let ex1 : S.t = S.add (S.lit 1) (S.lit 2)
end

module Int_Ex1 = Ex1(IntAExpr)
module String_Ex1 = Ex1(StringAExpr)
```

When you boil it down, a module is mostly a record. I say mostly because modules may also contain types. You can achieve a very similar effect by using records.


```ocaml
type 't aexpr_rec = {
  lit : int -> 't;
  add : 't -> 't -> 't
}

let int_rec : int aexpr_rec = {
  lit = fun x -> x;
  add : fun x y -> x + y
}

let string_rec : string aexpr_rec = {
  lit = string_of_int;
  add : fun x y -> sprintf "(%s + %s)" x y
}

let ex1 (s : 't aexpr_rec) : 't = s.add (s.lit 1) (s.lit 2)
let ex1_int = ex1 int_rec
let ex1_string = ex1 string_rec
```

To more closely match the above, we shouldn't expose the underlying type `'t`. We can to this by packing it away in an existential type. Packing it away means we can never do anything with it though. This brings in the concept of keys which are a witness of the packed away type. It tends to be the case these keys are implemented using extensible variants.

```ocaml
type _ k = ..
type packed_aexpr = { key : 't k;  impl : 't aexpr_rec}

type _ k += Int : int k
type _ k += String : string k

let packed_int_aexpr = {key =  Int; impl = int_rec}
let packed_string_aexpr = {key =  String; impl = string_rec}
```

Using first class modules amounts to about the same thing?

Now we can make a registry of implementations.


Finally tagless is interesting for multiple reasons.
Because you can combine multiple signatures in a module, finally tagless is open to new "constructors" in a way a concrete data type is not.
Interpreting over the initial data type is just that, an interpreter. Interpreters usually have a performance hit. It can be the case that finally tagless has less indirection and exposes more optimizations to the compiler. YMMV.
Finally tagless style is also interesting because it allows type safe interfaces that would require gadts to describe in initial style. This is because gadts allow you to constrain and hide the types in constructors in a way that you recover the types inside a pattern match. Since ordinary functions always allowed annotating more constrained types than their most general type, this is easy in the context of a finally tagless encoding


```ocaml
type 'a abexpr = 
   | Lit : 'a -> 'a abexpr
   | Add : int abexpr -> int abexpr -> int abexpr
   | Ite : bool abexpr -> 'a abexpr -> 'a abexpr -> 'a abexpr

let rec interp_val (type a) (x : a abexpr) : a = 
  match x with
  | Lit x -> x
  | Add (x,y) -> (interp_val x) + (interp_val y)

module type ABEXPR = sig
  type 'a t
  val lit : 'a -> 'a t
  val add : int t -> int t -> int t
  val ite : bool t -> 'a t -> 'a t -> 'a t 
end
```



The finally tagless style in bap performs a refactoring on this registry.
Way back at the beginning, the module namespace is ultimately under the hood a dictionary in the compiler associating the implementations with a name. We can reify this to a first class value instead

packed_aexpr String.Map.t




### Universal Types, Existentials and Packing

Extensible 

Types describe how data can be treated. If you want to have different types treatable in the same way, you need to find to convert them to a format that is uniform. Ocaml itself achieves this by having a uniform tagging convention and pointer.s Maybe more deeply under the hood, everything is made up of the same stuff.

But two common options are boxing and serialization.

`Sexp.t` is a uniform serialization format in ocaml. It is actually a good universal type. "stringly typed" indeed.
This is perhaps what Ivan was getting at in his comment about Ogre.

Instead of doing fancy typelevel tricks, a hlist can be presented as
`type hlist = Sexp.t list`

An extensible record is `Sexp.t String.Map.t` which we could hide behind a safe interface?

Packing is
`sexp_of_t : t -> Sexp.t`

And unpacking from the universal type is
`t_of_sexp : Sexp.t -> t option`

```ocaml
module Dict : sig
  type t
  type 'a key
  type create_key : string -> (Sexp.t -> 'a) -> (t -> Sexp.t option) -> 'a key
  val put : t -> 'a key -> 'a -> t
  val get : t -> 'a key -> 'a option
end = struct
type 'a key = { name : string;
                t_of_sexp : Sexp.t -> 'a;
                sexp_of_t : 'a -> Sexp.t option
              }
type t = Sexp.t String.Map.t
let create_key name t_of_sexp sexp_of_t = {name; t_of_sexp; sexp_of_t}
let empty = String.Map.empty
let put d k v = String.Map.put d k.name (k.sexp_of_t v)
let get d k = (String.Map.get d k.name) >>= k.t_of_sexp
end
```

It's almost silly.

Now, not everything has a `Sexp.t` representation. Functions typically don't (we could in the case of finite types as a domain reify the function into a table and serialize that, but otherwise we need to serialize the text of the function or code, or closure, all of which is tough (probably also not impossible though).)

A more low level approach might be to use Marshalling https://ocaml.org/api/Marshal.html

It is interesting to consider what we lose here and what we gain by going to more convoluted representations.

A different representation can be had by using existential packing. The following type can indeed contain anything.

`type some_type = Pack : 'a -> some_type`

We can get pretty far in the above

```ocaml
let create_key name = name
let put d k v -> String.Map.put d k (Pack v)
let get d k -> let Pack x = String.Map.get d k in ? (* We have lost the connection between the original type and the typed key. *)  
```
We could maintain a table of all keys registered and only allow it to happen once in which case we're possibly dignified in using an unsafe cast, but who knows. These things can be subtle.

```ocaml
let get d k -> let Pack x = String.Map.get d k in Obj.magic x
```

So we want to seal away the types so that things of different types are uniformly represented, but not forever. This leads us to a notion of a typed key, which is a kind of evidence we can pack up of the original type.


### Typed Keys

Let's say we have something that may work over ints and floats.

```ocaml
type ty = Int | Float
type univ = IntVal of int | FloatVal of float

let int_float_add (t : ty) (x : univ) (y : univ) : univ =
 match t, x, y with
 | Int, IntVal x, IntVal y -> IntVal (x + y)
 | Float, FloatVal x, FloatVal y -> FloatVal (x +. y)
 | _, _ , _ -> failwith "type mismatch in int_float_add"

```

You may have see this trick before. GADTs offer a convenient way to build value level thingies that tell us stuff about types.
For example if we wanted to tell the different between floats and ints.

```ocaml
type _ ty = 
   | Int : int ty
   | Float : float ty
```

Now we can use this value as evidence that an incoming type is either an int or float. (As a rule of thumb, it is wise to use the `type a` syntax when dealing with gadts)

```ocaml
let int_float_add (type a) (t : a ty) (x : a) (y : a) : a = 
  match ty
  | Int -> x + y
  | Float -> x +. y
```

We've removed the indirection of `univ` and made a compile time type check so that we no longer have a failure case.

In a sense, this reflection gives us a first class notion of quantifying over types, reflecting the type level down to the value level. Separately, modules and functors already gave a way of second class quantifying over types, and first class modules make that first class.

Something related is known as the singleton technique for reflecting values into the type level.

```ocaml
type zero = Zero
type 'a succ = Succ of 'a

type _ snat = 
  | SZero : zero snat
  | SSucc : 'a snat -> 'a succ snat 

(* plus as a relation *)
type (_,_,_) plus =
  | PZero : (zero, 'a, 'a) plus
  | PSucc : ('a, 'b, 'c) plus -> ('a succ, 'b, 'c succ) plus

(* exists c, (a,b,c) plus *)
type ('a,'b) exists_plus = Pack : 'c snat * ('a,'b,'c) plus -> ('a,'b) exists_plus

let rec splus : type a b. a snat -> b snat -> (a,b) exists_plus =
  fun x y ->
  match x with
  | SZero -> Pack (y, PZero)
  | SSucc n -> let (Pack (z, pf)) = splus n y in
               Pack (SSucc z, PSucc pf)
```

Ocaml has a very very interesting addition to this story you won't find in many other languages, using extensible variants. Extensible variants I believe have their history associated with exceptions, for which you could add new exception constructors to. This mechanism was generalized and interoperates with gadts and first class modules. Pretty crazy.
Now instead of having to have a closed universe of possible type witnesses like in `'a ty` above, we can leave the universe open and extensible. 

```ocaml

```

Other discussions of interest
- The Key Monad https://www.reddit.com/r/haskell/comments/574t1e/the_key_monad_type_safe_unconstrained_dynamic/ . Interesting examples- convert phoas to well typed de bruijn. Off the wall question: can we embed true hoas pattern matching?
- https://apfelmus.nfshost.com/blog/2011/09/04-vault.html
- The value restriction http://mlton.org/ValueRestriction https://counterexamples.org/polymorphic-references.html I wonder if there is a general theme that every counterexample is basically a technique in disguise. This may or may not work in rust as this is in some sense dependent upon aliasing.
- https://github.com/c-cube/datalog/blob/a29910e3262f4e0490fb69575b1246c4b4a165ee/src/bottom_up/bottomUp.ml#L8 Universal type
- https://blog.janestreet.com/more-expressive-gadt-encodings-via-first-class-modules/
- http://okmij.org/ftp/ML/first-class-modules/index.html "simplistic gadts" uses a ref cell tunnel. http://okmij.org/ftp/ML/GADT.ml This is exactly using the value restriction counterexample to good use.

Channel passing style. subroutine style giving output pointers.
(a -> b) -> (a -> unit * unit -> b) in ocaml. Can break apart. "Spooky action at a distance"
or 
(a -> b) -> (a -> b ref -> unit)
(a -> b ref -> ()) -> (a -> b)





###

type person = {name : string; age : int}
type people = person list

A refactoring one might want to do.
type people = {names : string list; ages : int list}

Now this isn't an isomorphism, but it's close. The new type is not constrained to have as many names as ages

These distinct reprentations show up all over the place.

There is a natural notion of product. We call it so because it obeys in a sense the usual laws of products
(int * bool) * string <-> int * (bool * string)

The usual tuple interpretation functor for finally tagless:
module Tup(S : ADDEXPR)(T : ADDEXPR) = struct

end


modules are kind of like records. In some sense, what we have done with defining multiple modules is isomorphic to


type 'a all_expr_impls = {
  intaexpr : 'a;
  stringaexpr : 'a;
}
type all_aexpr = aexpr all_aexpr_impl

We can factor through two composed records like this.



We can perform a refactoring of this to
The is the bap-style finally tagless for non extensbile records

type ('a,'b) t = 'a option
hold a key?
A tuple is a hetergenous record of sorts. but kind of not really. Only simpler in that the number of fields is small.

I guess 
type het_tup = {key1 : 'a key; 'a : key2 : 'b key; val2 : 'b}
Is complicating the key packed record on one axis, by increasing the number of fields. If we want a runtime dynamic number of fields
we go to `keyed list`

module FstString = 
  type t = (string * _ option)
  let lit x = (int_of_string x,  None)
end

module SndInt = 
  type t = (_ option * )
end
module Join( : Fst)( : Snd) =


# Bap Lisp
You can run primus lisp functions by making a file demo.lisp filled with the content
```(defun mymain ()  (declare (external 'mymain))    (msg "hello world"))`
And invoke it via `bap eval-lisp mymain --primus-lisp-load=demo --primus-print-obs=lisp-message,exception`

loading into semantics primus lisp
`bap show-lisp foo --primus-lisp-load=demo -tarmv5+le`

```lisp
foo:
((core:eff ((set R0 1)))
 (bap:ir-graph "00000009:
                0000000a: R0 := 1")
 (bap:insn-dests (()))
 (bap:bir (%00000009))
 (bap:bil "{
             R0 := 1
           }")
 (core:value ((core:val (1)) (bap:static-value (0x1)) (bap:exp 1))))
```

# Project Structure


# Binary / Program Analysis

Call graph
Control flow graph
Functions
Blocks
insns

Dataflow analysis. Backwards Forwards. Fixedpoint on graphs, topological sort.
May/Must

## Other tidbits
JT's gists
Ivan's gists
Choice gitter tips

## Universal Values
https://discuss.ocaml.org/t/types-as-first-class-citizens-in-ocaml/2030
https://github.com/janestreet/core_kernel/blob/master/univ/src/univ.ml
http://binaryanalysisplatform.github.io/bap/api/odoc/bap/Bap/Std/Value/index.html
https://blog.shaynefletcher.org/2017/03/universal-type.html

locally abstract types. Using (type u) as an argument - useful for first class modules ande gadts

Storing first class modules in a hashtable is an example.

DIY typeclasses

universal value + registry of typeclass instances?


#Primus
+ https://feliam.wordpress.com/2010/10/07/the-symbolic-maze/ solving a maze with symbolic execution
+ tabulating a function
+ a supercompiler?
+ taint tracking is like a cup game? Some myterious program swaps and does claculations on the entries. Which final entry came from your input? Taint tracking is like abstract interpetation with 100% path sensitvity. Concolic-ish. You can track what was possible along your exact path. Could i tag probabilities in any meaningful way on variables? I tfeels like probabilites tag the whole state, not pieces of it. Partial 
+ Partial evaluation/binding time analysis - Mark one input as "runtime" tainted and another as "compile" time tainted.

Primus is built in this extensible style.

You can find them in the plugins directory


I'm trying to understand the different primus plugins.

I suppose all of them can be mixed and matched but for some it be very strange to. Basically I would think you'd want only one Schedulers


Schedulers determine when and how forked machines are put into and take out of some kind of storage structure


Schedulers:
- primus-promiscuous
- primus-greedy


Forkers decide how and when to fork
- primus-random - fuzzing?
- primus-symbolic - symbolic execution?


primus-limit = limit the number of somethigns a machine can do before being killed. depth limited search
primus-print - just print various observations when they get fired

