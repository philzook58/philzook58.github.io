

title: Gettin Bappin with Bap


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


### Bap Plugins
> And this is the whole idea of BAP as a framework instead of a library. There are extension points, which enable you to extend bap without having to worry about how to create a project, how to properly find the file, how to specify the architecture and other parameters. You just register a pass that takes a ready project and focus on your analysis instead of writing all this boilerplate. E.g., in the example above it is rightful to assume that you want to get the project before starting enqueing jobs, so you can register a pass that will be called once the project is ready and if the pass is selected,

https://binaryanalysisplatform.github.io/bap/api/master/bap-main/Bap_main/index.html
https://gitter.im/BinaryAnalysisPlatform/bap?at=610c3e322453386b6c373696
https://en.wikipedia.org/wiki/Dependency_injection

The bap main thing

### Bap Passes


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

Trying to understand a binary
Why?
- Finding vulnerabilities for defense or offense
  + buffer overflows
  + double frees
  + use after frees
  + memory leaks - just bad performance
  + info leaks - bad security
- Verification - Did your compiler produce a thing that does what your code said?
- Reversing/Cracking closed source software
- Patching and Code injection
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

### Program Analysis
What's the difference? Binaries are less structured than what you'll typically find talked about in program analysis literature./


## Core Theory

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

