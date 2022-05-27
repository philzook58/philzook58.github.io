---
layout: post
title: Gettin' Bappin' with Bap
---

- [Let's Bap](#lets-bap)
  - [Installing](#installing)
  - [A toy program for you to try](#a-toy-program-for-you-to-try)
  - [The `bap` command](#the-bap-command)
  - [Bap equivalents of binutils](#bap-equivalents-of-binutils)
  - [Giving Bap C info](#giving-bap-c-info)
    - [Saving and restoring the knowledge base](#saving-and-restoring-the-knowledge-base)
    - [Recipes](#recipes)
    - [Interesting Places to Look](#interesting-places-to-look)
- [IRs](#irs)
  - [BIL](#bil)
  - [BIR](#bir)
  - [Core Theory](#core-theory)
- [Disassembler](#disassembler)
- [Primus Lisp](#primus-lisp)
- [Primus](#primus)
  - [Primus](#primus-1)
  - [Ocaml](#ocaml)
    - [Systems](#systems)
    - [State](#state)
    - [Forking](#forking)
    - [Components](#components)
    - [Observations](#observations)
    - [Linker](#linker)
- [Ocaml Stuff](#ocaml-stuff)
    - [Finding Stuff](#finding-stuff)
    - [Bap is not a library.](#bap-is-not-a-library)
  - [Plugins vs Commands vs Passes vs Scripts](#plugins-vs-commands-vs-passes-vs-scripts)
    - [Commands](#commands)
    - [Plugins](#plugins)
    - [Scripts](#scripts)
    - [Registries](#registries)
    - [Bap Lifecycle](#bap-lifecycle)
  - [Bap Project Directory Structure](#bap-project-directory-structure)
    - [Bap Plugins](#bap-plugins)
      - [Bap api](#bap-api)
    - [Bap Disassemble](#bap-disassemble)
    - [Saving and restoring the knowledge base](#saving-and-restoring-the-knowledge-base-1)
    - [Bap Analyze](#bap-analyze)
    - [Bap Passes](#bap-passes)
    - [Bap.Std](#bapstd)
  - [OCaml and Registries](#ocaml-and-registries)
  - [The Knowledge Base](#the-knowledge-base)
- [Knowledge Base](#knowledge-base)
    - [Classes, Slots](#classes-slots)
    - [Objects and Values](#objects-and-values)
    - [Domains](#domains)
    - [Promises](#promises)
    - [`Record.t` = `Dict.t` + Domains](#recordt--dictt--domains)
    - [Value = Record + Sorts](#value--record--sorts)
- [Core Theory Blithering](#core-theory-blithering)
    - [Universal Types, Existentials and Packing](#universal-types-existentials-and-packing)
    - [Typed Keys](#typed-keys)
- [Project Structure](#project-structure)
- [Binary / Program Analysis](#binary--program-analysis)
  - [Other tidbits](#other-tidbits)
  - [Universal Values](#universal-values)
- [Misc](#misc)

# Let's Bap

Bap, the binary analysis platform, is a framework that disassembles binary code in a variety of formats and for a variety of architectures and lifts them into a common representation. It then supplies analysis you may perform and tools with which to build your own custom analysis

Bap is quite the beast.

To me starting out there was a lot to swallow. First I had to learn Ocaml, second I knew even less about program analysis and binary stuff than I do now.

You may also want to look at [JT's Bap 2.0 Notes](https://github.com/draperlaboratory/cbat_tools/tree/master/bap-notes)

Come on down the the [BAP gitter](https://gitter.im/BinaryAnalysisPlatform/bap). It is a friendly place and basically the only way to use bap sometimes is to ask questions there

## Installing

`opam` is the standard ocaml package manager. Long story short:

```
opam depext --install bap # installs bap and its dependencies
```

More details here <https://github.com/BinaryAnalysisPlatform/bap#from-sources>

## A toy program for you to try

You really should get bap running on your machine and just try dumping out this program with the various options.

```C
int main(){
    return 3;
}
```

```
gcc foo.c
objdump -d a.out
```

## The `bap` command

After installing, if you type `bap` you will get a list of information

Typing `bap` on my system gets me. You should actually take a minute to read this. For serious. The `bap` command line itself is some of the best documentation of what bap has.

```
Usage:
  bap <COMMAND> [<OPTIONS>]

Common options:
  --version                prints the version number and exits;
  --plugin-path <DIR>      adds <DIR> to the plugins search path;
  --logdir <DIR>           creates a log file in <DIR>;
  --recipe <VAL>           extracts command line arguments from the recipe.

Commands:
  objdump                  disassembles and prints a binary using the linear sweep algorithm
  mc                       disassembles a (human readable) string of bytes
  primus-observations      prints a list of Primus observations
  primus-components        prints a list of Primus components
  primus-systems           prints a list of Primus systems
  compare                  compares several alternative versions of the binary with the base
  disassemble              disassembles and analyzes the input file
  print-recipes            prints available recipes
  recipes                  provides commands to manipulate the recipe subsystem
  list                     explores various BAP facilities
  .                        does nothing and prints nothing
  cache                    provides options to control cache size and cache garbage collector
  analyze                  analyses the knowledge base
  eval-lisp                runs the Primus lisp program
  show-lisp                shows the static semantics of Primus Lisp definitions
  primus-lisp-documentation no description provided
  dependencies             outputs program dependencies such as libraries and symbols
  specification            displays information about the binary


Plugins:
  abi                      apply abi information to a project
  analyze                  implements the analyze command
  api                      add parameters to subroutines based on known API
  arm                      the target support package that enables support for the ARM family of
  beagle                   microx powered obfuscated string solver
  bil                      provides bil optimizations
  byteweight               find function starts using Byteweight algorithm
  cache                    provide caching services
  callgraph-collator       compares projects by their callgraphs
  callsites                annotate callsites with subroutine's arguments
  constant-tracker         constant Tracking Analysis based on Primus
  cxxfilt                  provide c++filt based demangler
  demangle                 demangle subroutine names
  dependencies             analyses the binary dependencies
  disassemble              implements the disassemble command
  dump-symbols             dump symbol information as a list of blocks
  elf-loader               read ELF and DWARF formats in a pure OCaml
  flatten                  flattens (unrolls) BIR expressions into a trivial form
  frontc-parser            parse c files with FrontC
  glibc-runtime            enables ad-hoc support for glibc runtime code
  llvm                     provide loader and disassembler using LLVM library
  map-terms                map terms using BML DSL
  mc                       bAP Core Library
  mips                     provide MIPS lifter
  objdump                  this plugin provides a symbolizer based on objdump
  optimization             automatically removes dead code and propagates consts
  phoenix                  output project information in a phoenix format
  powerpc                  provide PowerPC lifter
  primus-dictionary        provides a key-value storage
  primus-exploring         evaluates all machines, prioritizing the least visited
  primus-greedy            evaluates all machines in the DFS order
  primus-limit             ensures termination by limiting Primus machines
  primus-lisp              install and load Primus lisp libraries
  primus-loader            generic program loader for Primus
  primus-mark-visited      registers the bap:mark-visited component
  primus-powerpc           powerpc support package
  primus-print             prints Primus states and observations
  primus-promiscuous       enables the promiscuous mode of execution
  primus-propagate-taint   a compatibility layer between different taint analysis frameworks
  primus-random            provides components for Primus state randomization and controls their
  primus-region            interval sets
  primus-round-robin       evaluates all machines in the BFS order
  primus-symbolic-executor enables symbolic execution in Primus
  primus-systems           loads Primus systems and registers them in the system repository
  primus-taint             a taint analysis control interface
  primus-test              primus Program Testing and Verification Kit
  primus-wandering         evaluates all machines while
  primus-x86               x86 support package
  print                    print project in various formats
  propagate-taint          propagate taints through a program
  raw                      provides a loader for raw binaries
  read-symbols             provides functions addresses and (optionally) names from a
  recipe-command           manipulates bap recipes
  relocatable              extracts symbolic information from the program relocations
  report                   reports program status
  riscv                    provide Riscv target
  run                      a pass that will run a program
  specification            prints the specification of the binary (like readelf)
  ssa                      translates a program into the SSA form
  strings                  find strings of characters
  stub-resolver            identifies functions that are stubs and redirects calls to stubs to
  systemz                  provide Systemz lifter
  taint                    taint specified terms
  thumb                    provide Thumb lifter
  trace                    manage execution traces
  trivial-condition-form   eliminates complex conditionals in branches
  warn-unused              warn about unused results of certain functions
  x86                      provide x86 lifter
```

I have no idea what many of these do. A majority of the commands are just ways to query for available capabilities of different kinds

Here are the highlights in my opinion.
- Commands
  + primus-observations      prints a list of Primus observations
  + primus-components        prints a list of Primus components
  + primus-systems           prints a list of Primus systems
  + list                     explores various BAP facilities. Especially helpful for finding slots in the knowledge base
  + cache                    provides options to control cache size and cache garbage collector
  + analyze                  analyses the knowledge base
  + eval-lisp                runs the Primus lisp program
  + show-lisp                shows the static semantics of Primus Lisp definitions
  + primus-lisp-documentation no description provided

- Plugins
  + print
  + run
  + api
  + primus-lisp

Typing `bap list` on my system gives

```
  entities                 prints this message
  plugins                  installed BAP plugins
  commands                 bap utility commands
  recipes                  installed recipes
  features                 plugin capabilities
  passes                   disassembler passes
  formats                  data output formats
  classes                  knowledge representation classes
  theories                 installed theories
  agents                   knowledge providers
  rules                    knowledge base rules
  collators                project collators (comparators)
```

all of which can be further queries to `bap list`. Of particular interest are `bap list theories` and `bap list classes` which are important information about the knowledge base (listing the available "theories" which are like different interpretations or analysis of the code. `classes` lists the registered classes and their slots in the knowledge base, aka interesting fields of data you can query bap for).

`bap -dbir -dbil -dknowledge -dasm -dcfg` are different options to dump different representations of the code. BIR and BIL are two ba intermediatre representations. `-dknowledge` dumps the knowledge base which is kind of everything bap could figure out about the binary.


`bap --help` is an overwhelming amount of information. Typically you need to try to `grep` for an appropriate keyword. `bap --help | grep -C 10 keyword` will show a context of 10 lines around the found keyword. The keyword I use is often the name of bap plugin from the big list above. 


The `bap` command is the same as `bap disassemble`. The code can be found here <https://github.com/BinaryAnalysisPlatform/bap/tree/97fb7fa6a8a90faeae2b077d8ad59b8b882d7c32/plugins/disassemble>

## Bap equivalents of binutils

`objdump` let's you see various outputs about a binary.
- assembly `-d`
- symbol `-t` or `--syms`
- sections & segments  `-x`

`readelf` has some overlap.

`bap -dasm` is like `objdump -d`

`bap specification` is kind of like `readelf --all`

`bap dependencies` is similar to `ldd` I think.


## Giving Bap C info

In order for bap to recover high level function arguments you can supply a header file.
If you know this plugin is called `api` you can find the options available by 
`bap --help | grep -C 4 api`

- `--api-path=somefolder` where somefolder has a folder called C in it.
- `--api-show`
- `--api-list-paths`

### Saving and restoring the knowledge base
You can have bap save it's info and restore it. `bap a.out -k my_knowledge_base --update` will build a knowledge base. Leaving out `--update` is useful for read only access to the KB. This is used for example with `bap analyze -k my_knowledge_base`, which gives a kind of repl for exploring some pieces (but not all) of the knowledge base. Try typing `help` at the prompt for more info.

### Recipes

Recipes are bundles of command line flags I think. Well, they are at least that. This can save copying ad pasting some huge command a bunch. <https://github.com/BinaryAnalysisPlatform/bap-toolkit>  Has some interesting example recipes

### Interesting Places to Look
- Ivan's gists - https://gist.github.com/ivg
- Tests
- Defining instruction semantics using primus lisp tutorial https://github.com/BinaryAnalysisPlatform/bap/wiki/Defining-instructions-semantics-using-Primus-Lisp-(Tutorial)
- https://github.com/BinaryAnalysisPlatform/bap-toolkit Has examples recipes

# IRs
## BIL
BIL is a simple imperative language bap lifts to with unstructured control flow.
## BIR
BIR is a refinement of BIL into a CFG. Each block of BIR contains BIL statements.
## Core Theory
The inextensibility of the two above IRs has chaffed the developer's of BAP. So underneath these IRs is the Core Theory language, which is quite a machine.

Looking at the "herbrand theory" https://github.com/BinaryAnalysisPlatform/bap/blob/master/plugins/core_theory/core_theory_main.ml can help to understand core theory

I discussed this some in this blog post https://www.philipzucker.com/bap-chc/



# Disassembler
Loader, Image.

Bap has a experimental ghidra backend now btw.

The semantics of the disassembler can be extended via Primus Lisp.



# Primus Lisp
It may seem odd to mention Primus Lisp before Primus, but it has outgrown it's original intended use case there. It is interesting in and of itself.

Primus Lisp is the language by which you may add new instruction semantics to BAP lifters. See this [tutorial](http://binaryanalysisplatform.github.io/2021/09/15/writing-lifters-using-primus-lisp/) by Ivan.

It is also the language you can use you script the Primus interpreter.

There is an introduction documentation to the language [here](http://binaryanalysisplatform.github.io/bap/api/master/bap-primus/Bap_primus/Std/Primus/Lisp/index.html)

`bap --help | grep -C 10 lisp` to see what bap has to sayis available as options. Note `--primus-lisp-add` to add directories and `--primus-lisp-load` to actually load particular primus files. Leave off the ".lisp" suffix when you give the file to `load`

`bap primus-lisp-documentation` will make an org mode file of all registered primus lisp functions. You can add ocaml functions as new primitives to primus lisp. It's also online [here](http://binaryanalysisplatform.github.io/bap/api/lisp/index.html)



You can run primus lisp functions by making a file demo.lisp filled with the content

```lisp
(defun mymain ()
    (declare (external 'mymain))
    (msg "hello world"))
```

And invoke it via `bap eval-lisp mymain --primus-lisp-load=demo --primus-print-obs=lisp-message,exception`. Note that you have to turn on printing for primus observations to see anything. I always turn on message and exception at minimum.

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

# Primus

Primus is an extensible interpreter/emulator. It can execute code lifted from binaries.
You may mix and match Primus Components

The simplest way to run it is

`bap /bin/true --run --run-entry-points=main --primus-print-observations=exception,pc-change`

For more options
`bap --help | grep -C 10 run`

There is a built in taint tracking functionality and symbolic executor for primus.

You can script the primus interpreter using Primus Lisp files


## Primus

Primus is an extensible interpreter. You can use it for fuzzing, symbolic execution, taint tracking, and more.

The pieces of functionality are implemented by components. They can be mixed and matched.

To see the list of available components type

`bap primus-components`

Prepackaged combos of components are called "systems". You can see the available systems by typing

`bap primus-systems`

On my system this returns

```
- bap:constant-tracker:
  Uses promiscuous-executor for constant tracking.

- bap:microexecutor-base:
  The base system for microexecution systems.

- bap:symbolic-executor:
  Uses symbolic execution to analyze all feasible and
  linearly independent paths.

- bap:base-taint-analyzer:
  Uses promiscuous-executor for taint analysis.
  No policy is specified

- bap:binary-executor:
  Executes a binary program.

- bap:taint-analyzer:
  Uses promiscuous-executor for taint analysis.
  The default taint propagation policy is selected
  using the --primus-taint-select-default-policy
  option (defaults to propagate-by-computation)

- bap:reflective-taint-analyzer:
  A taint analyzer that reflects taints to/from BIR terms

- bap:stubbed-executor:
  Executes a binary together with the Lisp Machine

- bap:legacy-main:
  The legacy Primus system that contains all components registered with the
  Machine.add_component function.

- bap:base-lisp-machine:
  Executes Primus Lisp program.

- bap:promiscuous-executor:
  Executes all linearly independent paths and never fails.

- bap:terminating-stubbed-executor:
  Executes a binary together with the Lisp Machine that
  is guaranteed to terminate.

- bap:multi-analyzer:
  Runs several analyses in parallel.

- bap:exact-taint-analyzer:
  Uses promiscuous-executor for taint analysis.
  Propagates taint exactly.

- bap:string-deobfuscator:
  Uses promiscuous-executor to find obfuscated strings.
```

To use primus in the simplest way, you can use the bap `run` plugin. Using the `run` plugin can be confusing because key command line options are supplied to other plugins.


Now try reading the basic documentation of Primus
https://binaryanalysisplatform.github.io/bap/api/master/bap-primus/Bap_primus/Std/index.html


Under the hood, primus is extensible because you can register callbacks to certain events called "observations". This is reminscent of register event listers in a browser for example.

To see the list of available observations type

`bap primus-observations`




## Ocaml

Primus is written as a generic monad transformer. You should ignore that. Do not look in the `Machine` module. You actually want `Analysis.t` which is this monad transformer specialized to the knowledge base monad.

https://binaryanalysisplatform.github.io/bap/api/master/bap-primus/Bap_primus/Std/Primus/Analysis/index.html


### Systems
There is significant descriptive documentation of the primus machine execution cycle in the `System` module. You should read it.
https://binaryanalysisplatform.github.io/bap/api/master/bap-primus/Bap_primus/Std/Primus/System/index.html

You may write `.asd` files to describe systems. `.asd` is borrowed from the common lisp world. You can find the definition of the built in systems here
https://github.com/BinaryAnalysisPlatform/bap/blob/97fb7fa6a8a90faeae2b077d8ad59b8b882d7c32/plugins/primus_systems/systems/core.asd

There is a short tutorial in the wiki here https://github.com/BinaryAnalysisPlatform/bap/wiki/Tutorial:-writing-a-symbolic-taint-analyzer on how to make a new one.

### State

You can add new kinds of state. You need to register the state globally with a unique uuid (it's odd). It looks like this to declare state

```ocaml
let state =
  Primus.Machine.State.declare
    ~name:"unchecked-return-value"
    ~uuid:"7390b60d-fac6-42f7-b13b-94b85bba7586"
    (fun _ -> {addrs = Set.empty (module Addr); verbose=false})
```
### Forking

### Components

To make a component, write a function in the `Analysis.t` monad that registers the callbacks to the events you care about. Pass this `unit Analysis.t` to `Component.register`. That's it.

### Observations

Most observations of interest are in the `Primus.Interprete` module https://binaryanalysisplatform.github.io/bap/api/master/bap-primus/Bap_primus/Std/Primus/Interpreter/index.html

### Linker
It may surprise you that really important functionality is in the `Linker` module.

https://binaryanalysisplatform.github.io/bap/api/master/bap-primus/Bap_primus/Std/Primus/Linker/index.html


# Ocaml Stuff

### Finding Stuff
I use a combination of Merlin, Github Search.

The most interesting folders are `lib` and `plugins`

- https://github.com/ivg/bap/blob/master/lib/bap/bap.mli the bap std library
- https://github.com/ivg/bap/tree/master/lib/bap_types many bap types are actually defined here

### Bap is not a library.

Bap is organized is an extensible kind of decentralized way that I find very confusing. I am constantly tempted to treat it as a library and shoot my foot off.


## Plugins vs Commands vs Passes vs Scripts

There are at least 3 different ways you might extend bap.
### Commands 
Commands do something different than the default bap command at the top level.
- <https://binaryanalysisplatform.github.io/bap/api/master/bap-main/Bap_main/Extension/Command/index.html> This describes how to build commands with a nice example at the bottom
### Plugins

> And this is the whole idea of BAP as a framework instead of a library. There are extension points, which enable you to extend bap without having to worry about how to create a project, how to properly find the file, how to specify the architecture and other parameters. You just register a pass that takes a ready project and focus on your analysis instead of writing all this boilerplate. E.g., in the example above it is rightful to assume that you want to get the project before starting enqueing jobs, so you can register a pass that will be called once the project is ready and if the pass is selected,

- <https://binaryanalysisplatform.github.io/bap/api/master/bap-main/Bap_main/index.html> The bap main documentation. This describes extensions and building using `bapbuild` and `bapbundle`

- https://gitter.im/BinaryAnalysisPlatform/bap?at=610c3e322453386b6c373696
- https://en.wikipedia.org/wiki/Dependency_injection
Plugins are meant to be mixed and matched. They extend the functionality of other bap commands.

You make plugins by building and installing it

```
bapbuild comment.plugin
bapbundle install comment.plugin
```
Any side effects of setting up the plugin should happen inside an `Extension.declare`. It consistently causes problem that bap requires certain things to happen at certain stages, and if you go off the reservation, you'll probably eat shit.

```
let () =
  Bap_main.Extension.declare (fun _ctx -> dostuff)
```

The stuff you might do might involve declaring new slots in the knowledge base, declaring new interpetations, declaring new primus components, stuff like that.

### Scripts
"Scripts" are a thing I've made up and am not sure are actually recommended. You can make a standalone binary using that call Bap_main.init.
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
let () = match Bap_main.init () with
        | Ok _ -> ()
        | Error s -> failwith s

(* Load a file as a project *)
let myfile = "/home/philip/Documents/ocaml/a.out"
let proj = Project.create (Project.Input.file ~loader:"llvm" ~filename:myfile) |> Or_error.ok_exn

(* Getting the current knowledge base *)
let state = Toplevel.current ()

```

### Registries

A ubiquitous programming pattern in the implementation of bap is to define global level registries for various constructs.

- Plugins
- Commands
- Knowledge Base Classes
- Knowledge Base Slots
- Core Theory implementations
- Primus Components
- Primus Observations

To learn about the contents of these registries, and hence the available capaibilities, the best way is to find the appropriate way to ask the `bap` command line tool. I then use the github search feature on the bap repo to search for a important string in question.

Ivan has an Ascii Cinema here

Get some info from the Knowledge Base. 
`bap list`

### Bap Lifecycle
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
-d is dump options to bap diassemble. currently I see:
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

for example
`bap -dogre a.out`


### Saving and restoring the knowledge base
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

# Core Theory Blithering

Dumping the concrete syntax of core theory <https://gitter.im/BinaryAnalysisPlatform/bap?at=61fd525703f27047821b4c08>
`bap /bin/true --core-theory-herbrand -dknowledge`

Always try `--no-cache`

To describe the operations of different machines, bap lifts into a common intermediate representation. From the common representation you can perform different binary analysis.

The main form representation in previous version of bap was an algebraic data type, BIL. This is to some degree still the case for some purposes, but now there is a different programming construct intended as the primary source. This thing is called the the Core Theory of bap. The word "theory", strange as it sounds to some ears, refers to a common set of typed apis that analysis need to implement to receive lifted code. A "theory" in the context of logic is a set of types, functions/constants, and axioms. We don't really have axioms expressible in ocaml, but we can certainly talk about types and functions.

Instead of having analysis receive a normal ocaml algebraic data type, instead they implement a finally tagless style type signature of core_theory. Instead of registering as a pass to receive the adt, they register their core_theory instance with a global database that is typically automatically called by other parts of bap.

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

# Misc
[Brumley's old bap notes](https://github.com/dbrumley/bap-plugin-book/blob/master/bap-plugin-book.org)

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