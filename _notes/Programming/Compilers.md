---
author: philzook58
comments: true
date: 2020-11-12 20:17:39+00:00
layout: post
link: https://www.philipzucker.com/?p=2913
published: true
slug: Compilers
title: Compilers
wordpress_id: 2913
---

- [Parsing and Lexing](#parsing-and-lexing)
- [Intermediate Representations](#intermediate-representations)
  - [SSA](#ssa)
  - [LLVM IR](#llvm-ir)
  - [CPS](#cps)
  - [RTL](#rtl)
  - [Misc](#misc)
  - [Tensor Stuff](#tensor-stuff)
  - [Misc](#misc-1)
- [Analysis](#analysis)
  - [Dominators](#dominators)
  - [Dataflow](#dataflow)
  - [def-use chains](#def-use-chains)
- [Undefined behavior](#undefined-behavior)
- [Optimizations](#optimizations)
  - [Polyhedral](#polyhedral)
  - [Link Time Optimization (LTO)](#link-time-optimization-lto)
  - [Profile Guided Optimization (PGO)](#profile-guided-optimization-pgo)
- [Code Gen](#code-gen)
  - [Declarative](#declarative)
    - [Unison](#unison)
    - [Fixed Instruction Order](#fixed-instruction-order)
    - [Scheduling and Allocation](#scheduling-and-allocation)
    - [Multiple Blocks](#multiple-blocks)
    - [Register Packing](#register-packing)
  - [Rewrite Rules](#rewrite-rules)
  - [Instruction Selection](#instruction-selection)
  - [Register Allocation](#register-allocation)
  - [Instruction Scheduling](#instruction-scheduling)
  - [SuperOptimizers](#superoptimizers)
  - [Assembly Production](#assembly-production)
- [JIT](#jit)
- [Garbage Collector](#garbage-collector)
  - [Conservative vs Exact](#conservative-vs-exact)
  - [Parallel](#parallel)
  - [Concurrent](#concurrent)
  - [mark and Sweep](#mark-and-sweep)
  - [Generational](#generational)
- [Misc](#misc-2)
  - [LLVM](#llvm)
- [JVM](#jvm)


# Parsing and Lexing
- See note on parsing

# Intermediate Representations
## SSA
http://ssabook.gforge.inria.fr/latest/book.pdf SSA bookv
[mirror of ssa book](https://github.com/pfalcon/ssabook)
[actually published?](https://link.springer.com/book/10.1007/978-3-030-80515-9)

[compcertssa](http://compcertssa.gforge.inria.fr/) verified ssa

[bril](https://github.com/sampsyo/bril) educational IR. ocaml and rust bindings.

[Simple and Efficient Construction of Static Single
Assignment Form](https://pp.info.uni-karlsruhe.de/uploads/publikationen/braun13cc.pdf) https://twitter.com/peter_a_goodman/status/1541105429215936513?s=20&t=Id3zoB1xCWLA5QQIrPNHVA

## LLVM IR
See LLVM section



## CPS
## RTL

## Misc
## Tensor Stuff
ILang
Tiramisu http://tiramisu-compiler.org/Comparison.html
MLIR
Halide
TVM
BYOC bring your own codegen https://tvm.apache.org/2020/07/15/how-to-bring-your-own-codegen-to-tvm


http://www.gilbertbernstein.com/resources/LiuPOPL2022.pdf ATL verified "scheduling" rewrites in coq - Gilbert. Gilbert works on coolstuff  http://www.gilbertbernstein.com/

[exo](https://github.com/exo-lang/exo)

https://princetonuniversity.github.io/isca22-ila-tutorial/ ILAlang
## Misc

[esolang VM](https://github.com/shinh/elvm) - C compiler to simple virtual machine for compiling to esolangs

[exo-lang.dev] exocompilation
# Analysis

## Dominators

Everyone talks about dominators.
Graph algorithms over the coaurse structure of the cfg itself.

https://llvm.org/devmtg/2017-10/slides/Kuderski-Dominator_Trees.pdf

a node x domainates another y if every path through y goes through x

postdominator, every path to exit has to pass throguh. Dual of domaintor

every def must dominate use

intersection of sets of dominators of your predecssors


Dominator trees
loop nesting forests

## Dataflow
Dataflow analysis
https://en.wikipedia.org/wiki/Data-flow_analysis
Must/May and intersection vs union. Least fixed point vs greatest

Kildall
bitvector


reaching definitions
live variable
very busy expressions
available expressions

## def-use chains
https://en.wikipedia.org/wiki/Use-define_chain

# Undefined behavior
undefined vs implementation defined.

undefined behavior:
The compiler is allowed to do anything? Represents things that trap. Stuff like divide by zero
The compiler may optimize code assuming undefined behavior never happens. It is free to make code more defined
 int wraparound

Poison undef
llvm IR has some surprising values available in it's semantics. Varables can hold _sets_ and poison. Poison is a special marker value that infects things. undef creates a set of a all possible values

[Towards Optimization-Safe Systems: Analyzing the Impact of Undefined Behavior](https://dl.acm.org/doi/pdf/10.1145/2517349.2522728)

[What Every C Programmer Should Know About Undefined Behavior #1/3](http://blog.llvm.org/2011/05/what-every-c-programmer-should-know.html)
[Undefined Behavior != Unsafe Programming](https://blog.regehr.org/archives/1467) "The essence of undefined behavior is the freedom to avoid a forced coupling between error checks and unsafe operations."

Refinement checking
alive2

# Optimizations

[Wikiepedia list of compiler optimizations](https://en.wikipedia.org/wiki/Optimizing_compiler)

- Common subexpression elimination
- Peephole

[Loop invariant code motion](https://en.wikipedia.org/wiki/Loop-invariant_code_motion) - aka hoisting. Move stuff that doesn't change out of the loop

[value numbering](https://en.wikipedia.org/wiki/Value_numbering)
hash consing kind of. Superlocal blocks. every block has only one predecessor. Not quite the same as loop free?
[value numbering in gcc talk](https://www.youtube.com/watch?v=oNeAtmsDfK0&ab_channel=SUSELabs)


loop unrolling

[instruction level parallelism](https://link.springer.com/book/10.1007/978-1-4899-7797-7) Alex Aiken Utpal Banerjee Arun Kejariwal Alexandru Nicolau

Reassociate to lessen tree height - less dependencies
Expand expressions with care - less dependencies

[Implementing a Toy Optimizer](https://twitter.com/cfbolz/status/1549376580912386051?s=12&t=2TzLXakPIAt6RPwcq4Qz9w)

[liveness analysis for ssa form program](https://hal.inria.fr/inria-00558509v2/document) 



## Polyhedral
[Polyhedral model](https://en.wikipedia.org/wiki/Polytope_model)
[Foundations of Fine Grain Parallelism](https://www.cs.colostate.edu/~cs560/Fall2015/). Recurrence equations. Analyze them
[granulairty](https://en.wikipedia.org/wiki/Granularity_(parallel_computing)) 

[Polyhedral Compilation as a Design Pattern for Compilers PLISS](https://www.youtube.com/watch?v=mt6pIpt5Wk0&ab_channel=PLISS)

isl and presburger arithmetic.
A relative of omega?

FPL - fast presburger arithmetic

## Link Time Optimization (LTO)
- See note on Linker

## Profile Guided Optimization (PGO)

# Code Gen
## Declarative
- [Relational Processing for Fun and Diversity](https://personal.utdallas.edu/~hamlen/lundquist19minikanren.pdf) minikanren
- [Denali - a goal directed super optimizer](https://courses.cs.washington.edu/courses/cse501/15sp/papers/joshi.pdf) egraph based optimization of assembly
- [PEG](https://cseweb.ucsd.edu/~lerner/papers/popl09.pdf) egraph cfg
- [RVSDG](https://github.com/egraphs-good/egg/discussions/106)
- [minimips minikanren mips assembler/disassembler](https://github.com/orchid-hybrid/minimips)
- [Parsing and compiling using Prolog](https://dl.acm.org/doi/abs/10.1145/22719.22946) There is also a chapter in the art of prolog

### Unison
- [Unison](https://unison-code.github.io/)

[diversification](http://www.diva-portal.org/smash/get/diva2:1232129/FULLTEXT01.pdf) make many versions of binary to make code reuse attacks harder. disunison


Toy Program:


If you do liveness analysis ahead of time, it really does become graph coloring, with an edge between every temporary that is live at the same time.

You cannot do liveness ahead of time if you integrate instruction scheduling with allocation. It needs to be internalized.

If you do SSA ahead of time, you have more flexibility to change colors/register at overwrite points

How to communicate to minizinc:
- Serialized files or C bindings
- Parameters or constraints. In some sense, you a writing a constraint interpreter over the parameters. Why not cut out the middleman? 1: less clear what the structure is. 2. It forces your hand with the bundling of different pieces. Many things need to be bundled into the `insn` predicate unless you reify the `insn` predicate to a variable, in which case you are rebuilding the parameter version.

There is a spectrum of more or less complex models you can use.

### Fixed Instruction Order
This makes a DSL in minizinc that looks like a somewhat reasonable IR. It uses a predicate function `insn` that takes in the lhs and rhs temporaries. It assigns a register to each temporary such that it never clobbers a live variable.

I could do the liveness analysis completely statically, but I choose to internalize it into the model for ease.

```minizinc
enum reg_t = {R0, R1, R2, R3};
enum temp_t = {T0, T1, T2, T3, T4, T5};
int : MAXID = 5;
set of int : operation_t = 0..MAXID;

array[temp_t, operation_t] of var bool : live_in;
array[temp_t] of var reg_t : reg;

predicate insn(operation_t : id, list of temp_t : lhs, string : opcode, list of temp_t : rhs) = 
  % https://en.wikipedia.org/wiki/Live_variable_analysis
  forall(t in temp_t)(
    if (t in rhs) % in gen set
      then live_in[t, id] = true
    elseif (t in lhs) % not in gen set, in kill set
      then live_in[t,id] = false
    else % propagate
      live_in[t,id] <- live_in[t, id + 1] 
    endif) /\
  % Assignments need to go to different registers than live variables of next instruction.
  forall(t1 in lhs)(
    forall(t2 in temp_t where t1 != t2)(
      live_in[t2,id+1] -> reg[t1] != reg[t2]
  ));

% Nothing is live at end of block
constraint forall(t in temp_t)( live_in[t, MAXID] = false);

constraint 
  insn(0, [T1], "mov", [T0])     /\
  insn(1, [T2], "add", [T0, T1]) /\
  insn(2, [T3], "sub", [T0, T1]) /\
  insn(3, [T4], "mul", [T1, T2]) /\
  insn(4, [T5], "inc", [T4]);


%reg = [T0: R2, T1: R0, T2: R1, T3: R2, T4: R0, T5: R0];
%live_in = 
%[|         0:     1:     2:     3:     4:     5: 
% | T0:  true,  true,  true, false, false, false
% | T1: false,  true,  true,  true, false, false
% | T2: false, false,  true,  true, false, false
% | T3: false, false, false, false, false, false
% | T4: false, false, false, false,  true, false
% | T5: false, false, false, false, false, false
% |];
%----------

% if we're not in ssa, maybe 
% array[temp_t, id] of var reg_t; 
% since register can change as reuse site.

% Registers don't allocate to same spot
%constraint forall (id in operation_t)(
%  forall(t1 in temp_t)(
%    forall(t2 in temp_t)(
%      (live_in[t1,id] /\ live_in[t2,id] /\ t1 != t2) ->
%      reg[t1] != reg[t2]
%    )));


```

How do you want to talk about the solution space.
- a next(id1,id2) matrix
- live[id,t] matrix vs start end cycle integers.

 % since we don't record the gen kill sets we need to do this in here.
`% next[i,j]` where you see `id + 1` 
I was assuming SSA, but maybe it can handle non ssa? Noo. It probably can't.

### Scheduling and Allocation
We can also use a next[i,j] matrix or change live to a start end cycle parameter.


### Multiple Blocks
### Register Packing
Using the rectangle packing constraint for register modelling



## Rewrite Rules
peephole optimization
[cranelift isle](https://github.com/bytecodealliance/wasmtime/blob/918671316301306d653345cc3486f0a15de2aa50/cranelift/docs/isle-integration.md)
[Verifying and Improving Halide’s Term Rewriting System with Program Synthesis](https://dl.acm.org/doi/pdf/10.1145/3428234)

See: e-graphs
[scheduling using unimodular modelling](https://twitter.com/taktoa1/status/1531386684876632064?s=20&t=-IHVNfpCMKlhva0T8ctWXA)

## Instruction Selection
Maximal munch parsing
http://www.cs.cmu.edu/afs/cs/academic/class/15745-s07/www/lectures/lect9-instruction_selection_745.pdf
Like parser generators / libraries, you can make instruction selection libraries / generators. Bottom up vs top down
- TWIG BURG BEG bottom up generate instruction selectors
- 

[iburg](https://old.reddit.com/r/Compilers/comments/edgx5s/successors_to_iburg/) https://github.com/drh/iburg a code generator generator

[Synthesizing an Instruction Selection Rule Library from Semantic Specifications](https://pp.ipd.kit.edu/uploads/publikationen/buchwald18cgo.pdf)

Subgraph isomorphism problem
VF2 algorithm
Very similar to "technology mapping" in the vlsi community.

type aexpr = Mul | Add

Macro expansion
 - procede bottom up
Maximal Munch

Instruction selection is taking a program and figuriing out which instructions can be used to implement this. Typically this leaves behind still some problems to solve, in particular register allocation and instruction scheduling. Presumably, everything in the program needs to be done. We have some notion of correspondence between the program representation and the available instructions. The exact nature of this correspondence depends on how we represent our program.

- Sequence
- Tree - One representation of a program might be as a syntax tree, say `(x + (y * z))`.
- DAG - consider `(x + y) * (x + y)`. Really we want to note common shared computation and not recompute `x+ y` twice. DAGs and the technique of hash consing can be useful here.
- Tree-like DAGS
- CFG - A different representation might be to separate out blocks and control edges between them. Blocks consist of a sequence of statements.

If the statements are purely for assignment, assignment can be inlined. The block is nearly purely functional in some sense. It can be compressed into a functional form like the DAG or Tree by inlining. The block could also itself be considered as a graph, as there is often more then one equivalent way of sequencing the instructions.

The simplest case to consider is that of the tree. We can enumerate patterns in the tree that we know how to implement using instructions. The relationship between tree patterns and instructions can be many-to-many. We should understand how to implement every node in the tree `(?a + ?b)`, `(?a * ?b)` with a pattern consisting of a sequence of instructions for completeness (ability to compile any tree). We also should try to figure out the tree patterns that correspond to a single assembly instruction like `load reg [reg+n]` because these will often be efficient and desirable.

There are two distinct and often separable problems here:
1. Find pattern matches
2. Pick which matches to actually use aka pattern selection


A direct approach to describing patterns is to develop a datatype of patterns. This datatype will be basically the datatype of your AST with holes. This is clearly duplication and becomes painful the more constructors your language has, but whatever.

```ocaml
type ast = Add of ast * ast | Var of string
type ast_pat = Hole of string | PAdd of ast_pat * ast_pat | PVar of string

pmatch : ast_pat -> ast -> (string * ast) list option
```

Alternatively, we can note that the main point of a pattern is to pattern match and use a church-ish/finalish representation

```ocaml
type ast_pat' = ast -> (string * ast) list option
let convert_pat' : ast_pat -> ast_pat' = pmatch
```

```ocaml
type var = string
type stmt = Ass of var * expr
type expr = Add of var * var | Var of var

type blk = stmt list

let inline : blk -> (var * ast) list
type insn = Mov of reg * reg | Add of reg * reg | Add2 of reg * reg * reg


```

A novelty of the Blindell et al work is the notion of universal function (UF) graph. There is both the functinal repsentation of data values, but also cfg is represented as opaque nodes. The correspondence of where values are defined and where computations happen is left up to the constraint solver.

What is the input language? Is it a pure expression langage? A side effectful imperative language? We can convert between these.

I have directly gone to effectful assembly from pure expression language above.

I understand enough to have many questions. What is the input language over which one is pattern matching. Perhaps language is already the wrong word since language tends to imply something tree-like. Is it a pure language or an imperative language. Is it represented as a sequence of IR instructions, a tree, tree-like dag, dag,  a graph, or something else. Is represented too weak a word for this question which seems to be very important? "BIL" represented as a sequence vs as a graph might as well be nearly entirely different things. It seems totally possible to translate between pure and imperative, and between the representations and yet it matters so much. What is the output language. It structurally isn't concrete assembly in many ways. It is definitely un-register allocated and probably unsequenced. Sometimes it feels like tree-like quasi assembly, where the node represents an "output" register even though assembly is really just a sequence of effects. Is there freedom to choose any N^2 combination of structural representations between input and output languages, purity and impurity?  None of this even starts to touch control flow. None of this touches what does "overlapping" of patterns mean and what should be allowed

Sequenced representation: Patterns may need to stretch over bits / reorderings. The sequence of the input language does not at all have to be the sequence of the output. Restricting yourself in this way

You can often macro repeat patterns in ways to undo any arbitrary choices made by the representation. Some kind of quotienting. If we have an order free representation, we could aebitrary sequence it, and then sequence the patterns into all possible sequencings. Then you end up with baically the same thing. You can't go the other way in general. 
There is something that feels galois connection-y here.

What is the output of pattern matching? Typically I would consider the output of a pattern match to be just pattern variable bindings. But in this case, really we may need full identification between pattern nodes and pattee nodes since this defines the covering.

There are different axes upon which to consider graph variations
- input/output Edges ordered or unordered / have identity are interchangeable. AST tree have identity. Consider the example of a power or any non commutative operation. Edges with identities may want to be considered to be attached to "ports"
- Zero/many input output edges (trees)
- Labels on vertices and or edges

Different kinds can be embedded in each other.
Trees can represent graphs if you are allowed to indirectly refer to nodes via labels.
Hash cons dags can have many input and output edges. However the output edges of the hash cons are unported, whereas the input edges are ported. The symmettry can be improved by using projection/port nodes connected to the output. In some sense the output of the original is then
Operads

You could take a relational perspective on operations, having neither input not output.

## Register Allocation
[iterated register coalescing - appell and george](https://c9x.me/compile/bib/irc.pdf)
move edges are considered special because the can be coalesced (collapse the node in the interference graph)
nodes with less than number of register nighbors can be removed and you can construct a coloring
conservative coalescing -
constants can be spilled cheaply via rematerialization




[regallo2 design doc](https://github.com/bytecodealliance/regalloc2/blob/main/doc/DESIGN.md)

[flambda reg alloc](https://github.com/ocaml-flambda/flambda-backend/pull/678) points to an [appell paper - iterated register coalescing](https://dl.acm.org/doi/abs/10.1145/229542.229546) and tiger book
<https://arxiv.org/abs/1804.02452>

[cranelift regalloc](https://cfallin.org/blog/2022/06/09/cranelift-regalloc2/) great blog post

[Register Allocation: What Does the NP-Completeness Proof of Chaitin et al. Really Prove? Or Revisiting Register Allocation: Why and How](https://link.springer.com/chapter/10.1007/978-3-540-72521-3_21#:~:text=Abstract,graph%20associated%20to%20the%20variables.)

[The Solid-State Register Allocator](https://twitter.com/impraxical/status/1577321303400452100?s=20&t=UJrepWvNkFpXFRNY8yoWDA) https://www.mattkeeter.com/blog/2022-10-04-ssra/
Belady's OPT algorithm page faults

[The Power of Belady’s Algorithm in Register Allocation for Long Basic Blocks](http://polaris.cs.uiuc.edu/publications/guo-2003-old.pdf)
[efficient global register allocation](https://arxiv.org/abs/2011.05608)

[linear scan register allocation](http://web.cs.ucla.edu/~palsberg/course/cs132/linearscan.pdf)

The typical starting point of register allocation is support you've been given as assembly program that doesn't have registers filled in like
```assembly
# input v1 v2 v3
mov v1, v2
add v1, v1
mul v3, v1
# output v3
```
The interference graph has an edge between any two variables that are live at the same time.
Live means that the variable has been made and someone still needs to use it now or later.
In this example, if we assume v1 v2 & v3 are live at the beginning, v1 is live for all 3 instructions, v3 is live for all three and at the output, but v2 is only live at the first instruction since it is never used again.

[dsatur graph coliring heurisitc](https://en.wikipedia.org/wiki/DSatur)

[RL4ReAl: Reinforcement Learning for Register Allocation](https://twitter.com/johnregehr/status/1513561374873464833?s=20&t=NBROMONLYyqlU8uerfss0A)
Compiler gym

## Instruction Scheduling
The pure instruction scheduling problem might occur even at the IR level. We can imagine an imperative IR. Certain operations commute and others don't. We may want to minimize the liveness time of variables for example. This would make sense as a pre-processing step to a sequence input language to an instruction selector.


Instruction scheduling can be parametrized as:
1. an embedding into actual time (cycle issue time probably). This is important if you are optimizing for runtime and can get estimates of how long each instruction takes.
2. a ranking as integers
3. next(i,j) relation which is basically integers. Allows for partial order. after(i,j) :- next(i,k), after(). after is path connected in temporal dag. Possibly this is mappable into a lattice notion of time (i,j,k,etc)?

## SuperOptimizers
https://en.wikipedia.org/wiki/Superoptimization

[Superoptimizer -- A Look at the Smallest Program ](https://web.stanford.edu/class/cs343/resources/superoptimizer.pdf) Massalin
https://news.ycombinator.com/item?id=25196121 discussion

- Souper https://github.com/google/souper https://arxiv.org/pdf/1711.04422.pdf
- STOKE https://cs.stanford.edu/people/eschkufz/docs/asplos_13.pdf
- TOAST an ASP based one?

https://twitter.com/kripken/status/1564754007289057280?s=20&t=KWXpxw5bjeXiDnNeX75ogw Zakai binaryen superopitmizer


## Assembly Production
You need to produce actual binary, actual 1s and 0s
See also:
- Linking
- Assembly



# JIT
de-optimization paths
[mir](https://github.com/vnmakarov/mir) an intermiedtae representation for JIT
[qbe](https://c9x.me/compile/)
[libjit](https://www.gnu.org/software/libjit/)
[ryujit](https://github.com/dotnet/coreclr/blob/master/Documentation/botr/ryujit-overview.md)
[libfirm](https://github.com/libfirm/libfirm)
[cranelift](https://github.com/CraneStation/cranelift)
[nanojit](https://github.com/dibyendumajumdar/nanojit)

[libgccjit](https://gcc.gnu.org/onlinedocs/jit/)

[copy and patch compilation](https://twitter.com/cfbolz/status/1516418354579394566?s=20&t=7564nBvc82Jdkz_E3ccZbA)

[asmjit](https://github.com/asmjit/asmjit) https://asmjit.com/ lightweight library for machine code generation

# Garbage Collector

https://github.com/mflatt/gc-demo
https://www.youtube.com/playlist?list=PLbdXd8eufjyVCrWF-obj8_BbyU5vEF8Jw


[treadmill gabrage collector of baker](https://news.ycombinator.com/item?id=32233472) http://www.cofault.com/2022/07/treadmill.html

[garbage collection handbook](https://gchandbook.org/ )
[lua wiki](http://wiki.luajit.org/New-Garbage-Collector#gc-algorithms_quad-color-optimized-incremental-mark-sweep)

real-time
concurrent
copying vs non-copying. Copying needs to adjust pointers. Can defragment
incremental - does the garbage collection need to happen all at once

bump allocation


## Conservative vs Exact

The boehm garbage collector seems easy to use. Also you can just malloc and never free.
https://en.wikipedia.org/wiki/Boehm_garbage_collector



## Parallel
## Concurrent
## mark and Sweep
colors mark finished, seen but children not finished.
white is unseen. black is swept. When finished anything white is no longer in use.
## Generational


Making a simple garbage collector [https://maplant.com/gc.html](https://maplant.com/gc.html)



# Misc
[Proving the correctness of a compiler - Xavier Leroy](https://xavierleroy.org/courses/EUTypes-2019/) summer course

[UMD compiler course](https://www.cs.umd.edu/class/spring2021/cmsc838E/index.html)

[Compilers are databases](https://www.youtube.com/watch?v=WxyyJyB_Ssc&ab_channel=Java)

[c-pit-claudel relational compilation](https://people.csail.mit.edu/cpitcla/thesis/relational-compilation.html)

```prolog
% This looks like a job for difference lists
compile(lit(n), [push(n) | TS]).
compiler(opp(T),  ).
compile(add(X,Y), [Z | TS] :- compile(X,X1), compile(Y,Y2), append(X1,Y1,Z), append(Z,Rest,TS).
```
prolog using coq.





[Query-based compiler architectures](https://ollef.github.io/blog/posts/query-based-compilers.html)

[Anders Hejlsberg on Modern Compiler Construction](https://www.youtube.com/watch?v=wSdV1M7n4gQ&ab_channel=Googol)

incremental compilation

[Calculating correct compilers](https://www.cs.nott.ac.uk/~pszgmh/ccc.pdf)

[cs6120 adrian sampson](https://www.cs.cornell.edu/courses/cs6120/2022sp/lesson/) Looks like a nice syllabus

[rose compiler](https://en.wikipedia.org/wiki/ROSE_(compiler_framework)) source to source compiler? Makes sense.


[compiler optimizations website](https://compileroptimizations.com/)

  * [https://github.com/aalhour/awesome-compilers](https://github.com/aalhour/awesome-compilers)

  *  [https://gcc.gnu.org/wiki/ListOfCompilerBooks](https://gcc.gnu.org/wiki/ListOfCompilerBooks)







- interesting links <https://twitter.com/1101_debian/status/1456346324794806274?s=20>
<https://news.ycombinator.com/item?id=29112482> more links

<cs.au.dk/~amoeller/spa> static program analysis

modules - global symbols, function declaration, function definitions, target information





<https://gist.github.com/MattPD/00573ee14bf85ccac6bed3c0678ddbef> program analysis resources. Big long list.






Man souffle does seem cool





It's surprisingly difficult to find a cogent explanation of all the stuff one might need. It's useful to call C or be called from C **https://blog.packagecloud.io/eng/2016/04/05/the-definitive-guide-to-linux-system-calls/**


    
    <code>	.globl compute_42
    compute_42:
        movq    %rdi, %rax # move argument into rax
    	addq	$32, %rax # add 32 
    	retq
        
    
    #include <stdio.h>
    #include <stdint.h>
    
    extern uint64_t compute_42(uint64_t a);
    
    int main()
    {
        printf("result is %ld \n", compute_42(4));
        return 0;
    }</code>





sjklsfkjl https://cs.brown.edu/courses/cs033/docs/guides/x64_cheatsheet.pdf x86 cheatsheet


alignment is for serious. It really does screw you if you don't do function alls with stack on 16byte boundaries


[https://en.wikibooks.org/wiki/X86_Assembly](https://en.wikibooks.org/wiki/X86_Assembly)


[https://modernc.gforge.inria.fr/](https://modernc.gforge.inria.fr/) modern c book free online


%rdi, %rsi, %rdx, %rcx, %r8, and %r9 as first 6 arguments


pushq %rbx is usually first instruction inside function


subq somethign rsp usually happens to allocate on the stack


[https://brown-cs0330.github.io/website/index.html](https://brown-cs0330.github.io/website/index.html) introduction to computer systems

Bryant and OHallaran book. CMU course http://www.cs.cmu.edu/~213/schedule.html

[https://bernsteinbear.com/blog/lisp/](https://bernsteinbear.com/blog/lisp/)

gdb. Compile with -g flag. break main. step next print. tui enabe https://sourceware.org/gdb/onlinedocs/gdb/TUI-Commands.html#TUI-Commands cheatsheet https://darkdust.net/files/GDB%20Cheat%20Sheet.pdf https://brown-cs0330.github.io/website/docs/guides/vgg.pdf

objdump -d -S -l

valgrind and core dumps.

## LLVM
LLVM IR

MIR

Instruction Combiner

  * [https://www.cs.cornell.edu/~asampson/blog/llvm.html](https://www.cs.cornell.edu/~asampson/blog/llvm.html)

<https://jonathan2251.github.io/lbd/index.html>  Tutorial: Creating an LLVM Backend for the Cpu0 Architecturehttps://danielkeep.github.io/tlborm/book/README.html

<https://www.youtube.com/watch?v=m8G_S5LwlTo&ab_channel=LLVM> LLVM IR tutorial

[llvm-mca](https://llvm.org/docs/CommandGuide/llvm-mca.html) - static analysis of performance of code 

<https://www.llvm.org/docs/ProgrammersManual.html>
<https://mukulrathi.com/create-your-own-programming-language/llvm-ir-cpp-api-tutorial/>

[Learning to combine instructions in LLVM compiler](https://twitter.com/johnregehr/status/1501649959505985537?s=20&t=-ebjuD7WRIIQNgiBChK5cQ)
<https://lowlevelbits.org/how-to-learn-compilers-llvm-edition/> 
# JVM



