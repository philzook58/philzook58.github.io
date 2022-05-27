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

- [Lexing](#lexing)
  - [Regular Expressions](#regular-expressions)
- [Parsing](#parsing)
  - [Algorithms](#algorithms)
  - [Parser Combinators](#parser-combinators)
  - [Parser Generators](#parser-generators)
- [Intermediate Representations](#intermediate-representations)
  - [SSA](#ssa)
  - [LLVM IR](#llvm-ir)
  - [CPS](#cps)
  - [RTL](#rtl)
  - [Misc](#misc)
- [Analysis](#analysis)
  - [Dataflow](#dataflow)
- [Optimizations](#optimizations)
  - [Link Time Optimization (LTO)](#link-time-optimization-lto)
  - [Profile Guided Optimization (PGO)](#profile-guided-optimization-pgo)
- [Code Gen](#code-gen)
  - [Declarative](#declarative)
    - [Unison](#unison)
    - [Fixed Instruction Order](#fixed-instruction-order)
    - [Scheduling and Allocation](#scheduling-and-allocation)
    - [Multiple Blocks](#multiple-blocks)
    - [Register Packing](#register-packing)
    - [Other](#other)
  - [Instruction Selection](#instruction-selection)
  - [Register Allocation](#register-allocation)
  - [Instruction Scheduling](#instruction-scheduling)
  - [Assembly Production](#assembly-production)
- [JIT](#jit)
- [Garbage Collector](#garbage-collector)
  - [Conservative vs Exact](#conservative-vs-exact)
  - [Parallel](#parallel)
  - [Concurrent](#concurrent)
  - [mark and Sweep](#mark-and-sweep)
  - [Generational](#generational)
- [Misc](#misc-1)
  - [LLVM](#llvm)
- [JVM](#jvm)
# Lexing

## Regular Expressions

https://regex101.com/
https://regexr.com/

# Parsing
I personally do not enjoy front end issues as much as back end. And yet a front to back compiler course starts there. Kind of off putting.

BNF
Context Free Grammars
[Parsing Expression Grammar](https://en.wikipedia.org/wiki/Parsing_expression_grammar)
LL
LALR

[How do you get good error messages](https://twitter.com/SandMouth/status/1513173009976147975?s=20&t=5y91-I1SPrIGomAWSqs69w)

[sy brand paper on how compilter diagnostics could be imporved](https://twitter.com/TartanLlama/status/1527327581464567809?s=20&t=C_oktCkKA7nprGoHnJpglQ)

## Algorithms
[List of algorithms - parsing](https://en.wikipedia.org/wiki/List_of_algorithms#Parsing)
Recursive Descent
Earley parser
Pratt Parser
LL Parser
LR Parser
packrat
allstar

## Parser Combinators
`String -> [(a,String)]` A non deterministic search that consumes a prefix of the input.
parsec

## Parser Generators


Flex
yacc/bison
antlr
Menhir [error handling the new way](http://cambium.inria.fr/~fpottier/menhir/manual.html#sec68)
Sam's coq stuff <https://github.com/slasser/AllStar> <https://github.com/slasser/CoStar>


Semantic Actions



# Intermediate Representations
## SSA
http://ssabook.gforge.inria.fr/latest/book.pdf SSA bookv
[mirror of ssa book](https://github.com/pfalcon/ssabook)

[compcertssa](http://compcertssa.gforge.inria.fr/) verified ssa

[bril](https://github.com/sampsyo/bril) educational IR. ocaml and rust bindings.
## LLVM IR
See LLVM section


## CPS
## RTL

## Misc
ILang
Tiramisu http://tiramisu-compiler.org/Comparison.html
MLIR
Halide
TVM
BYOC bring your own codegen https://tvm.apache.org/2020/07/15/how-to-bring-your-own-codegen-to-tvm

[esolang VM](https://github.com/shinh/elvm) - C compiler to simple virtual machine for compiling to esolangs

# Analysis
## Dataflow
Dataflow analysis
Must/May and intersection vs union. Least fixed point vs greatest


# Optimizations

[Wikiepedia list of compiler optimizations](https://en.wikipedia.org/wiki/Optimizing_compiler)

[Loop invariant code motion](https://en.wikipedia.org/wiki/Loop-invariant_code_motion) - aka hoisting. Move stuff that doesn't change out of the loop

[instruction level parallelism](https://link.springer.com/book/10.1007/978-1-4899-7797-7) Alex Aiken Utpal Banerjee Arun Kejariwal Alexandru Nicolau

Reassociate to lessen tree height - less dependencies
Expand expressions with care - less dependencies

[Polyhedral model](https://en.wikipedia.org/wiki/Polytope_model)
[Foundations of Fine Grain Parallelism](https://www.cs.colostate.edu/~cs560/Fall2015/). Recurrence equations. Analyze them
[granulairty](https://en.wikipedia.org/wiki/Granularity_(parallel_computing)) 

[Polyhedral Compilation as a Design Pattern for Compilers PLISS](https://www.youtube.com/watch?v=mt6pIpt5Wk0&ab_channel=PLISS)

isl and presburger arithmetic.
A relative of omega?

[liveness analysis for ssa form program](https://hal.inria.fr/inria-00558509v2/document)

## Link Time Optimization (LTO)
- See note on Linker

## Profile Guided Optimization (PGO)

# Code Gen
## Declarative
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
  insn(4, [T5], "inc", [T4]) ;

array[temp_t, operation_t] of var bool : live_in; %live_in
array[temp_t] of var reg_t : reg;
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

### Other
- [Relational Processing for Fun and Diversity](https://personal.utdallas.edu/~hamlen/lundquist19minikanren.pdf) minikanren
- [Denali - a goal directed super optimizer](https://courses.cs.washington.edu/courses/cse501/15sp/papers/joshi.pdf) egraph based optimization of assembly
- [PEG](https://cseweb.ucsd.edu/~lerner/papers/popl09.pdf) egraph cfg
- [RVSDG](https://github.com/egraphs-good/egg/discussions/106)
- [minimips minikanren mips assembler/disassembler](https://github.com/orchid-hybrid/minimips)

## Instruction Selection
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
<https://arxiv.org/abs/1804.02452>

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

# Garbage Collector
## Conservative vs Exact

The boehm garbage collector seems easy to use. Also you can just malloc and never free.

## Parallel
## Concurrent
## mark and Sweep
## Generational


Making a simple garbage collector [https://maplant.com/gc.html](https://maplant.com/gc.html)

# Misc

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



