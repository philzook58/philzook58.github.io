
Title:
Binary Metadata and Why care
Why care about binary metadata



Why care?
- Verification
- Faster recompilation via fine grained linking
- Low cost dynamism. It isn't persay that . Some cool aspects of dynamic languages are possible because they maintain data structures describing their world. Static compiler don't do this because the data structures and indirections have runtime cost. Metadata is a zero cost way to carry this extra stuff. Having stratified universes of modification rather than the dynamics world of mixed. You batch together modifications / memoize them in some sense.
- ABI on steroids. The ABI has serious cost. But imagine if the ABI was described in metadata. Then you could use whatever calling conventions you want, and other's could still call you. Bespoke ABI
- 
- Possibly faster and . LTO.


Feedback is important. We need to _use_ this data for it to stay accurate. The format must be verifiable without inspecting the process that produced it or have a concrete use where testing will reveal issues. Debug info doesn't have this and that is the problem. Decompilation likewise.



What are the commonalities of all programming languages.

Language workbenches


## GTIRB

What are the commonalities of all reverse engineering IRs.

Every IR has it's own notion of semantics. It is very difficult to map these semantics to each other.

THey are ultimately talking about the same binary though. And the coarse strokes of their representations are largely the same.

GTIRB should be packed with the binary and output by compilers in the first place. It is a form of debug data. 



## Disassembly Problems

Disassembly is hard. This was a surprise to me at some point.
Part of the issue is that the word disassembly might mean different problems to different people.
Indeed taking a given set of bits and mapping it to an assembly instruction is not conceptually hard. This process might also go by the name disassembly.

However, suppose I gave you a binary with

```
0x47839247836587926475634978256783625
7894725041580436258465071543705736406
308756784657843
```

Well, actually no. That was the text of Mary Had a Little Lamb.

- Variable Width Instructions. Now we don't know which bytes at which instructions start
- Interspersed data and instructions.

We can overapproximate the set of instructions by just disassembling every byte offset. Then the task is to try to trim this set down to the actually valid instructions.

This may be important because some very cheeky assembly techniques may involve punning the same sets of bytes at different instructions. This may happen in ROP chain attack for example or see E9patch.

This is because disassembly is interwined with control flow.

Finally, the term disassembly may correspond to constructing a control flow graph. Direct jumps are not difficult, but indirect jumps based on a calculated value may be very difficult. 





# Debugging, High and Low

Debugging is a form of runtime patching.
You could insert a breakpoint at the patch point, run an interpreter, and then return control flow at the appropriate place.

Debugging info is the main place where people have reified the connection between high and low programs.
It is meant for interactive human use.





## DWARF
DWARF is designed to be agnostic to both archtitecture and high level programming language.

There are a variety of very generic notions that languages can make a notion of

Let us try to note some highly obvious and (basically) universal observations.
- Every language has concrete syntax.
- Binary Encoding. 


As indicative of high level languages, let us consider
- C
- Rust
- Python
- C++
- Javascript
- OCaml
- Haskell


High level languages have:
- Variables
- Statements
- Expressions
- Types
- Functions
- Structured control. if/then/else, while, switch


- Intructions
  + Move
  + Arithmetic instructions
  + Load/Store
  + Direct Jumps
  + Indirect Jumps
  + Call
  + Memory Fence
  + Conditionally exectuable instructions
  + Delay slots
  + 

For instruction sets let us consider the commonalities of
- x86
- ARM
- RISC-V
- PowerPC
- AVR


For IRs let us speak of
- LLVM IR
- LLVM MIR
- GCC whatsy
- Pcode
- BAP BIR
- C minus minus
- STG
- Lambda

WHat do these all have in common
- Edges
- Blocks
- 


Relocatable assembly

Anything more niche than these, you're going to have to make an argument to me for why I should pay attention to it.

High level languages intensionally do not make guarantees about what calculations they actually perform.

They define observable behavior instead. 
People get puzzled by pure functional programming languages. If you can't print or write, how can there be any observation? Then the program is free to optimize into nothingness.

A high level program produces a sequence of observable effects. A low level program also producs a sequence of observable effects.


You may write a straightforward interpreter for a language, but not every notion or piece of state or action this interpreter performs 

There is however _often_ significantly more correspondence between the code output by a compiler than the Spec specifically guarantees.

What _is_ observable?

Concurrency, debugging, and micropatching make events observable that were not meant to be observable.

To make every event observable means the compiler writer has no freedom to optimize code ad the hardware designed has no freedom to perform parallelism and caching under the hood. And ultimately we _do_ want our programs to run fast. Slow programs cost real money, prevent real discoveries, stop new time sensitive applications from being feasible.
Interactive features must be fast. Calculations must be faster than the lifetime or patience of the researchers.



C, protobuf, and SQL all have a fixation on the notion of record.

They are missing sum types, which is super annoying.
```
type = {

}

```

## Program Points

## Assertions
Specifying control flow edges in the absence of context won't work. Sometmes they will only be restricted.




# Analyses

- Liveness
- def-use
- Avalable expression
- Global Value Numbering

Many of these are tagging sets to program points. 
Analysis may be may/must. 
Generic notions must tend to be overapproximate.

Analyses often fit in a fixed point framework.

# Optimizations
Optimizatins screw everything up.
How can we track them 
We need a language in which to state what happened with precise semantics. We will not prescribe how you decided to do it, or if it is even right in some sense, but merely describing what you did is a good start.






instruction selection
reg-alloc



# Patching, Linking, and Virus Writing
Relocations are a DSL, a sum type of actions that the loader is an intepreter over.


## JIT

## ELF

### Why does being packing alongside the binary matter?
It does.

- Compilers can generate this info in the first place. Disassembly and decompilation may require less guess work. Each bit should have verification criteria.

## Aspect Oriented Programming and Hooking and MetaObject protocols


# Notions of Decompilation
## Many-to-many
We have this notion that the high level program is blob A and the low level program is blob B. There is a notion of correspondence of states in A to states in B. There is also correspondences of the important observable events.

https://xavierleroy.org/courses/EUTypes-2019/slides.pdf

Bisimulation is the name of the game. Empirically however, there are more correspondences than strictly defined by the language spec. Beyond that, there are correspondences that aren't even temporally equilavent. Certain statements are reordered.

Again, empirically, these correspondences exist. People see them and use them. They patch critical systems using these correspondences even if the formal spec says nothing about it. If computer science is a science, we must admit that the theory is not fitting with the experiment in this situation.

Hence, until I'm convinced otherwise that either some extended notion of bisimulation 




[discussion about decompiler IRs](https://twitter.com/SandMouth/status/1619414427979386880?s=20&t=7B7JuRiqv83Ksf3h_ZjSeA)
