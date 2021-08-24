
Declarative Solving for Compiler Backends using Minizinc
Unison-style Compiler backends

Declarative compilation

https://arxiv.org/pdf/1804.02452.pdf

Schulte course on caonstraint programming
https://kth.instructure.com/courses/7669/files/folder/lectures?
on compilers
https://kth.instructure.com/courses/6414/files

# Instruction Selection

Subgraph isomorphism problem
VF2 algorithm

type aexpr = Mul | Add

Macro expansion
 - procede bottom up
Maximal Munch

Instruction selection is taking a program and firuing out which instructions can be used to implement this. Typically this leaves behind still some problems to solve, in particular register allocation and instruction scheduling. Presumably, everything in the program needs to be done. We have some notion of correspondence between the program representation and the available instructions. The exact nature of this correspondence depends on how we represent our program.

- Tree - One representation of a program might be as a syntax tree, say `(x + (y * z))`.
- DAG - consider `(x + y) * (x + y)`. Really we want to note common shared computation and not recompute `x+ y` twice. DAGs and the technique of hash consing can be useful here.
- CFG - A different representation might be to separate out blocks and control edges between them. Blocks consist of a sequence of statements.

If the statements are purely for assignment, assignment can be inlined. The block is nearly purely functional in some sense. It can be compressed into a functional form like the DAG or Tree by inlining. The block could also itself be considered as a graph, as there is often more then one equivalent way of sequencing the instructions.

The simplest case to consider is that of the tree. We can enumerate patterns in the tree that we know how to implement using instructions. The relationship between tree patterns and instructions can be many-to-many. We should understand how to implement every node in the tree `(?a + ?b)`, `(?a * ?b)` with a pattern consisting of a sequence of instructions for completeness (ability to compile any tree). We also should try to figure out the tree patterns that correspond to a single assembly instruction like `load reg [reg+n]` because these will often be efficient and desirable.

There are two distinct and often separable problems here:
1. Find pattern matches
2. Pick which matches to actually use.


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



# Graph Coloring and Register Allocation
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






Liveness via datalog.





# Instruction Scheduling





Dataflow analysis with Datalog.
I should lay out what I understand of the unison compiler.


Register Packing
Instruction Scheduling1

The box model


Christian Schulte course




