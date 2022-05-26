---

title: Compiling with Constraints I
---

Hey Hey! We've open sourced our project [VIBES](https://github.com/draperlaboratory/VIBES) (Verified, Incremental Binary Editing with Synthesis).

A compiler can be a complicated thing. Often we break up and approach the problem by breaking it into pieces. The front end takes text and converts it to a tree. In turn it is often converted to some kind of intermediate representation, say a control flow graph. The middle end performs rearrangements and analyses on this graph. The back end is in charge of taking this intermediate representation and bringing it to executable machine code.

The backend of a compiler has a number of different problems

1. Instruction Selection - Take `x := a + b` and turn it into `mov x, a; add x,b` 
2. Register Allocation - Take `add x,a` and turn it into `add R0, R1`
3. Instruction Scheduling - Rearrange instructions to maximize throughput of CPU. Internally cpu has pipelines and resources, store and loads to memory are slow, you want to make sure these are chugging along and interleaved well.

Typically, these will be run one after the other in some order, with greedy-ish algorithms and hand tuned code. This works pretty well and is fast to compile.
It does leave performance and size of the resulting code on the table.
The Unison approach is trying to build a non toy compiler that uses declarative constraint programming to solve these in concert.
Now any optimization is only as good as our modelling of the situation. This is one of the common fallacies of godhood people get when they think about applying math to problems. If your model of the cpu is coarse, then perfectly optimizing with respect to this . Ultimately, every ahead of time model is bad because it must be unable to know information that is readily accessible at runtime. This is at least one reason why without experimentation and measurement, you really can't tell whether crass online optimization can deliver superior results to thorough ahead of time optimization. See for example JITs, branch prediction, VLIW architectures, out of order execution. 




Can I write CFG programs directly in minizinc in a good way?
Would avoid 1 indirection or going in and out of a language

Declarative Solving for Compiler Backends using Minizinc
Unison-style Compiler backends

Declarative compilation

[Combinatorial Register Allocation and Instruction Scheduling](https://arxiv.org/pdf/1804.02452.pdf)

Schulte course on constraint programming
https://kth.instructure.com/courses/7669/files/folder/lectures?
on compilers
https://kth.instructure.com/courses/6414/files



# Graph Coloring and Register Allocation






In any case we are embedding a liveness analysis into minizinc.
live(t,i) = true/false
next(i1,i2) = true/false
next forms total order.


[after(i,k)  <- next(i,j), after(j,k) for i,j,k in insns]
[after(i,k) <-> exists(j in insn)( next(i,j) /\  after(j,k)) \/ next(i,k) forall i,k ]
[live[insn, temp] <- ]





# Instruction Scheduling

The pure instruction scheduling problem might occur even at the IR level. We can imagine an imperative IR. Certain operations commute and others don't. We may want to minimize the liveness time of variables for example. This would make sense as a pre-processing step to a sequence input language to an instruction selector.


Instruction scheduling can be parametrized as:
1. an embedding into actual time (cycle issue time probably). This is important if you are optimizing for runtime and can get estimates of how long each instruction takes.
2. a ranking as integers
3. next(i,j) relation which is basically integers. Allows for partial order. after(i,j) :- next(i,k), after(). after is path connected in temporal dag. Possibly this is mappable into a lattice notion of time (i,j,k,etc)?



Instruction matching as an SMT problem


Why is there such an impulse to model these problems in a purely functional style? Invariably we need to introduce a state threading.


Dataflow analysis with Datalog.
I should lay out what I understand of the unison compiler.


Register Packing
Instruction Scheduling1

The box model


Christian Schulte course



simple
```minizinc
include "alldifferent.mzn";
include "all_equal.mzn";
include "diffn.mzn";

set of int : reg_t = 1..4;
set of int : temp_t = 1..10;
set of int : instr_t = 1..10;
array[temp_t] of var reg_t : reg;
array[temp_t] of var instr_t : def;
array[temp_t] of var instr_t : death;
/*
There is a possible off by one error
is death at the last use site, or is it the instruction after
Let's say it is the last use site.
Or rather should we be thinking of program points between instructions


*/



%constraint alldifferent(def);

predicate insn(array[int] of var temp_t : defs, string: operator,  array[int] of var temp_t : uses) =
    all_equal([def[t] | t in defs ] )
    /* 
         forall(t2 in defs)(
             def[t1] = def[t2]
        ) */
        /\
        forall( t1 in defs)(
        forall (t2 in uses) (
            def[t1] > def[t2] /\ death[t2] >= def[t1]
        )
    );

% redundant?
constraint forall(t in temp_t)(
    def[t] <= death[t]
);

%output ["foo" | t in temp_t];
constraint diffn( reg, def , [1 | t in temp_t], [ death[t] - def[t] | t in temp_t ] );
%constraint diffn( reg, def ,  reg, [ death[t] - def[t] | t in temp_t ] );
/* 
We can't do it this way because alldifferent takes a compile time array.
We could do this if we had a set of dummy values,
Or if we ahead of time fixed the instruction ordering.
If wwe did that, liveness analysis might need to be done out of minizinc.

constraint forall( i in instr_t)(
    alldifferent(  [ reg[t]   | t in temp_t where i < death[t] /\  def[t] < i ]    )
); */

constraint insn( [3], "add", [1,2] );
constraint insn( [4], "sub", [1,3] );

solve minimize card(array2set(reg));
```


ordered
```minizinc
include "alldifferent.mzn";
/*

This file shows register allocation if we prefix the instruction order.

*/
set of int : reg_t = 1..4;
set of int : temp_t = 1..4;
%set of int : instr_t = 1..10;
array[temp_t] of var reg_t : reg;
%array[temp_t] of var instr_t : def;
%array[temp_t] of var instr_t : death;
enum inout = {Out, In};
set of int : instr_t = 1..4;
array[instr_t,inout] of set of temp_t : instrs =
   [|
    {1,2}, {}  |
    {3}, {1,2} |
    {4}, {2,3} |
    {},  {1,4}
   |];

array[temp_t] of int : def =
   [ min([ i  | i in instr_t where t in instrs[i,Out] ])  | t in temp_t ] ;

array[temp_t] of int : death =
   [ max([ i  | i in instr_t where t in instrs[i,In] \/ t in instrs[i,Out]  ])  | t in temp_t ];

constraint forall( i in instr_t)(
    alldifferent(  [ reg[t]   | t in temp_t where i <= death[t] /\  def[t] < i ]    )
);
```

Something like a finally tagless style encoding of block?
But I'd also like the same of insn
Side effectful functions?
Ok. So I want

```minizinc

predicate block(string : name, set[temp_t] : ins, set of [temp_t] : outs, array[int] of insn : data, array[int of insns : data] : ctrl)

```