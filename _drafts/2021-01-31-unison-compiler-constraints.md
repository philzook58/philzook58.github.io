---

title: Compiling with Constraints I
---

Hey Hey! We've open sourced our project [VIBES](https://github.com/draperlaboratory/VIBES) (Verified, Incremental Binary Editing with Synthesis).





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








# Instruction Scheduling

The pure instruction scheduling problem might occur even at the IR level. We can imagine an imperative IR. Certain operations commute and others don't. We may want to minimize the liveness time of variables for example. This would make sense as a pre-processing step to a sequence input language to an instruction selector.


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
Or rasther should we be thinking of program points between instructions


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