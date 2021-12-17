---
date: 2021-12-17
layout: post
title: "Instruction Matching with Souffle Datalog"
tags: datalog compiler
description: I use Souffle datalog to find patterns in a toy compiler IR. This also shows how to do graph pattern matching using datalog/sql 
---

I've been thinking about instruction selection and datalog a lot lately.

Instruction selection is the step of taking a compiler intermediate representation and figuring out which concrete assembly instructions you want to use to implement it. This slightly more concrete instruction IR (MIR) typically still needs to be register allocated and scheduled before it is fully formed assembly.

Sometimes there is a nice one to one correspondence, like there may be an add instruction in your IR that corresponds to an add assembly instruction.

Sometimes is may take multiple assembly instruction to implement a simple IR construct, or a simple assembly construct may implement a complicated IR expression. Simple examples of the latter included fused multiply add instructions, or memory load instructions that allow constant offsets of the address (an internal add operation like `ld result [addr + 4]`).

In some sense the way this is all typically done is by searching for special patterns in the IR. These patterns may be somewhat implicit in the code of the instruction selector, or a mixed code and DSL like in LLVM's tablegen.

There is an [interesting paper on using constraint satisfaction solvers](https://dl.acm.org/doi/10.1145/3126528) to perform the instruction selection problem that I've been trying to implement. At a high level it:

1. Find all matches of patterns
2. Grind on matches and ship them off to constraint model and solver to pick the best match cover
3. Chew on result of solver and build next stage IR out of templates for each selected match

I thought that 1. was kind of a cute example in which to use datalog (although I did not take this approach in the actual project which is to be open sourced soon).

If you have your IR in SSA form, it is easy enough to express as a table. Each statement becomes an entry in the tables corresponding to the different kinds of statements. 

What about the ordering of statements in a block? Actually, The ordering of the IR assignments within a basic block is a bit of a red herring IMO. It is an unfortunate side effect of needing to serialize the thing, or of using vector/list data structures. The dataflow within a block is really more graph-like than it is sequence-like. You do need to explicitly thread effects as values though if you do this. This is what is done in the paper.

Filling the initial database looks a bit like writing LLVM IR. The `.` of datalog is a bit like a statement ending `;`. You have to specify what block every statement is in with an explicit column in the statement table rather than declaring it at the top of the block like in LLVM IR.

Patterns can be specified as datalog clauses which fill out tables of every possible match. This is not a recursive query, so you could implement this in bog standard sql too if you'd like. You can dump all the matches as the entries of these tables and then ship them off to the constraint solver.

This is all a bit verbose. It would probably be better to generate this datalog from a more concise dsl of some kind.

```
.type var <: symbol
.type op <: symbol
.type blk <: symbol

.decl binop(blk : blk, out : var, op : op, a : var, b : var)
.decl unop(blk : blk, out : var, op : op, a : var)
.decl load(blk : blk, out : var, addr : var)
.decl br(blk: blk, cond : var, true_blk : blk, false_blk : blk)
// .decl phi() We'll think about this part later
//b1:
    binop("b1", "z", "add", "x", "y" ).
    unop("b1", "a", "neg", "z" ).
    br("b1", "z", "b2", "b3").
//b2:
    load("b2" , "q", "z").
    br("b2", "true" ,"exit", "exit").
//b3:
    binop("b3", "addr", "add", "z", "4").
    load("b3" , "q", "addr").
    br("b3", "true" ,"exit", "exit").


.decl add_match(blk : blk, out : var, a : var, b : var)
.output add_match
add_match(blk,out,a,b) :- binop(blk,out, "add", a, b).

.decl neg_match(blk : blk, out : var, a : var)
.output neg_match
neg_match(blk,out,a) :- unop(blk,out, "neg",a).

.decl load_add_match(blk : blk, out : var, addr_off : var, addr : var, offset : var)
.output load_add_match
load_add_match(blk, z, addr_off, addr, offset) :- 
    binop(blk, addr_off, "add", addr, offset),
    load(blk, z, addr_off).
```
Running this with `souffle match.dl -D -` results in

```

---------------
add_match
blk     out     a       b
===============
b1      z       x       y
b3      addr    z       4
===============
---------------
neg_match
blk     out     a
===============
b1      a       z
===============
---------------
load_add_match
blk     out     addr_off        addr    offset
===============
b3      q       addr    z       4
===============
```

Note that not everything was covered and the the add node in b3 was covered twice. The subsequent stages of the selector need to deal with this.

Finding matches within this IR is in fact graph pattern matching as one can have multiblock patterns that have cycles in them. Rearranging the body of the pattern clauses may have better or worse search characteristics.

It is interesting that this exposes there are more dimensions to consider graphs other than directed/undirected. These are "ported" graphs where the edges coming off each vertex are not interchangable in some sense. We are more familiar with this "portedness" in the context of trees and dags where standard ASTs like `pow(x,n)` obviously do not have `x` and `n` interchangeable.

I've been scared off graph matching before because it has a conjectured high complexity, but it really isn't so bad. Especially if you are looking for small patterns in a big graph like here. Then even fairly naive approaches are polynomial in the matchee graph size (the power being dependent on the size of the pattern). That is what datalog is doing here. 

Here are some references on some other graph matching algorithms

[VF2](http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.101.5342&rep=rep1&type=pdf_
[ullmann bitvector algorithms for binary constraint satisfcation](http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.681.8766&rep=rep1&type=pdf)

<https://stackoverflow.com/questions/17480142/is-there-any-simple-example-to-explain-ullmann-algorithm?rq=1>

<https://stackoverflow.com/questions/6743894/any-working-example-of-vf2-algorithm/6744603#6744603>


