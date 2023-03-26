---
layout: post
title: Constraint Programming
---

- [What is it for?](#what-is-it-for)
- [Minizinc](#minizinc)
    - [Embedding datalog into minizinc](#embedding-datalog-into-minizinc)
- [Picat](#picat)
- [Answer Set Programming](#answer-set-programming)
- [Topics](#topics)
  - [Branch and Bound](#branch-and-bound)
  - [Local Search](#local-search)
  - [Lattices](#lattices)
  - [Propagators](#propagators)
  - [Heuristics](#heuristics)
- [Misc](#misc)

# What is it for?
Puzzle solving
- n-queens
- sudoku

Compiler problems

Routing Problems
Allocation problems

Plannning
Reachability
Verification
# Minizinc
[webassembly playground](https://github.com/MiniZinc/minizinc-playground)
[tutorial](https://www.minizinc.org/doc-2.6.2/en/part_2_tutorial.html)
[202 autumn school](https://www.youtube.com/watch?v=lQi3b-sxt1s&ab_channel=AutumnSchoolonLogicandConstraintProgramming)

[Exploring a shipping puzzle, part 3](https://kevinlynagh.com/notes/shipping-puzzle/part-3/)

```minizinc
var int : x;
solve satisfy;
```

How to make DSLs. Look for macros. Look for function call. Look for gensyms


Minizinc has records now. That's huge. Hmm. But it doesn't have unions...
What about recurisive records? Probably not
```minizinc
type Foo = tuple(int,int);

var Foo: biz;

var Foo: null = (0,0);
enum tag = Foo | 
  record(tag: "Foo", foo:null)
```
```minizinc
type Cell = tuple(int, int);
type Heap = array[Cell];

```


```minizinc

mov("a","b");


```


var vs par is compile vs runtime distinction in type system
it would be cool if minizinc could support adts or records.

### Embedding datalog into minizinc

```minizinc
set of int : verts = 1..3;
array[verts,verts] of bool : edge;
%array[int,int] of verts : edge0;
array[verts,verts] of var bool : path;

%edge0 = [|1,2 | 2,3];
% check if in edges list
function bool: edge0(int : i, int : j) = 
    i = 1 /\ j = 2 \/
    i = 2 /\ j = 3;
edge = array2d(verts,verts, [ edge0(i,j) | i,j in verts]);

constraint forall(i,k in verts)(
    path[i,k] <-     % <-> ? 
    edge[i,k] \/ exists(j in verts)(edge[i,j] /\ path[j,k])
);

%output ["\(edge)"];

solve satisfy;
```

Note that `-a` or `--all-solutions` will show all solutions. 

Non negated datalog should have a unique solution. Datalog with negation is a different ballgame.

# Picat
[website](http://www.picat-lang.org/)

index mode annotations
table annotions include lattice type stuff "mode-directed tabling"

action rules
loops
# Answer Set Programming
See notes on answer set programming
# Topics
## Branch and Bound

## Local Search
## Lattices

## Propagators

## Heuristics

# Misc
- google or-tools
- eclipse https://www.eclipseclp.org/


[Hakan's site](http://www.hakank.org/) an insane number fo examples in systems

Coursera Course

[ORTools](https://developers.google.com/optimization) is apprently killer according to [Minizinc Challenge](https://www.minizinc.org/challenge.html)

GeCode

[CPMpy](https://www.youtube.com/watch?v=A4mmmDAdusQ&ab_channel=Int%27lConferenceonPrinciplesandPracticeofCP)

[constraint programming for robotics](http://www.codac.io/)
 Also see interval constraint programming [interval mooc](https://www.ensta-bretagne.fr/jaulin/iamooc.html)  http://www.codac.io/tutorial/index.html 

[csplib](https://www.csplib.org//) a library of constrains

[art of propagators](https://dspace.mit.edu/handle/1721.1/54635) 
[geocode manual on propagators](https://www.gecode.org/doc-latest/MPG.pdf) (appendix P) 
Propagators have been described as "just" monotonic functions between lattices. <https://www.youtube.com/watch?v=s2dknG7KryQ&ab_channel=ConfEngine>


[constraint acquisition](https://twitter.com/grmenguy/status/1531879717376184320?s=20&t=-IHVNfpCMKlhva0T8ctWXA) inferring predoncitions for code?

[Using and Understanding ortools' CP-SAT: A Primer and Cheat Sheet](https://github.com/d-krupke/cpsat-primer)