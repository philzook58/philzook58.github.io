---
layout: post
title: Constraint Programming
---

# What is it for?
Puzzle solving
- n-queens
- sudoku

Compiler problems

Routing Problems
Allation problems

# Minizinc
[tutorial](https://www.minizinc.org/doc-2.6.2/en/part_2_tutorial.html)
[202 autumn school](https://www.youtube.com/watch?v=lQi3b-sxt1s&ab_channel=AutumnSchoolonLogicandConstraintProgramming)

```minizinc
var int : x;
solve satisfy;
```

How to make DSLs. Look for macros. Look for function call. Look for gensyms


```minizinc

mov("a","b");


```


var vs par is compile vs runtime distinction in type system
it would be cool if minizinc could support adts or records.

# Answer Set Programming
<https://en.wikipedia.org/wiki/Answer_set_programming>

[Potassco, the Potsdam Answer Set Solving Collection](https://potassco.org/)

Clingo
dlv2 maybe https://dlv.demacs.unical.it/
[wasp](https://github.com/alviano/wasp)
[embasp](https://embasp.readthedocs.io/en/latest/index.html) https://github.com/DeMaCS-UNICAL/EmbASP
dlvhex http://www.kr.tuwien.ac.at/research/systems/dlvhex/

[seventh answer set competition](https://arxiv.org/pdf/1904.09134.pdf)

Disjunctive logic programming

Grounding - Figure out the term universe?
semi naive grounding.
So answer set programming runs datalog, and then ?

Hmm. This is datalog + csp. This is what i wanted to build a compiler end to end.


stable models - smallest of models?
[13 definitions of a stable model](https://www.cs.utexas.edu/users/vl/papers/13defs.pdf)
well founded
stable = well-founded + branch

[what is answer set programming](https://www.cs.utexas.edu/users/vl/papers/wiasp.pdf)
[answer set programming in a nutshell](https://www.youtube.com/watch?v=m_YuE2E_bck&ab_channel=SimonsInstitute)
loop formulas
`p :- q(X) : r(X)` conditional literals
stronger than sat?
`:- q(X), p(X).` integrity constraints.
`p(x); q(X):- r(X)` disjunction
smt infrastructure, but theory is asp specific?
modeling + grounding + solving

metaprogramming - intriguing

[applications of answer set programming](https://www.youtube.com/watch?v=i5dARGZmuIU&ab_channel=AutumnSchoolonLogicandConstraintProgramming)

huh clingo supports lua programs. That's intriuging. I was considerig doing that to souffle

Alviano, M., Faber, W., Greco, G., & Leone, N. (2012). Magic sets for disjunctive Datalog programs


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
