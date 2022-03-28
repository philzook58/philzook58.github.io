---
layout: post
title: Constraint Programming
---


# Minizinc
[tutorial](https://www.minizinc.org/doc-2.6.2/en/part_2_tutorial.html)

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

# Topics
## Branch and Bound

## Local Search
## Lattices

## Propagators

## Heuristics

# Misc

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
