---
layout: post
title: Metamath
---

Parsing is a proof obligation which is kind of cool / insane.
since fol is _embedded_, the distinction between sets and predicates is interestingly flimsy? Tarski S2
Disjointness and nominal logic?
A directed prolog of sorts. Proof checking as computation. You write which rules to resolve on, it adds the requirements to the goal stack

```prolog
d(X,Y) :- dif(X,Y).
a(axname, [path, X, Y]) :- d(), f(), f(), e(), e().
```

The RPN nature means we describe proof trees in a depth first manner. This is similar to bussproofs.

```
l1 $e stuff1
l2 $e stuff2
myax $a$ mydude
```

is like asserting an inference rule

```
l1 stuff      l2 stuff
----------------------- myax
      mydude
```

hoare in metamath

path proofs in metamath

```
$c vert path edge a b c d e f $.
$v x y z $.
$f vert x $.
$f vert y $.
$f vert z $.

min $e edge x y $.
base-path $a path x y $.

maj $e path y z $.
trans-path $a path x z $.

verta $a vert a $.
vertb $a vert b $.
vertc $a vert c $.
$a vert d $.
$a vert e $.

edgeab $a edge a b $.
edgebc $a edge b c $.

pathac $p path a c $.

```

```


https://drops.dagstuhl.de/opus/volltexte/2023/18384/pdf/LIPIcs-ITP-2023-9.pdf automated theorem proving for metamath

metamath 0

https://github.com/digama0/mm0

metamath-lamp https://github.com/digama0/mm0

metamath book

metamath pcc
drat
datalog
prolog
congruence closure
