---
layout: post
title: Functional Logic Programming
---

https://en.wikipedia.org/wiki/Functional_logic_programming

Curry
Mercury

RICE: An Optimizing Curry Compiler https://www.youtube.com/watch?v=K6gLX0la9zo&t=1179s&ab_channel=ACMSIGPLAN

Narrowing

graph combinators

bubbling vs backtrackng vs pulltabbing
[Making Bubbling Practical](https://arxiv.org/abs/1808.07990)
[on the correctness of pulltabbing](https://arxiv.org/pdf/1108.0190.pdf)


[verse](https://simon.peytonjones.org/assets/pdfs/verse-conf.pdf) that nutso spj epic games project


`sudo apt install pakcs` nice

Translation of prolog programs:
Turn each predicate int bool value function
`a :- b`  becomes  `a | b = True`
 
[curry tutorial](https://www.informatik.uni-kiel.de/~curry/tutorial/tutorial.pdf)


https://github.com/matthesjh/rewriting-curry libraries for term rewriting in curry

```bash
echo "
-- ;re
1 + 1
2 <= 3
2 == 3
let square x = x * x
square 7
x =:= 7 where x free
a ++ b  =:= [1,2] where a,b free
:q
" | pakcs
```

`path a z = edge a b && path b z where b free`

`=:=` constrained equality


https://ciao-lang.org/ciao/build/doc/ciao.html/fsyntax_doc.html ciao functional notaion
https://www.swi-prolog.org/pack/list?p=func func is kind of wimpy
```prolog
:- initialization(main,main).

fun(F,Res) :- functor(F,N), length(Ress,N), map2(call , Args, Ress), call(FSym, Ress).

_foo(X,Y,Z) :- call(X,A), call(Y,B), foo(A,B,Z).

_append(X,Y,Z) :- call(X,A), call(Y,B), append(A,B,Z).

nil(A) :- A = [].
cons(A,B,C) :- call(A,X), call(B,Xs), C = [X | Xs]. 
feq(X,Y) :- call(X,A), call(Y,A).

main(_) :- feq(X,  _append(nil,nil)).
```

:- initialization(main,main).
main(_) :-