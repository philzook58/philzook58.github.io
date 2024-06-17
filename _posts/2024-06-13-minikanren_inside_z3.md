---
title: "Justified SMT 1: The Minikanren inside Z3"
date: 2024-06-13
---

Z3 actually has a logic programming language inside it if you know how to look. This makes it one the easiest to pull off the shelf because Z3 has so much work put into it and excellent bindings. It also is perhaps one of the most declarative logic programming languages available with very cool strong theory support.

Here I talked about how to use Z3 to make a [minikanren](http://minikanren.org/), keeping the search in the python metalayer. <https://www.philipzucker.com/minikanren-z3py/> This is still a useful and interesting idea. I mention that the metalevel `conj` and `disj` can be replaced by z3's `And` and `Or` but at the cost of a quantifier. This is still true.

I find myself revisiting these old ideas with hopefully more sophisticated perspective.

There is an old topic that I've encountered most strongly in the answer set programming community of what exactly is the logical semantics of prolog? Prolog is quasi operational.

If we take this prolog program that searches for pathes in a graph.

```prolog
path(X,Y) :- edge(X,Y).
path(X,Z) :- edge(X,Y), path(Y,Z).
```

We might think the declarative semantics of this program are

```python
from z3 import *
BV = BitVecSort(2)
edge = Function('edge', BV,BV, BoolSort())
path = Function("path", BV,BV, BoolSort())
x,y,z = Consts('x y z', BV)
base = ForAll([x,y], Implies(edge(x,y), path(x,y)))
trans = ForAll([x,y,z], Implies(And(edge(x,y), path(y,z)), path(x,z)))
display(base)
display(trans)

```

&forall;x, y : edge(x, y) &rArr; path(x, y)

&forall;x, y, z : edge(x, y) &and; path(y, z) &rArr; path(x, z)

In a loose intuitive sense this is true and is what the prolog syntax is alluding to.

In a stricter sense that z3 implements something akin to multi sorted first order logic, this is false.

The thing Z3 (or any smt solver) tries to do is return models that satisfy the constraints. It does not really have an operational semantics.

What the axioms actually say is that `path` is transitive with respect to `edge`. This is _not_ the same as saying `path` is the transitive closure of `edge`. Transitive closure is inexpressible in a certain generic sense inside first order logic <https://math.stackexchange.com/questions/1286141/transitive-closure-and-first-order-logic> . As with many no-go theorems, I'm not sure there isn't perhaps a way around achieving the spirit of the objective that avoids the preconditions of the theorem.

The transitive closure is the _least_ transitive relation. Z3 is still free to overapproximate `path`. A simple useful test case is to consider whether `path=True` still works even when it's not

```python
solve(And(base,trans, edge(0,1), edge(1,2)))
```

    [path = [else -> True],
     edge = [else ->
             And(Not(And(Var(0) == 1,
                         Not(Var(1) == 2),
                         Not(Var(1) == 1))),
                 Not(And(Var(0) == 2,
                         Not(Var(0) == 1),
                         Var(1) == 1)))]]

One attempt to patch this up is to note that really we want `path` to be true not only _if_ one of the preconditions of a rule holds, but _if and only if_. This is the idea behind clark completion <https://www.inf.ed.ac.uk/teaching/courses/lp/2012/slides/lpTheory8.pdf> .

You do the clark completion by gathering up every rule of a given head. You can turn it into a rule with a body that is a giant `or` of `ands`. To make all the heads unifiable, make them unique variables and add the approriate equality constraints into each of the individual bodies.

Minikanren is intrinsically written in clark completion form by the nature of it's abuse of the function call mechanisms of it's host language. Every rule that produces it's head is gathered up in the body of that relations definition.

```python
# a sketch. I don't have a working minikanren on my pc right now or loaded up in my head.
def path(x,z):
    yield from disj( 
          edge(x,z),
          fresh(lambda y: conj(edge(x,y), path(y,z)))
    )

```

Ok well then how about

```python
clark = ForAll([x,z], path(x,z) == Or(
    edge(x,z),
    Exists([y], And(edge(x,y), path(y,z)))
))
s = Solver()
s.add(clark)
s.add(ForAll([x,y], edge(x,y) == Or(
    And(x == 0, y == 1),
    And(x == 1, y == 2)))
)

s.check()
m = s.model()
m
print("edge", {(x,y)  for x in range(4) for y in range(4) if  m.eval(edge(x,y)) })
print("path", {(x,y)  for x in range(4) for y in range(4) if  m.eval(path(x,y)) })

```

    edge {(0, 1), (1, 2)}
    path {(0, 1), (0, 2), (1, 2)}

This is still not correct. The Clark completion is not sufficient basically because it still allows circular reasoning in the form of loops.
Consider the below reformulation of the same basic idea, except that I write the transitive part of path differently.
`path` can sort of dignify itself.

I'm not exactly sure the conditions under which clark completion alone is sufficient, but they seem subtle and can't possibly always work. The `edge-path` form of transitivity I think is correct because of a stratification and grounding of path with respect ot edge.

```python
clark = ForAll([x,z], path(x,z) == Or(
    edge(x,z),
    Exists([y], And(path(x,y), path(y,z)))
))
s = Solver()
s.add(clark)
s.add(ForAll([x,y], edge(x,y) == Or(
    And(x == 0, y == 1),
    And(x == 1, y == 2)))
)

s.add(path(1,0))
s.check()
m = s.model()
m
print("edge", {(x,y)  for x in range(4) for y in range(4) if  m.eval(edge(x,y)) })
print("path", {(x,y)  for x in range(4) for y in range(4) if  m.eval(path(x,y)) })
```

    edge {(0, 1), (1, 2)}
    path {(0, 1), (1, 2), (0, 0), (1, 1), (0, 2), (1, 0)}

But there is a fix.

Earlier I said z3 is merely multi-sorted first order logic. This is a good first pass understanding, but it isn't true.
Ok, it does directly have support for transitive closure as a special relation <https://microsoft.github.io/z3guide/docs/theories/Special%20Relations/> , but actually even the uncontroversial addition of algebraic data types like Option/List/Nat has some kind of least fixed point character that let's you constrain the relations.

It's actually quite fascinating. What you do is add an extra parameter to your relation that contains a proof tree ADT.

1. Add an extra proof parameter to the definition of the relation itself
1. Make a datatype with a constructor for each case in your minkanren program
2. (optional?) Put any existentials into the proof sturcture

This is the same thing as adding a tracing parameter to a datalog (provenance <https://souffle-lang.github.io/provenance> ), prolog, or minikanren program. The tracing parameter can record the call tree that succeeds without using any extralogical funkiness. This is an instance of a general principle that the trace of any system you think is proving something is a proof object.

I stuck to bitvectors because then I knew the quantifiers wouldn't go off the rails. But if you use the `define-fun-rec` facilities of z3, you don't know generic quantifiers and you can get z3 to return proof trees and results even in infinitary cases. `define-fun-rec` implements a different mechanism than general quantifiers, something like iterative deepening. A recursive function definition is logically equivalent to using a quantified equality, but it is implemented differently. If you're seeking unsat, maybe either works, but if you're seeking models that contain that analog of minikanren answers, define fun rec seems superior.

```python
pathpf = Datatype("pathpf")
pathpf.declare("base")
pathpf.declare("trans", ("y", BV), ("p1", pathpf), ("p2", pathpf))
pathpf = pathpf.create()
p = Const("p", pathpf)

path = RecFunction("path", BV, BV, pathpf, BoolSort())

RecAddDefinition(path, [x,z,p], Or(
    And(pathpf.is_base(p), edge(x,z)),
    And(pathpf.is_trans(p), path(x, pathpf.y(p), pathpf.p1(p)), path(pathpf.y(p), z, pathpf.p2(p))))
)
edge = RecFunction("edge", BV, BV,  BoolSort())

RecAddDefinition(edge, (x,y),Or(
    And(x == 0, y == 1),
    And(x == 1, y == 2),
    And(x == 2, y == 3)))

s = Solver()
#s.add(ForAll([x,y], edge(x,y) == Or(
#    And(x == 0, y == 1),
#    And(x == 1, y == 2)))
#)

#s.add(path(0,3,pathpf.trans(1,pathpf.base,p))) 
s.add(path(0,2,p)) 
#pathpf.trans(1, pathpf.base, pathpf.base)))
s.check()
m = s.model()
#print(m[p])
m[p]
#print("edge", {(x,y)  for x in range(4) for y in range(4) if  m.eval(edge(x,y)) })
#print("path", {(x,y)  for x in range(4) for y in range(4) if  m.eval(path(x,y,p)) })
```

trans(1, base, base)

# Bits and Bobbles

The performance of finding these models is a bit unstable.

Asnwer set programming has been described as justified smt <https://www.weaselhat.com/post-1067.html>

I've used this trick to embed static datalog like analyses into constraint solver. An over approximation of liveness is ok, so just clark completion is acceptable. Usually other objectives will tend to push the liveness down to what is strictly needed anyhow. <https://www.philipzucker.com/compile_constraints/>

Z3's transtivie special relation or using its optimiation functionality to get the "least" path are other options.

I think I can use this to encode inductive relations for knuckeldragger. More on this next time. Indcution principles, recursors.

`path = Function("path", BV, BV, pathpf)` is also interesting and maybe good? Uniqueness of proofs

It doesn't have a notion of negation as failure. It'll just hang.

I jibbered about this on twitter more than I realized. Well, it's good to have it actually written up in some form

<https://x.com/SandMouth/status/1570411399997710343>

<https://x.com/SandMouth/status/1564299958135799811>

<https://x.com/SandMouth/status/1570236396677525504>

<https://x.com/SandMouth/status/1564347784194654220>

<https://x.com/SandMouth/status/1552665454497480706>

A trickier question that bore these ideas is how to do justified equality in z3. i wanted to mimic egglog / egg since the z3 model is kind of the egraph. Equality is very slippery. It'll ruin your justifications out from under your feet.

example of proof parameter tracking using DCGs
<https://x.com/SandMouth/status/1558473206239006720>

```prolog

%sequent( Hyp, Conc, Var )

:- use_module(library(clpfd)).
%:- table prove/2.
:- use_module(library(solution_sequences)).
%:- op(600, xfy, i- ).

prove(S, ax(S, id)) :- S = (A > A).
prove(S, ax(S, fst)) :- S = (A /\ _B > A).
prove( A /\ B > B, ax(A /\ B > B, snd)).
prove( S, ax(S, inj1 )) :- S = (A > A \/ _B).
prove( S, ax(S, inj2 )) :- S = (B > _A \/ B).
prove( false > _ , initial ).
prove( _ > true  , terminal ).
prove( A > B /\ C, bin(A > B /\ C, pair, P1, P2)) :- prove(A > B, P1), prove(A > C, P2).
prove( A \/ B > C , bin(A \/ B > C, case, P1, P2)) :- prove( A > B, P1), prove( A > C, P2).
prove( A > C, bin(A > C, comp, P1, P2)) :- prove(A > B, P1), prove(B > C, P2).


height(ax(_,_), 1).
height(un(_,_,PX), N) :- N #> 1, N #= NX+1, height(PX,NX).
height(bin(_,_,PX,PY), N) :- N #> 1, N #= max(NX , NY) + 1, height(PX,NX), height(PY,NY).

% maybe explicilty taking proof steps off of a list. using length.
% use dcg for proof recording?


prove(A > A)       --> [id].
prove(A /\ _ > A)  --> [fst].
prove(_ /\ B > B)  --> [snd].
prove(A > A \/ _)  --> [inj1].
prove(B > _ \/ B)  --> [inj2].
prove(false > _)   --> [initial].
prove( _ > true)   --> [terminal].
prove(A > B /\ C)  --> [pair], prove(A > B),  prove(A > C).
prove(A \/ B > C)  --> [case], prove(A > C),  prove(B > C).
prove(A > C)       --> [comp], prove(A > B),  prove(B > C).

:- initialization(main).
%main :- format("hello world", []).
%main :- between(1, 10, N), height(Pf, N), writeln(Pf), prove( w /\ x /\ y /\ z > w, Pf ), print(Pf), halt.
main :- length(Pf, _), phrase(prove(w /\ x /\ y /\ z > w \/ y),Pf), print(Pf), halt.
main :- halt.
```

Yes, the dcg form is very pretty. It's a writer monad of sorts. It is recording a minimal proof certificate that is reconstructable to the full thing pretty easily.

`G --> [tag], D1, D2`
Should be read as

```
  D1        D2
------------------ tag
       G
```

```

prove(Sig , A > B) --> { insert(A,Sig,Sig1) }, [weaken(A)], prove(Sig1, A > B).
prove(A > forall(X,B)) --> , prove(weak(X, A) > B).
prove(A > forall(X,B)) --> {insert(X,Sig,Sig2) }, prove(Sig1, A > B).
prove(Sig, forall(X,A) > ) --> , prove(weak(X, A) > B)

```

Maybe start with implication
prove((A > (B > C)  ) --> [curry], prove( A /\ B > C).
prove((A /\ (A > B) > B ) --> [eval].

```
