---
date: 2022-06-28
layout: post
title: "Contextual Datalog: Steps Towards Lambda Datalog"
description: Encoding partial Harrop clauses in Datalog with first class sets
tags: datalog
---

- [First Class Sets and Vectors](#first-class-sets-and-vectors)
    - [Vectors](#vectors)
      - [Comments](#comments)
- [Contexts](#contexts)
- [Reflection](#reflection)
- [Harrop Clauses](#harrop-clauses)
- [Examples](#examples)
- [Bits and Bobbles](#bits-and-bobbles)
- [Vector and Set Code](#vector-and-set-code)

The relationship between datalog and prolog seems to be a source of interesting questions and insights. Take anything from one and ask how it could be applied in the other.

Case in point:

[Lambda Prolog](http://www.lix.polytechnique.fr/Labo/Dale.Miller/lProlog/) is very cool.

I have an interest in how to view datalog as a theorem prover. I want to make a datalog coq tactic.

I want Lambda Datalog.

One of the features of Lambda Prolog is that it is based around Harrop clauses instead of Horn clauses. This means you get access to implication and universal quantification in the body of rules. These have the operational interpretation of locally extending your database with facts and locally extending the symbols with fresh symbols respectively. You can do something kind of sort of similar in regular prolog with [`assert`](https://www.swi-prolog.org/pldoc/man?predicate=assert/1) and `gensym`, but these constructs are not logically motivated the way they are in lambda prolog. It's quite nice.

A big question I've been pursuing for a while is how to encode more of Lambda Prolog into datalog systems. In [egglog0](https://www.philipzucker.com/egglog/), it was one of the first places I went, because the extra capabilities would have made my category theory encoding more satisfactory. I was hand converting Harrop clauses to horn clauses basically at compile time. But I failed to get that mechanized after trying pretty hard. I also hope the seeds of how to deal with binder forms in egraphs will be found in lambda datalog.

But now I think I've got a runtime encoding that works in regular datalog (Souffle)! Pretty stoked. I've been massaging these ideas for a couple months. The big impediment was finally buckling down, compromising, and making a naive first class set implementation using sorted arrays.

[code of post](https://github.com/philzook58/souffle-vector)

# First Class Sets and Vectors

There is something enticing about internalizing the notions of sets or relations into datalog as first class objects. As Cody said, going meta is the one move.

A simple approach is to use [bitsets](https://www.philipzucker.com/notes/Languages/datalog/#bitsets). We have integer data types available and bitwise operations over them. We can extend this outside of 32/64bit universes by using records of numbers. This representation is very good if we have a small universe of values we can talk about, but quite ungainly and inefficient if we don’t.

```souffle
.type bitset <: unsigned
// Operations
#define BOT 0x0
//assuming 32 bit
#define TOP  0xFFFFFFFF 
#define SING(x) (0x1 bshl x)
#define UNION(x,y) (x bor y)
#define ADD(x,set) UNION(SING(x), set)
#define INTER(x,y) (x band y)
#define COMP(x) (TOP bxor x)
#define DIFF(x,y) (x bxor INTER(x,y))

// Predicates
#define ISEMPTY(x) (x = 0)
#define NONEMPTY(x) (x != 0)
#define SUBSET(x,y) ISEMPTY(DIFF(x,y))
#define ELEM(x, set) NONEMPTY(INTER(SING(x), set))

.decl test(l : symbol, b : bitset)
test("ex1", SING(1)).
test("ex1", SING(2)).
test("ex2", DIFF(set, SING(2))) :- test("ex1", set).
test(l,UNION(s1,s2)) :- test(l, s1), test(l,s2).
test(l,s1) <= test(l,s2) :- SUBSET(s1,s2).

.output test(IO=stdout)
```

A key point is that we want a unique representation of the sets, and/or an unique identifier that we can associate to them. Bitsets do have this property.

Going beyond small universes there are couple options. Using some kind of sorted sequence type (vector or List). The sorting ensures the Set is canonical and makes some operations faster. This is what I've gone with for the moment since it was relatively easy.

### Vectors
A vector is a dynamically sized array. Souffle supports records, which are statically sized. The way you can turn static arrays into vectors generally speaking is by adding a `size` field and maybe a little unsafe C++ magic.

So I implemented this. Vectors are represented by a size 2 record `[size, index_to_data]` 

```souffle
.pragma "libraries" "vector"
.type bool <: number
.functor mypush(v : vec, x : number):vec stateful
.functor insort(v : set, x : number):set stateful
.functor myindex(v : set, i : unsigned):number stateful
.functor is_subset(v : set, v2 : set):bool stateful
.functor inter(v : set, v2 : set):set stateful
.functor set_union(v : set, v2 : set):set stateful
.functor set_diff(v : set, v2 : set):set stateful
.functor elem(v : set, x : number):bool stateful


.type vec = [size : unsigned, data : dataN]
.type set = [size : unsigned, data : dataN] // can't subset type records?
.type dataN <: number
.type data1 = [x0 : number]
.type data2 = [x0 : number, x1 : number]

#define EMPTY [0,0]
#define SING(R) @insort(EMPTY, as(R, number))
#define ELEM(set,R) (1 = @elem(set,as(R, number)))
#define REM(ctx,P)  @set_diff(ctx, SING(P))
```

Here is the code for indexing into the vector for example. You need to open up the size, data tuple first. Then get the actual underlying array, then index into that.

```C++
    souffle::RamDomain myindex(
        souffle::SymbolTable *symbolTable, souffle::RecordTable *recordTable, souffle::RamDomain v, souffle::RamDomain i)
    {
        assert(symbolTable && "NULL symbol table");
        assert(recordTable && "NULL record table");

        const souffle::RamDomain *myTuple0 = recordTable->unpack(v, 2);
        const souffle::RamDomain size = myTuple0[0];
        const souffle::RamDomain vec0 = myTuple0[1];
        assert(vec0 != 0 && "Index does not take nil");
        assert(i < size);
        const souffle::RamDomain *data = recordTable->unpack(vec0, size);
        return data[i];
    }
```

You can also use `Lists` <https://www.philipzucker.com/notes/Languages/datalog/#lists> but they are honestly kind of awkward to use. They wouldn't be so bad if I implemented a list library using external functors, but the mental cost of encoding functions into relations and all the other wacky stuff I'm doing is too much.

I could also box all values into a universal type ADT instead of using `number` as my universal type.

Here's some example usage of the vector. Inspecting the contents is annoying, becuase souffle doesn't know how this print this in a useful way. You need to explicitly index into the vector to look at stuff.

```
#include "vector.dl"
#define VEC1 @insort(@insort(@insort(@insort(@insort(@insort(@insort(EMPTY, 17), 32), 24),19),48),17),17)
#define VEC2 @insort(@insort(@insort(@insort(@insort(EMPTY, 17),19),48),17),17)
#define VEC3 @insort(@insort(@insort(@insort(@insort(EMPTY, 37),19),48),17),0)
#define VEC4 @insort(@insort(@insort(@insort(@insort(@insort(@insort(@insort(@insort(@insort(@insort(@insort(@insort(@insort(@insort( \
    @insort(@insort(@insort(@insort(@insort(@insort(@insort(@insort(@insort(@insort(@insort(@insort(@insort(@insort(@insort(EMPTY, 37),19),48),17),0),1),2),3),4),5),6),7),8),9),10),11),12),13),14),15),16),17),18),19),20),21),22),23),24),25)
.decl foo(x : set)
//foo(@mypush(17,@mypush(42,@mypush(3, EMPTY)))) :- true.
//foo(@insort(@insort(@insort(@insort(@insort(@insort(@insort(EMPTY, 17), 32), 24),19),48),17),17)) :- true.
//foo(@inter(VEC2,VEC2)) :- true.
foo(VEC4) :- true.
foo(REM(SING(10),10)) :- true.
//foo(@insort(@insort(@insort(@insort(@insort(@insort(@insort(@insort(@insort(@insort(@insort(@insort(@insort(@insort(@insort(@insort(@insort(@insort(@insort(@insort(@insort(@insort(@insort(@insort(@insort(@insort(@insort(@insort(@insort(@insort([0,0], 37),19),48),17),0),1),2),3),4),5),6),7),8),9),10),11),12),13),14),15),16),17),18),19),20),21),22),23),24)) :- true.
.decl bar (t : symbol, x : number, i : unsigned)
bar("t1", @myindex(v,i), i) :- foo(v), i = range(0,size),  v = [size,_data].
bar("t2", @myindex(v,i), i) :- v = @inter(VEC2,VEC1), i = range(0,3).
bar("t3", @myindex(v,i), i) :- v = @inter(VEC3,VEC2), i = range(0,3).
bar("t4", @myindex(v,i), i) :- v = VEC3, i = range(0,5).
bar("t5", @myindex(v,i), i) :- v = VEC2, i = range(0,3).
bar("t6", @myindex(v,i), i) :- v = @set_union(VEC3,VEC1), i = range(0,7).
bar("t7", @myindex(v,i), i) :- v = @set_diff(VEC3,VEC1), i = range(0,2).
bar("t8", @myindex(v,i), i) :- v = @set_diff(VEC2,VEC3), i = range(0,0).
bar("t9", @myindex(v,i), i) :- v = @set_diff(VEC2,VEC2), i = range(0,0).
bar("t10", @myindex(v,i), i) :- v = REM(SING(10),10), i = range(0,0).


.decl biz(t : symbol, x : bool)
biz("t0",@is_subset(EMPTY, EMPTY)) :- true.
biz("t-1", @is_subset(@insort(EMPTY,3), EMPTY)) :- true.
biz("t-2", @is_subset(@insort(EMPTY,3), @insort(EMPTY,3))) :- true.

biz("t1", @is_subset(VEC1, VEC2)) :- true.
biz("t2", @is_subset(VEC2, VEC1)) :- true.
biz("t3", @is_subset(VEC3, VEC2)) :- true.
biz("t4", @is_subset(VEC3, VEC1)) :- true.
biz("t5", @is_subset(VEC1, VEC3)) :- true.
biz("t6", @is_subset(VEC2, VEC3)) :- true.

//biz("t7",as(size,bool)) :- VEC3 = [size,_data].


.output foo(IO=stdout)
.output bar(IO=stdout)
.output biz(IO=stdout)
```

#### Comments 
A quite nice approach for sets is that of Patricia tries. Patricia tries are a commonly used functional data structure for intsets. They are canonical for a given set (unlike ordinary binary search trees). See for example the Haskell or ocaml libraries.

I'll note there is a history of internalizing sets as objects in datalog, but many of these systems seem like they have died off. See  LDL, Hilog, COL, relationlog.
- [Overview of Datalog Extensions with Tuples and Sets (1998)](http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.39.9904) 
- [The expressive power of higher order datalog](https://arxiv.org/pdf/1907.09820.pdf)


# Contexts
In datalog, you need to carry around what you need to remember in your tuples. You don't have prolog's stack to keep track of things for you. 

For Harrop clauses, we need to track a context of what hypothetical facts are in scope, a contextual database if you will. We do this by extending every relation with a context field

```
.type ctx = set
.decl r(ctx : ctx)
.decl q(ctx : ctx)
.decl s(ctx : ctx)
.decl t(ctx : ctx)
.decl u(ctx : ctx)
```

It is somewhat compelling to realize that one could in principle write `r(ctx)` as infix notation `ctx |- r`. Also be aware that datalog's `:-` is actually a closer match for an inference rule horizontal line than it is for the implication arrow. [See Pfenning notes for more](https://www.cs.cmu.edu/~fp/courses/15317-f17/lectures/18-datalog.pdf) So for example, we could read

`foo(@set_union(ctx1,ctx2)) :- bar(ctx1), biz(ctx2).` as

```
G1 |- bar     G2 |- biz
-----------------------
      G1 U G2 |- foo 
```


It is a theme in datalog encodings that you may need to enhance the number of fields of every relation. This is how you can do provenance for example. Contexts are related to provenance. They are tracking certain "marked" entities are in the proof tree. For example, we could want to have have a lattice that checks if a fact requires `foo(3)`, ie every proof has a `foo(3)` somewhere in it.

Now rules that do not manipulate contexts need to carry them along. You need to have a context that is the union of all the contexts you're previous facts required.

```
/*
Old rules:
s :- r, q.
t :- q, u.
q :- r.

In inference rule notation:

G1 |- r    G2 |- q
-----------------------
    G1 U G2 |- s

*/
s(@set_union(c1,c2)) :- r(c1), q(c2).
t(@set_union(c1,c2)) :- q(c1), u(c2).
q(ctx) :- r(ctx).
```

We should only maintain the weakest contexts requires to derive certain facts. Datalog subsumption is sufficient to implement this by removing any facts that exist under contexts that are dominated by another. This is the anti-chain lattice action I referred to earlier.

```
    G |- p
--------------- weak
   G, A |- p

p(ctx1) <= p(ctx2) :- 1 = @is_subset(ctx2, ctx1).

```

Subsumption is actually a natural fit for this application, but contexts can be encoded into a Datalog with lattices also. The lattice in question is the [antichain](https://en.wikipedia.org/wiki/Antichain) lattice of the powerset of facts.


# Reflection
We need to put relation rows into our context sets. These contexts only hold data objects (numbers, strings, adts), not relations. How do we do it?

Prolog makes it easy to have both a term `foo(x)` and a proposition `foo(x)` and not notice you've overloaded concepts. I'm not complaining, this is really nice. They are however extremely different.
What foo is in these two situations is vastly different. In the first, it is something like the analog of a function definition in the second it is something like defining a tree datastructure that is returned by `good`.

```
foo(x).
good(foo(x)).
```

In souffle datalog, we have to be a little more explicit when we reflect our predicates as objects. You can make an ADT that has one constructor for every predicate you want to talk about.

```souffle
.type Prop = S {} | Q {} | R {} | T {} | U {} | Foo {a : symbol, b : number}
.decl r()
.decl q()
.decl s()
.decl t()
.decl u()
.decl foo(a : symbol, b : number)
```

You can already do weird stuff. For example, you can define a global relation that is capable of replacing every usage of the original relations. I don't recommend such a thing if you can avoid it, you're paying a cost in indexing and packing and unpacking these records.

```souffle
.decl rel(p : Prop)

//foo(x,y) :- foo(x,y), foo(x, y + 1).
rel($Foo(x,y)) :- rel($Foo(x,y)), rel($Foo(x,y+1)).

```

With this we can no desrcibe a simple axiom rule. You may derive a fact in the context of itself. These are going to be the leaves of many of our proof trees.


```
/*

---------Ax
 r |- r         
 
*/


r(SING($R())).
q(SING($Q())).
s(SING($S())).
t(SING($T())).
u(SING($U())).
```

# Harrop Clauses
Harrop clauses enable you to use `=>` in more positions than just the single one separating rule head from body.

So what I am proposing here is a method by which to encode `=>` into the bodies of datalog rules. Souffle does not understand `=>` so what do we do? The meaning of logical connectives is described by the inference rules in which you can use them. This often includes an introduction and elimination form. Consider `p => q`. I can write this as a monolithic fresh name `p_q`. In what sense is `p_q` the same as `p => q`? Well it's the same in the sense that I have two rules

```
G1 |- p => q    G2 |- p
-------------------- E =>
    G U G2 |- q

// in datalog notation
q(@set_union(g1,g2)) :- p_q(g1), p(g2).


      G |- q
----------------- I =>
G \ {p} |- p => q


// in datalog notation
p_q(REM(g, $P())) :- q(g).

```

This inventing a first class name for a higher order thing is highly reminiscent of defunctionalization. These sort of defunctionaliztion games seem common when you're trying to encode higher order concepts into a weaker first order system. See SMT theory of arrays or Haskell [singletons](https://typesandkinds.wordpress.com/2013/04/01/defunctionalization-for-the-win/) library.


With that I think I've described the core tricks.

If you want to emulate lambda prolog magic set style, there are some context extending rules you might want also. You only trigger the Ax rules in the presence of something top down triggering them. Thinking these were the primary rules of interest confused me for quite a while.

# Examples

I took some simple propositional examples from chapter 3 of [Programming with Higher Order Logic](https://www.amazon.com/Programming-Higher-Order-Logic-Dale-Miller/dp/052187940X)

```souffle
#include "vector.dl"

.type Prop = Q {} | R{} | R_T {} | R_U {} |  R_U_R_T {} |  S {} | T {} | U {} 
.type ctx = set

.decl r(ctx : ctx)
.decl q(ctx : ctx)
.decl s(ctx : ctx)
.decl t(ctx : ctx)
.decl u(ctx : ctx)

// query2 :- (r => u) => (r => t).
.decl r_u(ctx : set)
.decl r_t(ctx : set)
.decl r_u_r_t(ctx : set)

// Implication introduction and elimination
#define IMPL(r_u,r,u, R) r_u(REM(ctx, $R())) :- u(ctx). u(@set_union(ctx1,ctx2)):- r_u(ctx1), r(ctx2).
IMPL(r_u,r,u, R)
IMPL(r_t, r, t, R)
IMPL(r_u_r_t, r_u, r_t, R_U)


/* Refl rules
---------
 p |- p
*/

r(SING($R())).
q(SING($Q())).
s(SING($S())).
t(SING($T())).
u(SING($U())).
r_u(SING($R_U())).
r_t(SING($R_T())).
r_u_r_t(SING($R_U_R_T())).

/*
These have the interpretation of weakening rules.
   Gam |- q    Gam <= Gam2
-----------------------
   Gam1  |-  q
*/
#define SUBSUMES(q) q(ctx1) <= q(ctx2) :- 1 = @is_subset(ctx2, ctx1).
SUBSUMES(q)
SUBSUMES(s)
SUBSUMES(r)
SUBSUMES(t)
SUBSUMES(u)
SUBSUMES(r_u)
SUBSUMES(r_t)
SUBSUMES(r_u_r_t)

/* s :- r, q.
   t :- q, u.
   q :- r.   */
s(@set_union(c1,c2)) :- r(c1), q(c2).
t(@set_union(c1,c2)) :- q(c1), u(c2).
q(ctx) :- r(ctx).

/*

G1 |- r  G2 |- q
-----------------
   G1 U G2 |- s

*/

.output r_u_r_t(IO=stdout)
.output t(IO=stdout)
.output u(IO=stdout)
.output r(IO=stdout)
.output r_t(IO=stdout)


.decl print_ctx(l : symbol, ctx : set, p : Prop)
print_ctx("t", ctx, p) :- t(ctx), ctx = [size,_data], i = range(0,size), p = as(@myindex(ctx,i), Prop).
print_ctx("u", ctx, p) :- u(ctx), ctx = [size,_data], i = range(0,size), p = as(@myindex(ctx,i), Prop).
print_ctx("r_t", ctx, p) :- r_t(ctx), ctx = [size,_data], i = range(0,size), p = as(@myindex(ctx,i), Prop).
//print_ctx("r", ctx, @myindex(ctx,i)) :- r(ctx), ctx = [size,_data], i = range(0,size).

.output print_ctx(IO=stdout)

/* Output:
---------------
r
===============
[1, 1]
===============
---------------
u
===============
[1, 3]
[2, 4]
===============
---------------
r_t
===============
[1, 2]
[1, 3]
[1, 7]
[1, 5]
===============
---------------
r_u_r_t
===============
[0, 0]
===============
---------------
t
===============
[2, 4]
[1, 7]
[2, 6]
[2, 11]
[2, 3]
===============
---------------
print_ctx
===============
t       [2, 4]  $R
t       [2, 4]  $R_U
t       [1, 7]  $T
t       [2, 6]  $R
t       [2, 6]  $U
t       [2, 11] $Q
t       [2, 11] $U
t       [2, 3]  $R
t       [2, 3]  $R_T
u       [1, 3]  $U
u       [2, 4]  $R
u       [2, 4]  $R_U
r_t     [1, 2]  $R_U
r_t     [1, 3]  $U
r_t     [1, 7]  $T
r_t     [1, 5]  $R_T
===============
*/
```

Interestingly, the book states the following example is non terminating in the depth first search semantics. No problem here!

```souffle

//(q :- (q => q)) => (q :- (q => q)).

#include "vector.dl"

.type Prop = Q {} | Q_Q {} | Q_Q_Q {} | Q_Q_Q_Q_Q_Q {}
.type ctx = set

.decl q(ctx : ctx)
.decl q_q(ctx : ctx)
.decl q_q_q(ctx : ctx)
.decl q_q_q_q_q_q(ctx : ctx)


// Implication introduction and elimination
#define IMPL(r_u,r,u, R) r_u(REM(ctx, $R())) :- u(ctx). u(@set_union(ctx1,ctx2)):- r_u(ctx1), r(ctx2).
IMPL(q_q, q, q, Q)
IMPL(q_q_q, q_q, q, Q_Q)
IMPL(q_q_q_q_q_q, q_q_q, q_q_q, Q_Q_Q)



/* Refl rules
---------
 p |- p
*/


q(SING($Q())).
q_q(SING($Q_Q())).
q_q_q(SING($Q_Q_Q())).
q_q_q_q_q_q(SING($Q_Q_Q_Q_Q_Q())).

/*
q  |- q
{} |- q_q

*/


/*
These have the interpretation of weakening rules.
   Gam |- q    Gam <= Gam2
-----------------------
   Gam1  |-  q
*/
#define SUBSUMES(q) q(ctx1) <= q(ctx2) :- 1 = @is_subset(ctx2, ctx1).
SUBSUMES(q)
SUBSUMES(q_q)
SUBSUMES(q_q_q)
SUBSUMES(q_q_q_q_q_q)


/*

G1 |- r  G2 |- q
-----------------
   G1 U G2 |- s

*/

// Ah, I'm not printing the empty context boys.
.output q_q(IO=stdout)
.output q(IO=stdout)
.output q_q_q(IO=stdout)
.output q_q_q_q_q_q(IO=stdout)

.decl print_ctx(l : symbol, ctx : set, p : Prop)
print_ctx("q", ctx, p) :- q(ctx), ctx = [size,_data], i = range(0,size), p = as(@myindex(ctx,i), Prop).
print_ctx("q_q_q", ctx, p) :- q_q_q(ctx), ctx = [size,_data], i = range(0,size), p = as(@myindex(ctx,i), Prop).
print_ctx("q_q", ctx, p) :- q_q(ctx), ctx = [size,_data], i = range(0,size), p = as(@myindex(ctx,i), Prop).
print_ctx("q6", ctx, p) :- q_q_q_q_q_q(ctx), ctx = [size,_data], i = range(0,size), p = as(@myindex(ctx,i), Prop).
//print_ctx("r", ctx, @myindex(ctx,i)) :- r(ctx), ctx = [size,_data], i = range(0,size).

.output print_ctx(IO=stdout)

/*
---------------
q
===============
[1, 1]
[1, 3]
===============
---------------
q_q
===============
[0, 0]
===============
---------------
q_q_q
===============
[1, 1]
[1, 3]
===============
---------------
q_q_q_q_q_q
===============
[0, 0]
===============
---------------
print_ctx
===============
q       [1, 1]  $Q
q       [1, 3]  $Q_Q_Q
q_q_q   [1, 1]  $Q
q_q_q   [1, 3]  $Q_Q_Q
===============
*/



```


# Bits and Bobbles
I don't yet know how to really do universal quantification elegantly. :(  
We'll get there.

I have internalized lambda terms as objects and Miller matching HOAS. I haven't done it in souffle yet. Another blog post.

[ELPI tabling](https://github.com/LPCIC/elpi/pull/118)

What does this have to do with egglog?

In hindsight, for the examples I'm showing here, bitsets would have been sufficient, but going forward they are not.

Utility in enumerating all contexts?
```
allctxs(EMPTY).
allctxs(@insrt(ctx, t)) :- allctxs(ctx), (t = $Q() ; t = $R() ; ...).  


```


# Vector and Set Code

Useful examples in the souffle repo <https://github.com/souffle-lang/souffle/blob/master/tests/interface/functors/functors.cpp>

```C++
#include <cstdint>
#include "souffle/SouffleFunctor.h"
#include <cassert>
#include <vector>
#if RAM_DOMAIN_SIZE == 64
using FF_int = int64_t;
using FF_uint = uint64_t;
using FF_float = double;
#else
using FF_int = int32_t;
using FF_uint = uint32_t;
using FF_float = float;
#endif

// https://github.com/souffle-lang/souffle/blob/master/tests/interface/functors/functors.cpp
extern "C"
{


    souffle::RamDomain mypush(
        souffle::SymbolTable *symbolTable, souffle::RecordTable *recordTable, souffle::RamDomain v, souffle::RamDomain x)
    {
        assert(symbolTable && "NULL symbol table");
        assert(recordTable && "NULL record table");

        const souffle::RamDomain *myTuple0 = recordTable->unpack(v, 2);
        const souffle::RamDomain size = myTuple0[0];
        const souffle::RamDomain vec0 = myTuple0[1];
        if (vec0 == 0)
        { // nil
            assert(size == 0);
            // souffle::RamDomain vec[1] = {x};
            const souffle::RamDomain vec2 = recordTable->pack(&x, 1);
            souffle::RamDomain myTuple1[2] = {1, vec2};
            return recordTable->pack(myTuple1, 2);
        }
        else
        {
            const souffle::RamDomain *data = recordTable->unpack(vec0, size);
            std::vector<souffle::RamDomain> vec;
            for (int i = 0; i < size; i++)
            {
                vec.push_back(data[i]);
            }
            vec.push_back(x);
            const souffle::RamDomain vec2 = recordTable->pack(vec.data(), size + 1);
            souffle::RamDomain myTuple1[2] = {size + 1, vec2};
            return recordTable->pack(myTuple1, 2);
        }
    }

    souffle::RamDomain myindex(
        souffle::SymbolTable *symbolTable, souffle::RecordTable *recordTable, souffle::RamDomain v, souffle::RamDomain i)
    {
        assert(symbolTable && "NULL symbol table");
        assert(recordTable && "NULL record table");

        const souffle::RamDomain *myTuple0 = recordTable->unpack(v, 2);
        const souffle::RamDomain size = myTuple0[0];
        const souffle::RamDomain vec0 = myTuple0[1];
        assert(vec0 != 0 && "Index does not take nil");
        assert(i < size);
        const souffle::RamDomain *data = recordTable->unpack(vec0, size);
        return data[i];
    }

    souffle::RamDomain insort(
        souffle::SymbolTable *symbolTable, souffle::RecordTable *recordTable, souffle::RamDomain v, souffle::RamDomain x)
    {
        assert(symbolTable && "NULL symbol table");
        assert(recordTable && "NULL record table");

        const souffle::RamDomain *myTuple0 = recordTable->unpack(v, 2);
        const souffle::RamDomain size = myTuple0[0];
        const souffle::RamDomain vec0 = myTuple0[1];
        if (vec0 == 0)
        { // nil
            assert(size == 0);
            // souffle::RamDomain vec[1] = {x};
            const souffle::RamDomain vec2 = recordTable->pack(&x, 1);
            souffle::RamDomain myTuple1[2] = {1, vec2};
            return recordTable->pack(myTuple1, 2);
        }
        else
        {
            const souffle::RamDomain *data = recordTable->unpack(vec0, size);
            std::vector<souffle::RamDomain> vec;
            bool added = false;
            for (int i = 0; i < size; i++)
            {
                souffle::RamDomain q = data[i];
                if (q == x)
                { // already in set.
                    return v;
                }
                else if (!added && q > x)
                {
                    vec.push_back(x);
                    added = true;
                }
                vec.push_back(q);
            }
            if (!added)
            {
                vec.push_back(x);
            }
            const souffle::RamDomain vec2 = recordTable->pack(vec.data(), size + 1);
            souffle::RamDomain myTuple1[2] = {size + 1, vec2};
            return recordTable->pack(myTuple1, 2);
        }
    }

    souffle::RamDomain elem(
        souffle::SymbolTable *symbolTable, souffle::RecordTable *recordTable, souffle::RamDomain v, souffle::RamDomain x)
    {
        assert(symbolTable && "NULL symbol table");
        assert(recordTable && "NULL record table");

        const souffle::RamDomain *myTuple0 = recordTable->unpack(v, 2);
        const souffle::RamDomain size = myTuple0[0];
        const souffle::RamDomain vec0 = myTuple0[1];
        if (vec0 == 0)
        { // nil
            return 0;
        }
        else
        {
            // Could do smarter binary search if sorted
            const souffle::RamDomain *data = recordTable->unpack(vec0, size);
            for (int i = 0; i < size; i++)
            {
                souffle::RamDomain q = data[i];
                if (q == x)
                { // already in set.
                    return 1;
                }
            }
            return 0;
        }
    }

    souffle::RamDomain is_subset(
        souffle::SymbolTable *symbolTable, souffle::RecordTable *recordTable, souffle::RamDomain v1, souffle::RamDomain v2)
    {
        assert(symbolTable && "NULL symbol table");
        assert(recordTable && "NULL record table");

        const souffle::RamDomain *myTuple0 = recordTable->unpack(v1, 2);
        const souffle::RamDomain size1 = myTuple0[0];
        const souffle::RamDomain vec1 = myTuple0[1];
        if (vec1 == 0)
        {             // nil
            return 1; // true
        }
        else
        {
            const souffle::RamDomain *myTuple0 = recordTable->unpack(v2, 2);
            const souffle::RamDomain size2 = myTuple0[0];
            const souffle::RamDomain vec2 = myTuple0[1];
            if (vec2 == 0)
            {             // nil
                return 0; // true
            }
            if (size1 > size2)
            {
                return 0; // false. smaller set must be subset
            }
            if (vec2 == vec1 && size1 == size2)
            {
                return 1; // equal
            }

            const souffle::RamDomain *data1 = recordTable->unpack(vec1, size1);
            const souffle::RamDomain *data2 = recordTable->unpack(vec2, size2);
            int i1 = 0;
            for (int i2 = 0; i2 < size2; i2++)
            {
                // These are both early return optimizations
                if (i1 == size1)
                {
                    return 1;
                }
                if (data1[i1] < data2[i2]) // we passed where we should have found data1[i1]
                {
                    return 0;
                }
                // The only one that actually matters.
                else if (data1[i1] == data2[i2])
                {
                    i1++;
                }
                // else data1[i1] > data2[i2] hence we still need to seek
            }
            if (i1 == size1) // we saw all of vec1 in vec2
            {
                return 1;
            }
            else
            {
                return 0;
            }
        }
    }

    // Hmm. I could also have convention that nil = [0,nil]. That would make sense. Could get two nils then. Meh.
    souffle::RamDomain inter(
        souffle::SymbolTable *symbolTable, souffle::RecordTable *recordTable, souffle::RamDomain v1, souffle::RamDomain v2)
    {
        assert(symbolTable && "NULL symbol table");
        assert(recordTable && "NULL record table");
        if (v2 == v1)
        {
            return v2; // equal
        }
        const souffle::RamDomain *myTuple1 = recordTable->unpack(v1, 2);
        const souffle::RamDomain size1 = myTuple1[0];
        const souffle::RamDomain vec1 = myTuple1[1];
        if (vec1 == 0) // nil
        {
            return v1;
        }
        else
        {
            const souffle::RamDomain *myTuple2 = recordTable->unpack(v2, 2);
            const souffle::RamDomain size2 = myTuple2[0];
            const souffle::RamDomain vec2 = myTuple2[1];
            if (vec2 == 0) // nil
            {
                return v2; // nil
            }
            const souffle::RamDomain *data1 = recordTable->unpack(vec1, size1);
            const souffle::RamDomain *data2 = recordTable->unpack(vec2, size2);
            int i1 = 0;
            int i2 = 0;
            std::vector<souffle::RamDomain> vec3;
            while (i1 < size1 && i2 < size2)
            {

                if (data1[i1] < data2[i2])
                {
                    i1++;
                }
                else if (data1[i1] == data2[i2])
                {
                    vec3.push_back(data1[i1]);
                    i1++;
                    i2++;
                }
                else if (data1[i1] > data2[i2])
                {
                    i2++;
                }
            }
            souffle::RamDomain size = vec3.size();
            const souffle::RamDomain vec4 = recordTable->pack(vec3.data(), size);
            souffle::RamDomain myTuple1[2] = {size, vec4};
            return recordTable->pack(myTuple1, 2);
        }
    }

    souffle::RamDomain set_union(
        souffle::SymbolTable *symbolTable, souffle::RecordTable *recordTable, souffle::RamDomain v1, souffle::RamDomain v2)
    {
        assert(symbolTable && "NULL symbol table");
        assert(recordTable && "NULL record table");
        if (v1 == v2)
        {
            return v2; // equal
        }
        const souffle::RamDomain *myTuple1 = recordTable->unpack(v1, 2);
        const souffle::RamDomain size1 = myTuple1[0];
        const souffle::RamDomain vec1 = myTuple1[1];
        if (vec1 == 0) // nil
        {
            return v2;
        }
        else
        {
            const souffle::RamDomain *myTuple2 = recordTable->unpack(v2, 2);
            const souffle::RamDomain size2 = myTuple2[0];
            const souffle::RamDomain vec2 = myTuple2[1];
            if (vec2 == 0) // nil
            {
                return v1; // nil
            }

            const souffle::RamDomain *data1 = recordTable->unpack(vec1, size1);
            const souffle::RamDomain *data2 = recordTable->unpack(vec2, size2);
            int i1 = 0;
            int i2 = 0;
            std::vector<souffle::RamDomain> vec3;
            // merge of mergesort essentially
            while (i1 < size1 && i2 < size2)
            {
                if (data1[i1] < data2[i2])
                {
                    vec3.push_back(data1[i1]);
                    i1++;
                }
                else if (data1[i1] == data2[i2])
                {
                    vec3.push_back(data1[i1]);
                    i1++;
                    i2++;
                }
                else if (data1[i1] > data2[i2])
                {
                    vec3.push_back(data2[i2]);
                    i2++;
                }
            }
            // cleanup. Only one for loop can actually run.
            for (int i = i1; i < size1; i++)
            {
                vec3.push_back(data1[i]);
            }
            for (int i = i2; i < size2; i++)
            {
                vec3.push_back(data2[i]);
            }
            souffle::RamDomain size = vec3.size();
            const souffle::RamDomain vec4 = recordTable->pack(vec3.data(), size);
            souffle::RamDomain myTuple1[2] = {size, vec4};
            return recordTable->pack(myTuple1, 2);
        }
    }

    souffle::RamDomain set_diff(
        souffle::SymbolTable *symbolTable, souffle::RecordTable *recordTable, souffle::RamDomain v1, souffle::RamDomain v2)
    {
        assert(symbolTable && "NULL symbol table");
        assert(recordTable && "NULL record table");
        if (v1 == v2) // return empty set
        {
            souffle::RamDomain myTuple1[2] = {0, 0};
            return recordTable->pack(myTuple1, 2);
        }
        const souffle::RamDomain *myTuple1 = recordTable->unpack(v1, 2);
        const souffle::RamDomain size1 = myTuple1[0];
        const souffle::RamDomain vec1 = myTuple1[1];
        if (vec1 == 0) // nil
        {
            return v1;
        }
        else
        {
            const souffle::RamDomain *myTuple2 = recordTable->unpack(v2, 2);
            const souffle::RamDomain size2 = myTuple2[0];
            const souffle::RamDomain vec2 = myTuple2[1];
            if (vec2 == 0) // nil
            {
                return v1; // return v1 unchanged
            }

            const souffle::RamDomain *data1 = recordTable->unpack(vec1, size1);
            const souffle::RamDomain *data2 = recordTable->unpack(vec2, size2);
            int i1 = 0;
            int i2 = 0;
            std::vector<souffle::RamDomain> vec3;
            while (i1 < size1 && i2 < size2)
            {
                if (data1[i1] < data2[i2])
                {
                    vec3.push_back(data1[i1]);
                    i1++;
                }
                else if (data1[i1] == data2[i2])
                {
                    i1++;
                    i2++;
                }
                else if (data1[i1] > data2[i2])
                {
                    i2++;
                }
            }
            for (int i = i1; i < size1; i++)
            {
                vec3.push_back(data1[i]);
            }
            souffle::RamDomain size = vec3.size();
            const souffle::RamDomain vec4 = recordTable->pack(vec3.data(), size);
            souffle::RamDomain myTuple1[2] = {size, vec4};
            return recordTable->pack(myTuple1, 2);
        }
    }
}

/*
What other functions are useful?
Sort
An array based map.
Is it possible souffle garbage collects records?

elem
subset
union
inter


*/

```









