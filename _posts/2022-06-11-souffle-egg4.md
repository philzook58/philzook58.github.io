---
date: 2022-06-11
layout: post
title: "E-Graphs in Souffle IV: It's actually kind of fast this time"
description: Finally a reasonably fast embedding of egraphs into souffle datalog
---

Based on the insights of [relational e-matching](https://arxiv.org/abs/2108.02290) and [egglog0](https://www.philipzucker.com/egglog), I've been attempting to embed [e-graphs](https://www.philipzucker.com/notes/Logic/egraphs/) into [Souffle datalog](https://souffle-lang.github.io/) on and off for over a year. Here's some relevant previous posts in that direction:

- [Encoding E-graphs to Souffle Datalog](https://www.philipzucker.com/egraph-datalog/) Points out that datalog easy expressed some subproblems in equality saturation. Rebuilding (congruence closure and canonicalization) is clearly some kind of fixed point operation. E-matching is a kind of graph matching and datalog is one of the most convenient languages for graph matching I know. Looking back at this post, it seems like I understood a lot of things even back then. I'm not sure why it has taken so long for this idea to work. I grew discouraged and switched to overlaying datalog on top of egg (egglog0)
- [Naive E-graph Rewriting in Souffle Datalog](https://www.philipzucker.com/datalog-egraph-deux/) Naive encoding using ADTs - Very straightforward, however does not at all properly share pieces the way egraphs do. Nice for conceptual modelling, but this is ultimately unacceptable.
- [A Questionable Idea: Hacking findParent into Souffle with User Defined Functors](https://www.philipzucker.com/souffle-functor-hack/) - The first attempt at hacking a union find primitive into Souffle as an awkward untrustworthy backdoor. In this last encoding, using ADTs somewhat clunked up the representation. ADTs are in general to better way to generate new objects in datalog as compared to the `autoinc()` counter. This is because ADTs hash cons themselves, so you won't generate the same ADT twice. This improves termination and database size significantly. This intuition seems to have failed me here. autoinc() is now ok, but only because of the unusual stratified datalog encoding.

The toy benchmark problem that I've been using is associativity and commutativity of ``1 + 2 + ... 9`. These embeddings were ultimately failures, because they were just plain too slow, like a minute or nonterminating.

But I have a different encoding which is slightly different. And it is competitive with egg itself in speed I think!

Here is the output of the latest encoding running in souffle compiled mode with parallel `-j 4`

```
phil:~/Documents/prolog/soffule/egraphexist$ time ./run_comp.sh 
add1    23
add1    51
add1    129
add1    402
add1    1451
add1    5692
add1    15648
add1    18660
add1    18660

real    0m0.544s
user    0m1.779s
sys     0m0.063s
```

It saturates quickly and `18660 = 3^9-2^10+1` is the correct number of enodes of a fully associative commutative egraph expansion of `1 + 2 + ... 9` . See previous blog post for explanation of this calculation.

### Idea 1: External Fixedpoint 
Egg uses a fixedpoint of ematch -> rebuild -> repeat. This is a good idea because it is really important to keep your egraph free of junk and rebuilding does that. Rebuilding shrinks the egraph, ematching often grows it. The actual space of terms being represented is horrifically exponential and an unrebuilt egraph starts to see that. 

To express this in datalog, we need a notion of scoped or nested fixedpoints. Typically datalog mashes everything (or at least each strata / scc of relation dependence) into a big single fixedpoint. It seems that allowing this will make the egraph get too unclean too quickly as evidenced by the slowness of the previous blog post.

One way to achieve this is to put a fixedpoint at the "bash" level. If we write our datalog program to take in a database and output a database, we can run souffle in a bash for-loop until saturation.

This can be implemented by making a separate input and output relation that feed into the same file in souffle.
```souffle
.input add0
.output add(filename="add0.facts")
```

### Idea 2: External UnionFind
The external unionfind is an idea that I tried in the previous blog post and failed, but I think it is now a key ingredient.

One big problem with the hacked in external unionfind is that it adds an imperative operational dependence that is impossible to reason about. Souffle is free to shred it's rules in whatever way it likes and it does. What has especially bitten me in the past is assuming that `foo,biz.baz` in the head "foo(x), biz(x), baz(x) :- gum(x)" have to occur temporally near each other. They do not. Souffle immediately expands this rule at the very first stage into 3 simpler rules.

One thing we actually _can_ kind of count on is souffle to obey stratification. We can basically guarantee that if strata n relies on a relation produced in strata m, `m < n`, then souffle really will calculate strata m first.

It is definitely possible (easier even) to build a datalog that mashes all strata together (in the absence of negation), but souffle doesn't because it is more efficient to finish strata one at a time.

In particular, the interplay of the imperative unionfind and subsumption. It was to my great pleasure that subsumption actually seems to hurt rather than help on my examples. I'm glad to leave it behind, but we'll see.

It is ok to not fully complete congruence closure, but it is not obviously ok to not complete canonicalization of ids if we are blowing up the union find on every iteration with the above mentioned bash loop. The union find lives in the souffle process and we are shutting it down and restarting it. The strata ordering is enough to guarantee this though. This also has the benefit of filtering out anything stale that may be in `add1`, removing one of the needs for subsumption.

```souffle
add1(@findRoot(x),@findRoot(y),@findRoot(z)) :- add(x,y,z).
.output add1(filename="add0.facts")
```

### Idea 3: The Dirty Relation 

The basic congruence closure algorithm is easily expressible in datalog. This is part of the compelling case for using datalog to implement egraphs
```.
eq(z,z1) :- add(x,y,z), add(x,y,z1), z != z1.
```

However, we aren't really using an `eq` that datalog understands or is aware of. So datalog doesn't know that adding to `eq` could trigger more rebuilding.

A mechanism by which to help datalog along is the add a `dirty` relation.

```.
add(@findNode(x),@findNode(y),@findNode(z)) :- add(x,y,z), (true; dirty(x) ; dirty(y)).
dirty(@unionNodes(z,z1)), dirty(z), dirty(z1) :- add(x,y,z), add(x,y,z1), z1 != z, (true; dirty(x) ; dirty(y)).
```

the underlying seminaive `delta_dirty` relation is plahying a role analagous to the dirty worklist in egg. Relational joining dirty on add is achieving a lookup similar to using the parents table in egg.

Now, as written there is no guarantee that dirty will fully rebuild `add`. But this is ok because of mentioned in idea 2.

```souffle
add1(@findRoot(x),@findRoot(y),@findRoot(z)) :- add(x,y,z).
.output add1(filename="add0.facts")
```

Failing to fully complete congruence closure appears to not be a disaster.

To be fully honest, I fiddled with where to put `dirty`s until it worked well. I am not entirely clear that I shouldn't have more.

If you want a more complete rebuild, it is possible to tag `dirty(x,iter)` with extra integers in such a way that you can double dirty. It is not clear that even this technique is fully congruence closing, so buyer beware.

### Idea 4: Separate autoinc() rules and rewrite rules

Still rebuilding is leaky and needs to be nursed, so we need to go out of our way to not put unnecessary pressure on it.

My go to example for testing ideas in egraph's is commutativity and associativity of addition. Commutativity `a + b = b + a` is a very simple rule. There are no joins that need to happen and no new eclasses ever need to be generated

```
add(y,x,xy) :- add0(x,y,xy).
```

Associativity `a + (b + c) = (a + b) + c` is much more complex. It has a join and does _sometimes_ need to generate a new id.

Naively this works.
```
add(y,z,autoinc()) :- add0(_x,y,xy), add0(xy,z,_xyz).
add(x,y,autoinc()) :- add0(x,yz,_xyz), add0(y,_z,yz).
```

However this is putting unnecessary pressure on rebuilding, generating new names that will need to be congruenced. Instead we can seperate this into two rules per direction (this idea came from discussions with Max, Zach, Yihong). One rule generates the necessary id to complete the rewrite if it doesn't exist (the awkward `count` guard), and the other looks up the id and uses it, more similar to the commutativity example.

```
// generate new ids needed for certain rules
add(y,z,autoinc() + mid) :- add0(_x,y,xy), add0(xy,z,_xyz), 0 = count : add0(y,z,_yz), maxid0(mid).
add(x,y,autoinc() + mid) :- add0(x,yz,_xyz), add0(y,_z,yz), 0 = count : add0(x,y,_xy), maxid0(mid).

add(x,yz,xyz) :- add0(x,y,xy), add0(xy,z,xyz), add0(y,z,yz).
add(xy,z,xyz) :- add0(x,yz,xyz), add0(y,z,yz), add0(x,y,xy).
```

It is not entirely clear this idea is 100% crucial. Perhaps the other ideas are enough to make rebuilding strong enough to handle unnecssary autoinc here.

Note also the `maxid0` predicate which is shown below, which is necessary because we need to generate fresh ids and autoinc's state is not retained between souffle runs.

## Code


```souffle
.pragma "libraries" "unionfind"
.decl add0(x:number, y : number, z : number)
.decl add(x:number, y : number, z : number)
.decl add1(x : number, y : number, z : number)
.decl maxid0(x : number)
.decl id0(x : number)
.decl dirty(z : number)
.functor findNode(number):number 
.functor unionNodes(number,number):number

// should go in separate file
add0(1,2,12).
add0(12,3,123).
add0(123,4,1234).
add0(1234,5,12345).
add0(12345,6,123456).
add0(123456,7,1234567).
add0(1234567,8,12345678).
add0(12345678,9,123456789).

.input add0

// calculate fresh id offset
id0(x) :- add0(x,_,_).
id0(y) :- add0(_,y,_).
id0(z) :- add0(_,_,z).

maxid0(x) :- x = 1 + max t : id0(t).

// generate new ids needed for certain rules
add(y,z,autoinc() + mid) :- add0(_x,y,xy), add0(xy,z,_xyz), 0 = count : add0(y,z,_yz), maxid0(mid).
add(x,y,autoinc() + mid) :- add0(x,yz,_xyz), add0(y,_z,yz), 0 = count : add0(x,y,_xy), maxid0(mid).
add(x,y,z) :- add0(x,y,z).

// Ematch for rewrites
add(y,x,xy) :- add0(x,y,xy).
add(x,yz,xyz) :- add0(x,y,xy), add0(xy,z,xyz), add0(y,z,yz).
add(xy,z,xyz) :- add0(x,yz,xyz), add0(y,z,yz), add0(x,y,xy).

add(@findNode(x),@findNode(y),@findNode(z)) :- add(x,y,z), (true; dirty(x) ; dirty(y)).
dirty(@unionNodes(z,z1)), dirty(z), dirty(z1) :- add(x,y,z), add(x,y,z1), z1 != z, (true; dirty(x) ; dirty(y)).
// Wait what. Getting rid of the dirty iter number still works?

//add1 is a least canonicalized, if perhaps impartially congruenced.
add1(@findNode(x),@findNode(y),@findNode(z)) :- add(x,y,z).

.output add1(filename="add0.facts")
.printsize add1
```

Runner script:
```bash
rm add0.facts
for i in {0..10}
do
souffle add_uf.dl -j 4
done
```

The small unionfind shim to attach to souffle's unionfind impl.
```c++
#include <cstdint>
#include "souffle/CompiledSouffle.h"
#include "souffle/datastructure/UnionFind.h"

extern "C"
{

    souffle::SparseDisjointSet<int32_t> ds = souffle::SparseDisjointSet<int32_t>();

    int32_t unionNodes(int32_t x, int32_t y)
    {
        ds.unionNodes(x, y);
        return ds.findNode(y);
    }
    int32_t findNode(int32_t x)
    {
        return ds.findNode(x);
    }
}
```

```make
all: add_uf rebuild libunionfind.so

add_uf: add_uf5.dl libunionfind.so
	souffle-compile.py -l unionfind -L . add_uf.cpp
	souffle -g add_uf add_uf5.dl -j 8

rebuild: rebuild2.dl libunionfind.so
	souffle -g rebuild rebuild2.dl -j 8
	souffle-compile.py -l unionfind -L . rebuild.cpp

libunionfind.so: unionlib.cpp
	/usr/bin/c++ -march=native -fopenmp -O3 -DUSE_NCURSES -DUSE_LIBZ -DUSE_SQLITE -fopenmp \
		-std=c++17 -o unionlib.o -c -fPIC unionlib.cpp \
		-I../../souffle/build/src/../include -I../../souffle/build/src/include \
		-I../../souffle/build/src/../include/souffle/swig -I../../souffle/build/src/include/souffle/swig \
		-I/home/philip/Documents/prolog/souffle/src/include
	g++ -shared -o libunionfind.so unionlib.o 

```

You can also run in Souffle's compiled mode which gives a 2-4x speedup in my experience.

```
rm add0.facts
make
for i in {0..8}
do
# give LD_LIBRARY_PATH the path to libunionfind.so
LD_LIBRARY_PATH=. ./add_uf -j 4
done
```

## Bits and Bobbles
Thanks to Yihong, Remy, Max, and Zach, whose ideas are interspersed throughout here.

Souffle already supports an eqrel union find backed equivalence relation. The problem with it is it does not support the findRoot operation. Perhaps if there was a way to expose this to surface souffle, all would be well.
It is also not quite desirable to have seminaive semantics for the eqrel. This means findRoot might be slightly stale. It is absolutely key in my experience so far to never choke yourself with stupidly stale ids.
Maybe the eqrel could also have an associated dirty relation? This is in some sense `delta_eq` which already exists under the hood? `eq(x,x)` could play the role of dirty?

Here is just spitballing some plausible syntax.

```
.decl myeq(x : number, y : number) eqrel
foo(myeq.find(3)).
```

# Addendum: 6/20/22
Actually subsumption based union find works good too. This maintains a root relation that relates an eclass id to the minimum id in it's equivalence class. This is faster and requires no external library. The essential point seems to be the external fixed point and careful stratification.

```souffle
.decl add0(x:number, y : number, z : number)
.decl add(x:number, y : number, z : number)
.decl add1(x : number, y : number, z : number)
.decl maxid0(x : number)
.decl id0(x : number)
.decl root(x : number, y : number)

// should go in separate file

add0(1,2,12).
add0(12,3,123).
add0(123,4,1234).
add0(1234,5,12345).
add0(12345,6,123456).
add0(123456,7,1234567).
add0(1234567,8,12345678).
add0(12345678,9,123456789).
//add0(123456789,10,12345678910).
//add0(12345678910,11,1234567891011).

.input add0

// calculate fresh id offset
id0(x) :- add0(x,_,_).
id0(y) :- add0(_,y,_).
id0(z) :- add0(_,_,z).

maxid0(x) :- x = 1 + max t : id0(t).

// generate new ids needed for certain rules
add(y,z,autoinc() + mid) :- add0(_x,y,xy), add0(xy,z,_xyz), 0 = count : add0(y,z,_yz), maxid0(mid).
add(x,y,autoinc() + mid) :- add0(x,yz,_xyz), add0(y,_z,yz), 0 = count : add0(x,y,_xy), maxid0(mid).
add(x,y,z) :- add0(x,y,z).

// Ematch for rewrites
add(y,x,xy) :- add0(x,y,xy).
add(x,yz,xyz) :- add0(x,y,xy), add0(xy,z,xyz), add0(y,z,yz).
add(xy,z,xyz) :- add0(x,yz,xyz), add0(y,z,yz), add0(x,y,xy).

// Hmm. A little awkward I can't use add0?
root(x,x) :- add0(x,_,_).
root(y,y) :- add0(_,y,_).
root(z,z) :- add0(_,_,z).

add(x1,y1,z1) :- add(x,y,z), root(x,x1), root(y,y1), root(z,z1).
root(z,z1) :- add(x,y,z), add(x,y,z1), z1 < z.
// canonical element is minimum number in equiv class
root(x, y) <= root(x, y1) :- y1 <= y.

// way slower. Huh.
//add(x, y, z) <= add(x1, y1, z1) :- root(x,x1), root(y,y1), root(z,z1).

//add1 is projection of only roots
// allow through if not in union find at all also
add1(x,y,z) :- add(x,y,z), ((root(x,x) ; !root(x,_)), (root(y,y); !root(y,_)), (root(z,z) ; !root(z,_))).

/* 
alternatively include fresh ids in root
root(x,x) :- add(x,_,_).
root(y,y) :- add(_,y,_).
root(z,z) :- add(_,_,z).
add1(x,y,z) :- add(x,y,z), root(x,x), root(y,y), root(z,z).

*/

.output add1(filename="add0.facts")
.printsize add1
```
