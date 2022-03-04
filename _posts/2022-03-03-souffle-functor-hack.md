---
date: 2022-03-03
layout: post
title: "A Questionable Idea: Hacking findParent into Souffle with User Defined Functors"
tags: egraph
---

Souffle supports an equivalence class relation backed by a union find data structure. This is intriguing for possible usage in an egraph among other things. I've been sniffing around this idea and so has the Egg group (Remy, Yihong, Max, and Zach). This post is based upon their work with some bad ideas of my own thrown in. See their [POPL paper](https://www.mwillsey.com/papers/relational-ematching) and blog posts <https://www.philipzucker.com/datalog-egraph-deux/> <https://www.philipzucker.com/egraph-datalog/> for more in this vein.

What souffle doesn't support is a simple efficient way to get the canonical element of the union find. To some degree this operation might break the relation abstraction and datalog semantics badly.

But if you _do_ have such a thing, you can write a very simple looking subsumption clause to delete stale elements.

```
add(x, y, z) <= add(FIND(x), FIND(y), FIND(z)) :- true.
```

And you can directly input the most canonical element currently known, hopefully avoiding inserting very stale non canonical elements.

```
// comm-add
eql(as(xy, number), as(yx, number)),
 // make sure to add canonical nodes
 add(FIND(x), FIND(y), FIND(xy)) :- add(y, x, yx),
 xy = $Add(x, y).
```

I thought I had a cute idea. What if one use the souffle [user defined functor](https://souffle-lang.github.io/functors) feature to backdoor into the native souffle equivalence relation or interact with an external union find library?

A nice sample problem is commutativity and reassociating an AExpr tree. Naively there are a lot of terms. The egraph significantly compresses this.
In the saturated egraph there should be
- $2^N - 1$ eclasses. This corresponds to all possible ways of picking a set of the N leaves minus 1 because there is no eclass for no leaves. Modulo associativity and commutativity, an AExpr tree corresponds to just it's set of leaves.
- The number of `add` enodes is $$\sum_{n=1}^{N} \sum_{k = 1}^{N - n} {N \choose n} {N - n \choose k} $$. Suppose I pick n leaves for the left child and k leaves to go in the right child. You can choose a set of n leaves  for the left child of `add` $$N \choose n $$ ways. You can then choose the right branch of `add` out of the remaining $$N - n$$ remaining leaves $$N - n \choose k $$ ways. Then sum over all possible values for $$n$$ and $$k$$. Wolfram alpha says this is $-2^{N} + 3^{N} + 1$ which perhaps there is a way to see this directly.

These numbers matter, because it was difficult to get this hacked souffle program to actually saturate to the right number of things. I think soundness of the equality saturation process is still ok. If souffle says two terms are equal, they really are. Completeness is highly questionable though. If souffle thinks it has saturated the egraph, it may not actually have.

You can find Remy's encoding of an initial approach that hacked the Souffle generated C++ code [here](https://github.com/remysucre/egg.dl). What this did is replace the dynamic linking mechanism of souffle with an include file that contained _macros_ defining the user defined functor `eqfind`.

```
#define eqfind(x) rel_1_myeq->ind.findNode(x)
```
 In this way, one could get access to the actual souffle equivalence relation `rel_1_myeq` (the macros are important because the `rel_1_myeq` isn't even in scope outside of the file). You can find my notes on this hack [here](https://gist.github.com/philzook58/b3e8f8ad5d465b384da8474eea841e34) This also required threading the `findNode` function up through the EquivalenceRelation class in souffle itself.

A second version [here](https://gist.github.com/philzook58/428c313f6e23672ba0b05110d254f225) instead made a global variable containing a souffle `SparseDisjointSet`. This is a bit less hacky and you don't need to edit C++ code (regular dynamic linking works fine) and can use stock souffle. The idea was that one problem with the previous encoding is that 

```
eql(as(xy, number), as(yx, number)),
 add(FIND(x), FIND(y), FIND(xy)) :- add(y, x, yx),
 xy = $Add(x, y).
```

actually is in souffle's eye's is equivalent to

```
eql(as(xy, number), as(yx, number)) :-  add(y, x, yx), xy = $Add(x, y).
add(FIND(x), FIND(y), FIND(xy)) :- add(y, x, yx), xy = $Add(x, y).
```

This is very different from out perspective though, since now yx and xy are not merged in the second rule and hence more stale terms are generated. If we rely on the functional dependence of user defined functor for operation ordering we can instead write

```
add(UFIND(xy, yx, x), FIND(y), FIND(xy)) :- add(y, x, yx),
 xy = $Add(FIND(x), FIND(y)).
```

where `UFIND` unions the first two arguments and returns the FIND of the third. Now Souffle can't decouple these rules.


```c++
#include <cstdint>
#include "souffle/CompiledSouffle.h"
#include "souffle/datastructure/UnionFind.h"
extern "C" {
    souffle::SparseDisjointSet<int32_t> ds = souffle::SparseDisjointSet<int32_t>(); 

    int32_t unionNodes(int32_t x, int32_t y){
        ds.unionNodes(x,y);
        return 0;
    }
    int32_t findNode(int32_t x){
        return ds.findNode(x);
    }
    int32_t constfind(int32_t x, int32_t y){
        return ds.findNode(y);
    }
}
```

And then you can use these functors in the souffle program like so

```
#define NUM(x) as(x, number)
#define FIND(x) as(@findNode(NUM(x)), Id)
#define UFIND(x,y,z) as(@constfind(@unionNodes(NUM(x), NUM(y)), NUM(z)), Id)
.functor findNode(number):number 
.functor constfind(number,number):number // find second argument, ignores first
.functor unionNodes(number,number):number // performs union, returns 0
.type Id = Add {x : Id, y : Id}
         | Num {n : number}
```

I don't really know how to do better than this encoding and I'm confused why it isn't working that well. It is orders of magnitude slower that egg, even compiled and parallelized. I am also very confused on why seemingly innocuous changes to the rules make a huge difference in terms of completeness and runtime. My best guess at the moment is that I'm fighting souffle's scheduling of rules.

# Thoughts
- The contract with Souffle is that user defined functions are to be pure. `eqfind` definitely is not, returning different but consistent results at different points of the execution
- Semi naive evaluation of the first encoding means that the latest additions to `eq` are not available. This makes unneccesarily stale terms that need to be cleaned up later by the subsumption mechanism. It is possible to also query the `new_eq` relation, but it isn't obvious to me how this relation is merged into the original, in otherwords which canonical elements win.
- Souffle has no idea that `eqfind` is dependent in any way upon `eq`, and doesn't schedule accordingly. This also messes up souffles stratification analysis. In the second encoding
- The naivest operational reading of datalog code is inaccurate. Multiple right hand sides are merely syntax sugar for completely separate rules. It is within souffle's rights to decouple these completely. What this means is that the adding to the union find is temporally very separate from adding new terms. these terms will therefore often be pretty stale with respect to the union find.
- It feels like somehow `$Add` and `add` getting out of sync with each other may be the problem.
- 
# Bits and Bobbles
User defined functors really could be used for some cool stuff. For example bitsets, or an external intern store that is keyed into by ints. This feature is so powerful and pretty easy to use once you give it a shot.
