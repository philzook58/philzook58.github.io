---
author: Phillip Zucker
date: 2021-05-09
layout: post
title: Encoding E-graphs to Souffle Datalog
---


Yihong Zhang had a really interesting twist on how to look at egraph and egraph matching. <http://effect.systems/doc/relational.pdf> <https://github.com/egraphs-good/egg/pull/74>

Datalog is a specification language of relations. <https://en.wikipedia.org/wiki/Datalog> It is similar in some respects to SQL.
[Souffle Datalog](https://souffle-lang.github.io/) is an implementation in C++ geared especially towards program analysis needs. A nice intro here <https://www.stephendiehl.com/posts/exotic04.html>

Datalog differs from prolog in a number of ways
1. it only allows atomic terms like `a` rather that `cons(a,nil)`.
2. It tends to be evaluated bottom up rather than top down. Because of this, things that are bad prolog because they would lead to infinite loops are fine in datalog.
3. It tends to eschew the extralogical constructs in prolog like cuts
4. negation is not allowed in full generality. If you think about how datalog is building up it's tables, teh required rules actually kind of make sense 

A cute aspect of datalog is that it has a fairly straightforward operational reading. For example

```r(X,Z) :- a(X,Y), b(Y,Z)```

The naivest way of storing a relation is as an array of tuples. This line of datalog could compile into the follow `for` loop.

```julia
for (x,y) in a
    for (y1,z) in b
        if y == y1
            push!(r, (x,y))
        end
    end
end
```

Then running a datalog program is running all the loops described by each clause in the program until no new tuples are found. The limitations of datalog compared to prolog guarantee this saturation process does terminate.
An actual good datalog implementation should go about things smarter, using good indexing data structures, reordering the pieces of the clauses, and using better evaluation strategies than the maximally naive one. In addition, you can topologically order the dependencies of the relations on each other. Then you can completely finish some relations before you start on others. This is the origin of the stratified negation rules.


An Egraph is a kind of bipartite graph between enodes and equivalence classes. It in a sense holds a bag of terms that are related by equalities. I've written more about them in the past.
- <https://www.philipzucker.com/egraph-1/>
- <https://www.philipzucker.com/egraph-2/>
- <https://www.philipzucker.com/a-simplified-egraph/>

As a general technique in logic, tree-like terms can be flattened if you introduce new symbols. This is a useful simplification in many places, for example the ANF intermediate representation in a compiler, or as a virtual machine compilation of a prolog query. Assembly is also a bit like this, as the operands of individual assembly instructions are basically registers, memory locations, and constants.

It makes intuitive sense that congruence closure can be encoded into datalog. Simple fixed point calculations sort of tend to be able to be expressed in this way.

The encoding of a congruence closure problem to datalog can go like so:

1. Flatten terms introducing new names for each new eclass
2. Make an n+1 arity relation for each n arity function symbol. For example, the function plus(x,y) becomes plus(x,y,result)
3. Make an equivalence relation `equiv` for the eclasses. You can explicitly write out the axioms 
```
.decl equivalence(x:number, y:number)
equivalence(a, a) :- equivalence(a, _).     // reflexivity
equivalence(a, b) :- equivalence(b, a).     // symmetry
equivalence(a, c) :- equivalence(a, b), equivalence(b, c).  // transitivity
```

Souffle datalog actually has special support for this backed by a union find data structure  <https://souffle-lang.github.io/relations#equivalence-relations> <https://doi.org/10.1109/PACT.2019.00015>

4. Assert the existence of every piece of every expression you want to talk about
5. Write down congruence closure axioms for every function symbol.

Here's an example.


Given
```
f(f(f(a))) = a
f(f(f(f(f(a))))) = a
```

Does `f(a) = a`?

And here is a datalog program to encode this.

```
.decl a(n: number)
.decl f(n: number, m: number)
.decl label(n: number, m : symbol)
// This is merely initializing the graph
a(0).
f(1, 0).
f(2, 1).
f(3, 2).
f(4, 3).
f(5, 4).

label(0, "a").
label(1, "f(a)").
label(2, "f(f(a))").
label(3, "f(f(f(a)))").
label(4, "f(f(f(f(a))))").
label(5, "f(f(f(f(f(a))))))").

.decl equiv(n: number, m : number) eqrel
equiv(3,0). // f(f(f(a))) = a
equiv(5,0). // f(f(f(f(f(a))))) = a

// congruence closure for f
equiv(A, A0) :- f(A, B), equiv(B, B0), f(A0, B0).

.decl equivl(l : symbol, l1 : symbol) eqrel
equivl(l, l1) :- equiv(A,B), label(A,l), label(B,l1).
.output equivl
```

Run with `souffle -D - egraph2.dl` to get output

```
---------------
equivl
l       l1
===============
a       a
a       f(f(f(a)))
a       f(f(f(f(f(a))))))
a       f(a)
a       f(f(f(f(a))))
a       f(f(a))
f(f(f(a)))      a
f(f(f(a)))      f(f(f(a)))
f(f(f(a)))      f(f(f(f(f(a))))))
f(f(f(a)))      f(a)
f(f(f(a)))      f(f(f(f(a))))
f(f(f(a)))      f(f(a))
f(f(f(f(f(a))))))       a
f(f(f(f(f(a))))))       f(f(f(a)))
f(f(f(f(f(a))))))       f(f(f(f(f(a))))))
f(f(f(f(f(a))))))       f(a)
f(f(f(f(f(a))))))       f(f(f(f(a))))
f(f(f(f(f(a))))))       f(f(a))
f(a)    a
f(a)    f(f(f(a)))
f(a)    f(f(f(f(f(a))))))
f(a)    f(a)
f(a)    f(f(f(f(a))))
f(a)    f(f(a))
f(f(f(f(a))))   a
f(f(f(f(a))))   f(f(f(a)))
f(f(f(f(a))))   f(f(f(f(f(a))))))
f(f(f(f(a))))   f(a)
f(f(f(f(a))))   f(f(f(f(a))))
f(f(f(f(a))))   f(f(a))
f(f(a)) a
f(f(a)) f(f(f(a)))
f(f(a)) f(f(f(f(f(a))))))
f(f(a)) f(a)
f(f(a)) f(f(f(f(a))))
f(f(a)) f(f(a))
===============
```

We do indeed see the line `f(a)    a` in there.

Now, this a a very generic table based approach and definitely gets the pants slapped off it by an actual egraph implementaion.

Two points there though:
1. This demonstrates that the language of datalog or prolog might be a good input language to an egraph solver
2. There is the possibility that rearranging this program or using some of Souffles stranger features or coming up with some other extra datalog feature you could get the table based approach to be more efficient.

Alessandro has run some experiments using a table based representation of the egraph data structure and he did not come away impressed. Fair enough.


### Finding Pattern Instantiation in Datalog

A second piece of the egraph story is the ematching algorithm. Yihong reports that a table based approach here exhibits extreme speedups compared to even a somewhat refined virtual machine based top down search.

The recipe is

1. For each pattern, make a predicate holding the instantiable vairables. `pat1(A,B,C)`
2. Assert the current egraph as a starting database.
2. Flatten the patterns and and make a claus for each with all the pieces appearing in the pattern in the right hand side.

The results of this query will be instantiations of the pattern variables, which via an external program you can instantiate and reassert into the egraph.

Here is a simple program and egraph that instantiates some commutative and associative patterns

```
.decl lit(n: number)
.decl plus(n: number, m: number, k : number)
.decl label(n: number, m : symbol)
// This is merely initializing the graph
lit(1).
lit(2).
lit(3).
label(1, "a").
label(2, "b").
label(3, "c").

plus(1,2,4).
label(4, "plus(a,b)").
plus(2,3,5).
label(5, "plus(b,c)").
plus(1,3,6).
label(6, "plus(a,c)").
plus(4,3,7).
label(7, "plus(plus(a,b),c)").


.decl comm_pat(a:number, b:number)
comm_pat(a,b) :- plus(a,b,_).

// pattern plus(a,plus(b,c))
.decl assoc_pat1(a:number, b:number, c:number)
assoc_pat1(a,b,c) :- plus(a,x,_), plus(b,c,x).

//pattern plus(plus(a,b),c)
.decl assoc_pat2(a:number, b:number, c:number)
assoc_pat2(a,b,c) :- plus(x,c,_), plus(a,b,x).

.output assoc_pat2
.output assoc_pat1
.output comm_pat
```

Results:
```
---------------
comm_pat
a       b
===============
1       2
1       3
2       3
4       3
===============
---------------
assoc_pat1
a       b       c
===============
===============
---------------
assoc_pat2
a       b       c
===============
1       2       3
===============
```

This datalog representation of patterns does not present difficulties to some very useful extensions of pattern matching: Multipatterns and Guards. Also this does not have to be in pure rewrite mode. Whatever you choose to do with the pattern instantiation is the job of the next stage of code.

Datalog seems like a reasonable way to approach having programmable ematching search.

### Bits and Bobbles

What I think this demonstrates more than anything is that Datalog is a very good candidate for a specification language for egraph solvers. Datalog or some variant of it seems like a somewhat natural way to express operations on the egraph. Some changes may be necessary. 

It seems like for a user, they should not have to hand flatten their terms. This shows once again that it isn't really about trees vs atomic symbols that makes prolog vs datalog or term rewriting vs string rewriting. It is about whether you allow pattern variables / unification variables interior to the trees or not. Grounded term trees are basically the same thing as atoms or strings.

Can these two above pieces be fit together in pure datalog? Probably not. The actual instantiation of the right hand side of patterns requires the generation of new eclasses. This also destroys the termination guarantee of datalog. 
I note that Souffle does have some unusual features that may make this possible though. `$` is used to generate unique random values to populate a table. It should be used with care as it may result in stepping outside the standard Datalog semantics.
<https://souffle-lang.github.io/arithmetic>
Another feature of Souffle that might do something useful is <https://souffle-lang.github.io/choice> This might help avoid how unnecessarily verbose the datalog representation is being

<https://souffle-lang.github.io/provenance> Souffle has an explain feature. This is proof producing congruence closure

There is an interesting analogy put forward by Alessandro that the egraph itself is a kind of database. One can consider that the mere existence of a term being in the egraph as the statement of the term's truth. The egraph database contains one very special relation `=` which one is not necessarily required to make use of. Then rules themselves are kind of a datalog run. The current egraph implementations are kind of oriented around rewrite rules and are not careful about what is inserted into the egraph or not. They are more careful about what is asserted as equal or not.

An alternative to this perspective is to create a special node in the egraph called `true` and then any relation that is in the same eclass as this node has been proven somehow.
There is something of a intuitionist flavor to this perspective in my mind. Note that we can have both `true` and `false` nodes and it is not required that every pattern eventually fall into each, hence in some sense the law of excluded middle does not hold. Things are not platonically true or false, instead they are proved true, proved false, and unknown.

An online datalog system could stream out pattern instantiations and ingest new equalities

Are datalog evaluation techniques applicable here.
Seminaive evaluation is a fairly simple but powerful idea of avoiding looking at things twice. Could this be a way to avoid multiple redundant pattern instantiations, only looking at new info?


Integrating egraphs into datalog might be a way to a way to nicely integrate them with other static analysis for program optimization. See <https://www.cs.cornell.edu/~ross/publications/eqsat/>


Prolog and Datalog have a special predicate `=` expressing unification. Could we not have a special predicate = which expresses egraph joining when it appears in the head of the clause and eclass guards or searches when in the clause? 



Analyses. Datalog seems compatible with lattices although I don't think it is supported in Souffle all that well
For analysis that are a lattice that is finite sets under union. This works although is not efficient for maximum also. You can easily enough reconstruct the maximum posthoc https://souffle-lang.github.io/aggregates.
```
analysis(i,max(a,b)) :- analysis(j,a), analysis(k,b), f(j,k,i).
analysis(i,a) :- equiv(i,j), analysis(i,b).
```



