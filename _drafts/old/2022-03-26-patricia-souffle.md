---
author: philzook58
date: 2020-12-06
layout: post
title: "Reifying sets with Patricia Tries"
---

There is something enticing about internalizing notions of sets or relations into datalog. As Cody said, going meta is the one move.

A simple approach is to use bitsets. We have integer data types available and bitwise operations over them. We can extend this outside of 32/64bit universes by using records of numbers. This representation is very good if we have a small universe of values we can talk about, but quite ungainly and inefficient if we don’t.

A key point is that we want a unique representation of the sets, and/or an unique identifier that we can associate to them. Bitsets do have this property.


Going beyond small universes there are couple options. Using the algebraic datatype facilities of Souffle seems like an enticing option. A very simple set data type is just a vector/array. For sparse small sets in large universes, this may even be the best data type. To make sure they are canonical we could enforce that they must be sorted. We could approach this via either using a linked list adt, by encoding into a string, or possibly by abuse of the record system.

Finally a quite nice approach is that of Patricia tries. Patricia tries are a commonly used functional data structure for intsets. See for example the Haskell or ocaml libraries.
A trie is a data structure for storing sets of sequences or maps from sequences (we can make sets out of maps generally by ignoring or removing the storage field). We can consider integers as a sequence of bits. We then build a tree that branches based on the bits of the key. Patricia tries compress long common prefixes to avoid unnecessary node allocation and indirection, Patricia tries support fast versions of basically all set operations. Crucially, Patricia tries are canonical for the set they represent. Balanced search trees do not typically have this property, the order in which you add elements to the set creates a structurally different data structure.
There is a choice of how much to memoize the operations over the trie. It is a classic trade off of time vs space. I am tempted to use the C++ user defined function interface to implement the operations as functors. There are a couple downsides here.
Chasing “pointers” of soufflé adts is not that cheap
Adding extra compilation steps and a whole other very complicated language. There is some bit twiddling involved, and keeping track of whether soufflé is using 32 or 64 bits is a little worrying.
User defined generative functors aren’t a thing yet (?), so we can’t enumerate elements of the set without trickery. We might be able to do this using the tries size and the range generative functor, but then we need to store an extra size field in the trie and have a more  expensive than necessary indexing operation to produce subsequent elements because we can’t save where we left off.

implementing the functions as soufflé relations also has significant downside. We probably want a need based instantiation of these relations, which functors get us by default. There is an almost sinful amount of data duplication. The trie itself of course holds its elements and also achieves significant sharing between related tries whereas an elem(trie, x) relation will duplicate the entire trie as an internal soufflé btree.
However, we stay in a much safer language, don’t have to worry , and it is possible that caching these operations is beneficial to speed.

Datalog is bottom up and prolog is top down. In a sense datalog feels “push” and prolog feels “pull”. These viewpoints can be translated to some degree to each other. Prolog can gain some benefits of datalog via tabling, which is a memoization technique. Likewise datalog can become goal driven via the “magic set transformation”, The following is a simplified but intuitive presentation I believe of the vague idea.

Relations in prolog can be used in different [modes](https://www.swi-prolog.org/pldoc/man?section=modes) (this is prolog terminology btw. An interesting concept). It’s part of the beauty of prolog that relations are sometimes reversible or generative if written to be so. Sometimes prolog programs are written to only behave correctly if used as if they were essentially a function.
If you find yourself needing what is essentially a function call on a relation, you can define “need” relation for that relation that takes the arguments. Then the regular clauses producing that relation also take the need relation to push in the actually needed instantiations of the clause. Here is an example for factorial. We examine the body of fact to see that we need the recursive call evaluated in order to evaluate.

```souffle
.decl needfact(n : unsigned)
needfact(n-1) :- needfact(n), n > 0,

.decl fact(n : unsigned, m : unsigned) choice-doamin
```

We have the expense of the extra table but we have gained pull based evaluation. Bottom up evaluation of fact would not terminate without an a priori bound on the argument. We could use subsumption to reduce the size of this table in this case.
Choice domain may present an optimization. It is marking the relation as functional in character, which in principle could allow soufflé to use an optimized data structure. I hope it makes things faster and doesn’t just add an unnecessary check. 

Because soufflé has ubiquitous interning/ hash consing almost anything can be identified and looked up from a unique integer. Hence, With an intset data structure, we can store other data types as well.
We can also use them to store relations if we consider the intset of a records containing the relations fields.


Reifying contexts as sets for Harrop clauses. Making fresh variables is not good for datalog. We want a reason for them to be fresh. Adts give us this ability. What is reason for forall variable? Clause that made it? Program context that made it? Are some program contexts equivalent.?
De bruin for free cars, var maps for bound bars. We can store free var as a list then. We need to traverse this list every time we go up? That sucks. Truly global vars also as a separate construct. 
Linked list with specialized cases. Unroll up to n=4 let’s say. reasonable. Mix of the bounded vn and linked list.
This is a disaster for rewriting. But no one has a good solution for that. Max is probably right about extract and normalize.
We need the term and varmaps defactored.
Meta interpreter. Fact, clause, database. Use intset for relations? Maaaaybe. Doesn’t seem necessary.
Use zipper of list to run through each clause. Relations need to hold lists of values as rows.
Rels(name, row).

Need universal type also.
If we want to keep separate multiple soufflé runs, we do need internalized set.



Subsumption rewriting in soufflé is interesting. Many things do have a canonizing rewrite system. Polynomials. Sorted lists.

Polynomial is int trie of powers to coefficients.
Linear term is symbol to int trie of coefficients. That floats aren’t associative sucks.






Bddbddbd. What aboud BDDs internalized as souffle adts.


A set of sets.
Union find is a set of disjoint sets.
We need contextualized union find in order to emulate prolog's union find.

state(goal, x, y)

.type Field = Var {n : symbol} | Lit {x : number} // and other cases
.type FieldList = [ hd : Field ; rest : FieldList ]
.type Pattern = [ name : symbol,  fields : FieldList ]
.type Goal = And { x : Pattern, xs : Goal } | Done {}

Goal is also body of clause

.type Head <: Pattern

.type Clause = [head : Head, body : Goal]


query(query).
state(q, ? ) :- query(q).
answer(s) :- state(nil, s).

.type state = [goalstack, unionfind ]
Possibly we may consider 
[goalstack, varmap]
possibly we may consider
[goal, varmap]
context insensitivty is condered kind of good instead of bad.

eq(tag,x,y)
vs
uf(tag, uf) 
we don't need the tag anymore. uf is it's own tag.
We can share structure between multiple contexts.
eq(tag,x,y) can be reified.

This is super reminiscent of super compilation. Just sayin.
Could use substitions instead of union find? minikanren style?


eval(head,body) :- rule( head, body)
:- eval(head,nil, varmap)

How do lit1 and lit2 become unified?
```
node(Query, Child) :- node(Query, [Lit|Rest]),
rule(Lit, Body),
append(Body, Rest, Child).
```