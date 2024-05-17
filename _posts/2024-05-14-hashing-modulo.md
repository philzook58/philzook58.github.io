---
title: Hashing Modulo Theories
date: 2024-05-14
---

Hashing <https://en.wikipedia.org/wiki/Hash_function> is a scrambly function that turns a datastructure into an integer.

We anticipate that hash functions will have collisions. They have to. Good hash functions don't have collisions for keys likely to appear together.

It is "wrong" though if there is some notion of equality the hash function does not respect.

Consider for example `(4,8)` representing the fraction $\frac{4}{8}$. In our intended meaning this is "equal" to `(1,2)` aka $\frac{1}{2}$ , but if I use python's default hashing function, they will map to different integers

```python
print(hash((4,8))) # 2714140458487201590
print(hash((1,2))) # -3550055125485641917
```

More pragmatically, if I have some kind of AVL tree or red-black tree data structure representing a set or dictionary, the exact balancing is actually irrelevant internals. If I use an ordinary tree hashing algorithm on these, logically "identical" sets will map to different hashes, which is wrong. So what do you do?

Sets are useful in all sorts of ways, but in particular I the application I find most interesting is to hash sets that correspond to contexts in a automated theorem prover context (egglog, datalog, other).

Another example that I care about a lot is alpha invariant expressions. If the intended meaning of an expression is intended to be invariant to non-clashing renamings aka permutations of the variable labels. For example, `foo(X,Y,X) = foo(Z,W,Z) != foo(X,Y,Z)`. This shows up in theorem proving contexts.

There are at least 3 methods to fight this problem

- Canonization
- Hash homomorphisms into integers
- Invariants

# Canonization

Like the rational example, the obvious solution if it is available is to reduce your structure to a canonical form and then hash that. We should immediately reduce `(4,8)` to `(1,2)` and only store that caonnical version. The python built in `Fraction` is something like that.

```python
from fractions import Fraction
print(hash(Fraction(4,8))) # 1152921504606846976
print(hash(Fraction(1,2))) # 1152921504606846976
```

For sets, dictionarys, multisets, there are multiple options.

The obvious one is to sort the elements (or sort the hashes of the elements) of the set into a list. This list is canonical. Then you can use regular ordered list hashing.

```python
print(hash(tuple(sorted([3,4,5])))) # 4003026094496801395
print(hash(tuple(sorted([4,5,3])))) # 4003026094496801395
```

One nice thing to use for sets of sequences is a trie, which is a canonical tree that represents the set (This may kick the can a little since each internal node of the tree is also a dictionary). Integers can be considered a sequences of bits <https://en.wikipedia.org/wiki/Radix_tree>

Canonization is a simple method that works pretty well.

But, it can be expensive to keep recanonizing or it may not be obvious that you even can canonize.

I did something like this for first class sets in datalog here <https://www.philipzucker.com/contextual-datalog/>. I represented them using a list algerbaic datatypes that I wrote sorting routines for.

One way to create a canonical alpha equivalent term is to label the variables by a traversal order (pre-order, post-order). This isn't perfect because you need to possibly rename every time you plug a term in. Maybe there is some smart traversal?

For a general equational theory, you might orient it's equations into rules and complete them to get a canonizing rewrite system. Then you can just hash these caononical forms. This is not always possible however.

# Homomorphisms

There is an analogy between the syntactic expressions for certain algebraic theories and data structures.

- A tree is like a binary operator with no relations.
- a list is the free monoid with appending as the binary operation. It is an associative binary operator. `(x + y) + z = x + (y + z)`
- a multiset is a commutative associative monoid.
- a set is an [idempotent](https://en.wikipedia.org/wiki/Idempotence) associative commutative monoid.  `x+x=x`
- a tree with unordered children is like a commutative operator without associativity. This kind of thing shows up in finite set theory where there are sets of sets of sets. <https://www.philipzucker.com/finiteset/>

See also the Boom hierarchy <https://link.springer.com/chapter/10.1007/978-1-4471-3236-3_1>

One way to build a hash function is to find a homomorphism from these theories into the integers. In order words, some kind of integer operator that respects the symmettries of the datastructure.

One example of such things is `xor`, `or`, `and` on your integers. This way lies [bloom filters](https://en.wikipedia.org/wiki/Bloom_filter).

# Invariants / Fingerprints

A different approach is to try and invent some invariants that respect the undelrying symetries of your structure. These invariants do not have to completely describe the original structure ,but they may tend to resolve collisions well enough. There is a tradeoff of the cost of canonicalization/invariant calculation to the cost of a bad hash collision.

Note that `hash(x) = 42` isn't "wrong" in the sense that collisions are allowed, but it is very wrong in intent. This will cause very bad collisions and ruin any sort of performance guarantees you hoped to achieve with hashing.

An invariant of a set or multiset would be it's size for example.

You can produce an invariant tree from an alpha renameable tree by replacing every `X` or `Y` with a token `var`. Under this scheme `foo(X,X)` will have `foo(var,var)` as it's invariant, but also `foo(X,Y)` has the same invariant. You could interpret this as either a term with all variables identified or all variables considered unique.

Another invariant/fingerprint is the multiset of variable counts of the expression. For example `foo(X,X,Y,Y,Z)` would have the multiplicity count multiset `{2,2,1}` which you can then hash via multiset hashing.

Any of the above "homomorphism hashes" or canonical structure is also an invariant, but I find I tend to think of different things when I'm seeking invariants rather than seeking homomorphisms or canonical forms. Homomorphisms and invariants can be lossy, but the canonicalization approach is a bit more exact (One you hash the canonical structure, you aren't exact for the usual collision reasons.).

Fingerprints can also be useful for range queries where perhaps you are looking for all sets of size at least 7.

<https://link.springer.com/chapter/10.1007/978-3-642-31365-3_37> Fingerprint Indexing for Paramodulation and Rewriting - Schulz

# Bits and Bobbles

I think there is a distinction of  Hashing modulo alpha as you might find in prolog or a resolution prover compared to
Hash modulo scoped alpha <https://arxiv.org/abs/2105.02856> where you want your alpha renameable things scope. That's a whole other can of worms. I think unscoped modulo alpha might be easier.
<https://pvk.ca/Blog/2022/12/29/fixing-hashing-modulo-alpha-equivalence/>
<https://arxiv.org/abs/2401.02948>  Hashing Modulo Context-Sensitive α-Equivalence - very interesting.

Co-debruijn, upon which the technique in the paper above is based, makes a canonical tree form for lambda terms by making a little tree map from the position the variable is bound to wehre it is used. That's smart. <https://arxiv.org/pdf/1807.04085> <https://jesper.sikanda.be/posts/1001-syntax-representations.html>

I'm cribbing on the name "Satisfiability Modulo Theories" for the title of this post. Hash Modulo Alpha is something that has been published and discussed, but I think this is kind of a part of a more general concept of hashing which respecting interesting notions of equality.

<https://www.preprints.org/manuscript/201710.0192/v1/download>   Ricard O’Keefe How to Hash a Set.

Graph hashing is OP. You can map hashing modulo alpha into graphs by making `var` nodes for every variables. It fits into the above framework.

- nauty <https://pallini.di.uniroma1.it/> can canonize graphs by adding canonical labels
- <https://networkx.org/documentation/stable/reference/algorithms/graph_hashing.html> Simpler things kind of take the invariant fingerprint approach. You can make a fingerprint of every vertices neighborhood and then combine them using a set-like hashing procedure.
- <https://arxiv.org/pdf/2002.06653> Caleb has great points in his Directed graph Hashing Paper. Perhaps useful for Unison?
- <https://static.googleusercontent.com/media/research.google.com/en//pubs/archive/37599.pdf>

- <https://www.philipzucker.com/relational-ac-matching/> Here I used graph matching to achieve associative commutative matching. This is also kind of what relational ematching does. Graph matching is OP. Graph matching is a database query anyhow. It's actually not that bad if your patterns are small despite the aura of NP that floats around it. SQLite/DuckDB/datalog is a good graph matching engine you already have today. queries are patterns, tables of edges are the graph.

<https://stackoverflow.com/questions/20832279/python-frozenset-hashing-algorithm-implementation>  python frozenset rules. It's a built in hashable/hasconsable set data structure.
I used this quite a bit making nested hash consable sets here <https://www.philipzucker.com/finiteset/>

Depth first labelling. Non compositional. There might be some smart traversal that fixes this.

- See Term Indexing in Handbook of automated reasoning <https://dl.acm.org/doi/10.5555/778522.778535>
- Variant / subsumption tabling in prolog <https://www.swi-prolog.org/pldoc/man?section=tabling-subsumptive>

More Boom hierarchy
<https://www.cl.cam.ac.uk/events/owls/slides/maaike.pdf>
<https://www.youtube.com/watch?v=kGDSPxXtKdg>

In a dependent type theory kind of context, this all gets kind of funky. If it is undecidable to determine if there is a proof two things are even equal what can you do then?

We are somewhat used to having an issue that some datatypes do not implement Order typeclasses or interfaces. Or perhaps they are only partially ordered. That's another fun twist.

We can also consider the semidecidable equality case.

Also in egglog, this is all funky. A set of things in egglog only has a bound on its size because things inside the set may be equated later.

Automata minimization is the analog of coinductive hash consning. You need to seal the automata off / forget some observations. Monotonically forgetting observations monotonically compresses automata.

Hashing modulo beta is interesting. Canonization is assured sort of with the appropriate type system with strong normalization. The type indeed is an invariant of a reducing expression. What other kinds of invariants exist modulo beta reduction? Beta reduction won't produce new uninterpreted symbols, but it can remove them. The "worst" type inside the term may be going down (Cody mentioned something from some girard book).

Clarke, D.E., Devadas, S., Dijk, M., Gassend, B., Suh, G.E.: Incremental multiset hash functions and their application to memory integrity checking.

Suppose you wanted to hash a dag. Hashconsing unifies all dags or trees to the minimal dag. But what if you want to separately identify different dags. Kind of an alpha invariant term is a dag where Var nodes can be identified/compressed or not. Everything else should be maximally shared.
<https://stackoverflow.com/questions/14532164/hash-value-for-directed-acyclic-graph> hmm there is reason to believe that isomorphism between dags is hard. Still one (I) suspects there may be a very effective algorithm of some kind.
<https://en.wikipedia.org/wiki/Graph_isomorphism_problem#GI-complete_classes_of_graphs> Oh but is this for unordered children?

sets = absorptive monoid
multisets = commutative monoid
lists = monoid
tree

Lattice data structures.
Multisets of incomparable elements, we ought to be able to tune between having a total order and a partial order.
The more total the order is, the better we can do.
Equality
partially ordered <https://doc.rust-lang.org/std/cmp/trait.PartialOrd.html>
total ordered

Maybe a set of chains of some kind

Hash cons modulo theories
Hash Cons modulo symmetry

There is material on how to perform hashing in terms of how to take a range of integers and deterministically map it in a scrambled way into a smaller range. By the nature of functions, if two objects map to different hashes they must not be equal. `f(x) != f(y) -> x != y` no matter what the definition of `f` is. We cannot conclude anything if two objects map to the same value (a hash collision) and a further test must be made.

There are some interesting questions that come up when you want to hash data structures or mathematical objects. How do you take these things to an integer in the first place?

The simplest case is hashing of tuples and ordered trees (like typical ASTs). This doesn't seem that bad.

But in other data structures there are representational redundancies or equations that might hold. How do you hash these things that have a notion of equality beyond that of structural equality?

A common example is typical dictionary data structures like red-black trees. The order you put keys into these trees changes their exact balancing. To put this in more mathematical terms, how do we make hashes for finite maps. A related question is how do we make hashes for sets?

There are alternative formulations of sets. Tries are one example, for example patricia tries. These data structures are canonical for the set or map they represent and hence you can use regular tree hashing techinques.

If you have a normalization procedure that can

Another example which really inspired this post is the question of how to hash a tree that has a notion of alpha equivalence (where names of variables don't really matter). Examples of these things are lambda binders, summation symbol indices, the dummy variable name for an integral, etc. [Hashing Modulo Alpha-Equivalence](https://arxiv.org/abs/2105.02856) presents a scheme for doing this.

egraphs in a sense are an answer to how can you hash modulo an equational theory with no good properties. It keeps refining and fixing up your hash dynamically

Lambda syntax requires variables to also be scoped. This may be a separate concern.

de Bruijn indices is famously a canonical representation of closed lambda terms. Why is this not a solution to the problem?

##

actually making a term with alpha equality. Not hashing, but interesting I think.

```python
from dataclasses import dataclass
from typing import Any
@dataclass(frozen=True)
class Term():
    pass
@dataclass(frozen=True)
class Fn(Term):
    name: str
    args: tuple[Any, ...] = ()
    def __repr__(self):
        if len(self.args) == 0:
            return self.name
        return f"{self.name}({', '.join(map(repr, self.args))})"
    def __eq__(self, other, perm=[]):
        if not isinstance(other, Fn) or self.name != other.name or len(self.args) != len(other.args):
            return False
        for x,y in zip(self.args, other.args):
            if not x.__eq__(y,perm):
                return False
        return True

    
@dataclass(frozen=True)
class Var(Term):
    name: str
    def __repr__(self):
        return "?" + self.name
    def __eq__(self, other, perm=[]):
        if not isinstance(other, Var):
            return False
        for x,y in perm:
            if x == self.name:
                return y == other.name
            if y == other.name:
                return x == self.name
        perm.append((self.name, other.name))
        return True
    def __hash__(self):
        # The name is not alpha invariant so can't naively be part of the hash
        return 19

def f(x):
    return Fn("f", (x,))
def bar(x,y):
    return Fn("bar", (x,y))
x,y,z = map(Var, "xyz")

print(f"{f(x) == f(f(x))=}")
print(f"{f(x) == f(y)=}")
print(f"{bar(x,y) == bar(x,x)=}")
print(f"{bar(x,x) == bar(y,y)=}")

print(f"{hash(bar(x,y))=} {hash(bar(x,y))=}")

print(f"{set([ bar(x,x), bar(y,y), bar(y,x), bar(x,y) ])=}")
```

## draft

It is useful to consider invariants of the equivalence class of structures. One invariant is the tree derived by replacing every variable with the same marker. An invariant from `("foo", ("var", 0), ("var", 1))` is `("foo", "marker", "marker")`
Another invariant is the number of variables, the set of counts of variables, or the confusion size.
The variable breadcrumb trick in co de Bruijn notation is very clever. A set of multicontexts. There is redundant information here.

These are all special cases of graph hashing. That is not to say that you want to reach for the big hammer of graph hashing, since it might be very difficult to do.

Hashing and Hash consing are related but distinct concerns. Hash consing is also called interning in some contexts. See for example [`sys.intern`](https://docs.python.org/3/library/sys.html#sys.intern) in the python standard library.

If you only use interned data, you can replace structural equality `==` with physical equality `is`, since every equal thing is literally the same object in memory. This is much faster, especially when you consider structural equality may require traversing some big tree.

False positive and false negatives

Definitely equal,
Definitely not equal,

Structural equality
Physical equality

Big integers, arbitrarily large integers often

### Canonization

One technique to
Binary search trees
Tries
Patricia trie in souffle

Hashing Sets

Hashing graphs

Homomorphisms and hash functions

Fingerprinting and invariants.

Fast paths
Structural Equality.

Hash Consing

Replacing varables with generaic var. Does this represent a tree of all equal variables or tree of all different

Unique Enumeration

Variable maps

```python


```

Resources:

- Handbook of automated reasoning
- Vector fingerprint eprover paper
- Hash cons modulo alpha, criticism by paul.
- Richard O-Keefe paper
- Python hashing of frozensets

```python

_mytable = {}
interned_ids = set()

def intern(x):
    if isinstance(x,tuple):
        #x = tuple( intern(y) for y in x )
        key = tuple(id(y) if id(y) in interned_ids else id(intern(y)) for y in x) # don't recursively intern
    elif isinstance(x,str) or isinstance(x,int):
        key = x
    else:
        assert False, f"not internable {x}"
    x1 = _mytable.get(key)
    if x1 is not None:
        return x1
    else:
        _mytable[key] = x
        interned_ids.add(id(x))
        return x

def fast_equals(x,y): #"fast"
    x = intern(x)
    y = intern(y)
    return x is y
    
print(intern( (1,2,(3,4)) ) is intern( (1,2,(3,4)) ))
print(id(intern((1,2,3))))
print(_mytable)
```

## Old draft - Reifying sets with Patricia Tries - 2020-12-06

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
