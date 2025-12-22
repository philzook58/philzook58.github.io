---
title: An Inequality Union Find Inspired by Atomic Asymmetric Completion
date: 2025-12-22
---

Atomic asymmetric completion is a union find. Ground term asymmetric completion is a refinement egraph.

# Abstract Completion

Abstract [completion](https://en.wikipedia.org/wiki/Knuth%E2%80%93Bendix_completion_algorithm) is a generic brute force strategy for turning equations into good (convergent = confluent + terminating) rewrite rules.

For any kind of data structure or mathematical object with a notion of equality, matching and replacement (strings, terms, ground terms, atoms, [polynomials](https://en.wikipedia.org/wiki/Gr%C3%B6bner_basis), [groups](https://gap-packages.github.io/kbmag/doc/chap2.html), [traces](https://en.wikipedia.org/wiki/Trace_monoid), [multisets](https://www.philipzucker.com/multiset_rw/), graphs, term graphs, drags, combos thereof) the following makes sense of something you might try to do:

1. Define a well founded order on your thing (typically smaller, simpler, etc).
2. orient your unoriented equations to simplifying rules
3. Find all overlaps of two rule left hand sides, add those as new deduced equations
4. goto 2

Whether this battleplan is actually complete or terminating requires mathematical analysis (critical pair /diamond lemmas and other stuff), but it is obviously sound. A better version also reduces rules with respect to each other, but this also requires care to retain completeness.

# Asymettric Completion

[Asymmetric completion](https://www.iiia.csic.es/~levy/papers/jsc.pdf) is a shift on this strategy for things that aren't fundamentally bidirectional, reasoning about an inequality relationship `<=` (for examples subset relations, subtype relations, undefinedness, and refinement relations) with similar machinery as you do for a symmettric equality relationship `=`

# How does it work

The trick is you need two rewrite relations `R`, `S` rather than the single rewrite relation for equational theories.

Rather than orient an equation `a = b` to turn it into a rule `a -> b` or `b -> a`, you orient an inequality `a <= b` by by placing it into either `R` or `S` depending on whether it is increasing or decreasing.

In completion, no matter how we orient, it remains true that `E = (R U R^-1)*`. In asymettric completion `LE = (R U S)*`  since facts from `LE` just get placed in `R` or `S`.

For example `e17 <= e15` goes into `R` because it is reducing the identifier, whereas `e15 <= e17` would go into `S` since it is increasing the identifier.

In order to prove a query `a <=? b` we do a searching reduction of `a` by `R*` and `b` by `S*`. This correspond to an intuition that you should search up from `a` at the same time you search down from `b` <https://en.wikipedia.org/wiki/Bidirectional_search> , but the separation of R and S removes redundancies in that search.

This does not have as good of properties as a completed rewrite system, which has normal forms. We can't greedily destructively rewrite and have to retain all the things we can reach and see if the two cones emanating from `a` via `R` and `b` via `S^-1` intersect.

Because `R` and `S` are oriented producing eids in a monotonic orderly fashion, possibly enabling fast techniques involving min-heaps, sorted lists, and sorted merges.

# Code

This is a basic version of the above. I use brute force python sets of tuples  `set[tuple[int,int]]` to represent R and S. Obviously, one should probably use a better data structure, maybe something more like `dict[int, set[int]]`.

It is not clear that this structure is superior to the one I describe here <https://www.philipzucker.com/le_find/> . Things do come out a little more orderly, but at some conceptual complexity and rebuild cost. To what benefit?

```python
from dataclasses import dataclass, field
def find_down(T, x):
    """
    Transitively close downward from x. Pre apply T
    yT*x
    """
    res = set([x])
    while True:
        new = {y for (y,x1) in T for x in res if x == x1}
        if len(new - res) == 0:
            return res
        res |= new

def find_up(T, x):
    # xT*y . Transitively close upwards. Post apply T
    res = set([x])
    # dumbest possible loop. could seminiave it or keep queue.
    # new values come out monotonically
    while True:
        new = {y for (x1,y) in T for x in res if x == x1}
        if len(new - res) == 0:
            return res
        res |= new

@dataclass
class LEUF():
    R : set = field(default_factory=set)
    S : set = field(default_factory=set)
    fresh : int = 0
    def makeset(self):
        v = self.fresh
        self.fresh += 1
        return v    
    def find_le(self, x, y):
        zSy = find_down(self.S, y)
        xRz = find_up(self.R, x)
        return len(zSy & xRz) > 0
    def assert_le(self, x, y):
        if x == y:
            return True
        zSy = find_down(self.S, y)
        xRz = find_up(self.R, x)
        

        if len(zSy & xRz) == 0:
            if x < y:
                self.S.add((x,y))
            else:
                self.R.add((x,y))
        else:
            return True
    def rebuild(self):
        # form all SR critical pairs and reduce them
        # Or do the rebuilding immiediately in assert
        # Repeatedly rebuild until you learn nothing new
        pairs = {(x,z) for (x,y) in self.S for (y1,z) in self.R if y == y1}
        for (x,z) in pairs:
            if not self.find_le(x,z):
                self.assert_le(x,z)
        # possible remove redundant also


find_up({(1,2), (2,3)}, 3)
find_down({(1,2), (2,3)}, 3)

uf = LEUF()
x,y,z = uf.makeset(), uf.makeset(), uf.makeset()
uf.assert_le(x,y)
assert uf.find_le(x,y)
assert not uf.find_le(y,x)
assert not uf.find_le(x,z)
uf.assert_le(y,z)
assert uf.find_le(x,z)
assert not uf.find_le(z,x)

uf = LEUF()
x,y,z = uf.makeset(), uf.makeset(), uf.makeset()
uf.assert_le(x,y)
uf.assert_le(z,x)
uf
```

    LEUF(R={(2, 0)}, S={(0, 1)}, fresh=3)

You can also do a version of this that has an explicit union find and puts things in there is you ever assert `a <= b` and `a >= b`. The union find should also be a variant that tie breaks unions by `min`. eids can be canonized as you go along.

# Ground Term Asymmetric Completion

I'm fairly disturbed that Struth says ground asymettric completion fails. He has a counterexample. <https://www.sciencedirect.com/science/article/pii/S1571066104002968> Knuth-Bendix Completion for Non-Symmetric Transitive Relations - Georg Struth

# Ordered Resolution as Completion

Ordered Resolution and completion have a lot of similarity. Ordered resolution was designed in full knowledge of completion. I think it makes sense to think of ordered resolution as converting unordered clauses into prolog / datalog rules. This is different from standard completion in that there are many ways to orient a clause, not just two. If you have ordered all your clauses, you can then run the datalog program to construct a model. Ordered resolution combines rules in such a way to try and make this datalog run not reach an inconsistency.

|          | unoriented  | oriented     |
|----------|-------------|----------|
| Equality | equation `=`| rewrite `->` |
| Propositional |  clause  `c | a | not b` | rule `a :- b, not c` |

A bunch of propositional clauses has many models. If they are horn clauses (each has only one positive literal), then there is a very reasonable unique notion of a minimal model. If they aren't horn, you need to say how you'd like the tie break your preference of models with a term / proposition ordering. This is sort of like prescribing an objective function to the problem. If you can eliminate all models that would be minimal, then you've eliminated all models and the thing is unsatisfiable. Requiring only search through minimal models may eliminate the need to search through some models that would obviously not be minimal (there is some other model that must also work if that one worked that would be better).

The Struth article takes another road to model propositional reasoning as inequality reasoning module the axioms of a lattice. I'm not sure if this is a more or less radical perspective. <https://link.springer.com/chapter/10.1007/10721975_15> An Algebra of Resolution - Georg Struth. It's very interesting that a finitely presented lattice specialization of completion gives you something like resolution akin to how specializing to finitely presented rings gives you grobner bases and Buchberger's algorithm. This really caught my eye because I've been thinking more about e-graphs modulo theories lately rather than refinement egraphs, but this shows a connection between the two topics.

Ordered resolution can be seen as _set rewriting_ where matching on the left hand side does not consume it. This is in comparison to multiset rewriting, where you do consume resources. Ordered resolution completes to a datalog rule system that converts any given extensional database into the minimal model according to your chosen term ordering.

- Handbook of automated reasoning chapter 2 resolution <https://lawrencecpaulson.github.io/papers/bachmair-hbar-resolution.pdf>
- <https://rg1-teaching.mpi-inf.mpg.de/autrea-ws21/notes-3d.pdf>
- <https://www.tcs.ifi.lmu.de/teaching/courses-ws-2024-25/automated-theorem-proving/slides07-more-resolution.pdf>
- <https://www.philipzucker.com/superpose_datalog/> Superposition as a Super Datalog

Also relatedly, roughly speaking the Prolog Technology Theorem Prover  <https://link.springer.com/article/10.1007/BF00297245> and the MESON procedure (see Harrison Handbook of practical logic and automated reasoning 3.15 model elimination) are roughly:

1. Turn clauses into all horn rule orientations
2. Run a prolog which pays attention to if it is in a loop by looking at it's stack.

This is also a reasonable search procedure for equational stuff.

# Bits and Bobbbles

This post is a relative of this one <https://www.philipzucker.com/le_find/>

Resources on asymmetric completion:

- <https://www.iiia.csic.es/~levy/papers/jsc.pdf> Bi-rewrite Systems - JORDI LEVY AND JAUME AGUSTI
- <https://link.springer.com/chapter/10.1007/10721975_15> An Algebra of Resolution - Georg Struth
- <https://www.sciencedirect.com/science/article/pii/S1571066104002968> Knuth-Bendix Completion for Non-Symmetric Transitive Relations - Georg Struth
- <https://people.mpi-inf.mpg.de/alumni/ag2/2011/hg/index/index7.html> Look at part 2

nelson Oppen for inequalities. if we have an inequality union find, can we glue theories together with a common `<=` in addition to a a common `<`? Maybe.

I should write about dynamic strata for datalog, which is related to the above discussion about picking a term ordering to resolve negation problems.

For refinement e-matching, you probably need to enumerate everything above or below an eid, so the faster find_le maybe isn't as useful?

Assymmetric completion looks to me like a good engine for subtyping.

It's a bit odd that asymmetric completion doesn't seem like it went anywhere?

1. `S*R* <= R*S*` iff `(R U S)* <= R*S*`
2. `SR <= R*S*` implies `(R U S)* <= R*S*` if `R U S^-1` is wellfounded

These generalize church rosser and Newman's lemma

<https://www.iiia.csic.es/~levy/papers/jsc.pdf> Bi-rewrite Systems - JORDI LEVY AND JAUME AGUSTI

I'm surprised that Dolan's <https://www.cs.tufts.edu/~nr/cs257/archive/stephen-dolan/thesis.pdf> discussion of birewriting and biunification contains no reference to Levy and Agusti. Is the connection not known? Is there no connection?

<https://arxiv.org/abs/1802.08437> Abstract Completion, Formalized
<https://www.csl.sri.com/papers/bachmairtiwari00/cade00-CC.pdf> abstract congruence closure

Writing out some small examples helped me alot. Try out some small Hasse lattices with meangingless eid labels.

A second article Knuth-Bendix Completion for Non-Symmetric
Transitive Relations struth 2001. Also discusses the ground case. Says it is not terminating even for ground. Does automata something fix that? Noticing something? Seems odd.
`f(b) < b  R is reducing`
`f(a) < b  S is antireducing`

- Atomic completion is a union find. <https://www.philipzucker.com/egraph-ground-rewrite/> <https://www.philipzucker.com/egraph2024_talk_done/>

- Ground Term completion is an e-graph basically.

- Atomic asymmetric completion is an inequality union find.

- Ground Term asymmetric completion is a refinement egraph.

# Generalized Rewriting

Generalized rewriting and generalized congruence closure is the right framework for a refinement egraph.
It is propagation other relations besides equality up through function symbols.
You can bake this propagation in to the farbic of the egraph.
The refinement egraphs is a manifestation of refinement closure / monotonicity `a <= b -> f a <= f b` in the same way that the regular egraph is a manifestation or datatypification of congruence closure `a = b -> f a = f b`.

Dénès, M., Mörtberg, A., Siles, V.: A refnement-based approach to computational
algebra in coq

Generaliuzed rewriting <https://rocq-prover.org/doc/v8.18/refman/addendum/generalized-rewriting.html>
<https://jfr.unibo.it/article/download/1574/1077/3383> A New Look at Generalized Rewriting in Type Theory Sozeau
Subst (being <=) and diff being a fun symbol. That's a good one. since diff is `->` in some heyting sense, also makes sense.

Indeed A cup B <= C  is the same as A <= C  and B <= C . Is that useful? Does that fight an AC problem?
So set algebra. A = B, C = D,  diff, union, complement, intersection . Some of these do have anti modality.
set constraints
clp set
{a} <= A  is open set with a in it.  elem(a,A) == sing(a) <= A

"mediated" equality is very much exactly gewneralized rewriting in sozeau sense
The variance / compatibility rules are the custom congruence rules.

[Bas94] David A. Basin. Generalized Rewriting in Type Theory
A Semi-reflexive Tactic for (Sub-)Equational Reasoning  Claudio Sacerdoti Coen

Andrew McCreight. Practical tactics for separation logic
Nick Benton and Nicolas Tabareau. Compiling Functional Types to Relational Specifications for Low Level Imperative Code. used generalized rewriting for their tactics?

<https://maude.cs.illinois.edu/w/images/0/0f/BMgrt_2003.pdf>  Generalized Rewrite Theories -Roberto Bruni12 and Jos´e Mesegue . Maude. Kind of hartd to read. This might be getting at some of the same stuff. Yes.  E and R.

<https://www.youtube.com/watch?v=3Dh-EG6JfyU> Generalized Rewriting
Jovan Gerbscheid  gcongr tactic 2023 heather macbeth Lean  <https://icetcs.github.io/frocos-itp-tableaux25/slides/itp/lean4-gerbscheid.pdf>

Some suggested relations to do generalized rewriting over:

```
≤ <
≡ [ZMOD n] n
⊆
→
∣
=ᶠ[ae μ] almost everywhere equality
μ
```

My subsort checker database is basically a congryuence database?

cong = {
    set.Union: kd.ForAll([A,B,C,D], A <= B, C <= D, Union(A,C) <= Union(B, D))
    set.Inter:
}

# Semi Unification

<https://archive.computerhistory.org/resources/access/text/2024/01/102805327-05-01-acc.pdf> Henglein "semi-unification"

<https://pure.mpg.de/rest/items/item_1834874_3/component/file_1857517/content> Is this the same or a different semi unification?
<https://www.sciencedirect.com/science/article/pii/0304397591901899> Kapur semi unification
sig phi t = phi s
a unification and a matching
<https://types.pl/@flippac/115102336973734248>

or sig t <= sig s  equivalently.

<https://dl.acm.org/doi/10.1145/169701.169687> type reconstruction in the presence of polymorphic recursion
<https://cormack.uwaterloo.ca/rasup.pdf>  A Larger Decidable Semiunification Problem

# graph reachability

 Amortized efficiency of a path retrieval data structure
<https://www.sciencedirect.com/science/article/pii/0304397586900988>

<https://chaozhang-cs.github.io/files/sigmod23-tutorial-short.pdf> An Overview of Reachability
Indexes on Graphs

- tree cover indices
- 2-hop indices - hmm. Kind of like a union find to root, away from root. Finding good quasi roots
- approximate reachability

This does match my paradigm of rebuild or approximate.

<https://drops.dagstuhl.de/storage/00lipics/lipics-vol221-sand2022/LIPIcs.SAND.2022.1/LIPIcs.SAND.2022.1.pdf> Recent Advances in Fully Dynamic Graph
Algorithms

Inequality solvers in flow typechecker

- <https://github.com/facebook/flow/blob/main/src/typing/tvar_resolver.ml>
- <https://github.com/facebook/flow/blob/d076b30cfc3635ff8c38d43bee0b08c66cb9ec4f/src/typing/context.ml#L1209> find_root? I dunno. This seems problematic.

That lattice textbook

Where in compilers is there an example of a contravaraint symbol?
Inputs to function calls?
Call site f(x,y,z)
bind site
def f(x,y,z):  

t <= pat <= rhs

`t <bisubst= pat <= rhs

E-graph trinitarianism - hash cons <-> union find <-> egraph

Ordered chaining
<https://www.philipzucker.com/le_find/>

```
tSu          vSw
-----------------
  sig[t] S sig[w]
```

But with the usual restrction that we only need to do inferences that increase something?

ground ordered chaining. maybe there is some path compression that can work here?

<https://inria.hal.science/inria-00073205/document> Pottier thesis

Higher order Bi-Unfication
F(x) <= x

icfp gilbert something knitting groupoid. Hmm.

# Uses of refinement

2 more

- refinement reasoning in algerab of programming. Relational spec. functional implementation. The calculated typer <https://people.cs.nott.ac.uk/pszgmh/typer.pdf> . Program Construction: Calculating Implementation  from Specifications . Mathmeth <http://www.mathmeth.com/> <https://www.cs.ox.ac.uk/publications/books/PfS/> . Gries?
- Cycluic proofs.  We get the theoremwe're trying to rpover as a inequality guarded rule. Would not numerical ineq be good enough?1

<https://en.wikipedia.org/wiki/Relation_algebra>

<https://www.philipzucker.com/a-short-skinny-on-relations-towards-the-algebra-of-programming/>

<https://www.di.uminho.pt/~jno/ps/pdbc.pdf>

- Gibbons book?
- agda aop
- Backhouse calculation book

<https://staff.math.su.se/anders.mortberg/papers/refinements.pdf> refinement for free
dense poly to sparse poly

<https://link.springer.com/content/pdf/10.1007/978-3-031-57262-3_10.pdf>  Trocq: Proof Transfer for Free, With or Without Univalence 2024. Hmm. 2 versions of bitvec
CoqEAL library <https://github.com/rocq-community/coqeal>

Automatic and Transparent Transfer of
Theorems along Isomorphisms
in the Coq Proof Assistant  Theo Zimmermann1 and Hugo Herbelin 2015

Data vs Program rtefinement. Cahnge the program or change the datatype.
quot(X) = Y  fine. mod out permutations.
canon(Y) = X , pick one somewhat arbitrarily vs
Y -> X    . Kind of expressing containment in quoitent set. It is possible to refine Y to many possible X.

<https://en.wikipedia.org/wiki/Refinement_calculus>

# Algebra of Resolution

An algebra of resolution by struth 2000. That this seems only available in the proceedings compendium stinks.

A second article Knuth-Bendix Completion for Non-Symmetric
Transitive Relations struth 2001. Also discusses the ground case. Says it is not terminating even for ground. Does automata something fix that? Noticing something? Seems odd.
f(b) < b  R is reducing
f(a) < b  S is antireducing

`a { f { b`

f^n(a) < b

Can we find a good ordering though?
create `c` such that c = b and c is in a good spot.

Hmm. But we could close it out up to the currently existing terms. And then leave remaining critical pairs frozen or something.

Suppose we had a question about abstract entitites
`e17 <=? e42`

Then the R half of the inequality
`e17 R<= e13 R<= e11` Is being produced left to right

`e11 S<= e14 S<= e34 S<= e42` is being searched right to left using the S half of the inequality

In both cases the ids are being decreased. If the ids stop at `e0`, the process has to stop.

There may be more stuff in there. `e40 S<= e42` may also be a fact around that is not useful for this particular derivation, but you can't know it's not useful immediately.

That everything comes in a monotonic way probably makes for nicer usage of ordering based data structures like insorting on lists or sorted binary trees or minheaps and sorted merging.

Huh. When you write it out, it feels obvious this works, because we just perform a transitive closure.
But that you get to prune the transitive lcosure is non obvious.

The idea of proving a <= b  by searching up from a while at the same time searching down from b is intuitive

search up from a until you find b
search down from b until you find a
search simultaneously until you find a common connecting node <https://en.wikipedia.org/wiki/Bidirectional_search>

If you choose to search simultaneously, you may start sending out tendrils that "obviously" are going far below the thing you are looking for. It's good to prune these

For regular canonization, the properties of the rewrite system enable nice things.
If it is confluent and terminating , normalizing, you can greedily simplify
It it is just terminating but not confluent, it is possibly you need to do search, but the search will be finite.

proof orderings. A sequence of dudes. Lexicographically shortest proofs, which isn't what we'd ask for probably.

Relationship to subtyping
assymmettric

assymettric rewriting and linear programming. I had a spiel about working over R+ .
I wonder if Q semiring could use linear programming somehow, N semiring use MILP
The analog/generalization of F4 might use LP to do many semiring reductions at once

Ax <= c
Maybe R and S have a relationship to primary and dual?

Equations overs R+ is a way of baking inequality in (?)
`x**2` in grobner bases. `x**2 = linexpr` <-> `linexp >= 0`  DOes it make sense? Maybe. `x**4 = x**2`

sum of sqaures is nicer. But if we make grober + birewriting, do we get a systematic treatment of

It feels like the generalized / abstract KB and assymmetric KB are sometimes encodable?

Fourier motzkin. normalize to largest term (with positive 1 coefficient. That part is a bit odd)
x <= p
p <= x
Yeah, we don't get a normal form. that's how birewriting do

I do think I can encode fourier motzkin to grobner bases by making dummy variables. They kind of track

Simplex is goal driven.

Analagous algorithm for polynomials. Isolate largest monomial to positive side.
y*x**3 <= p
p <= zx**3

a = a -> bot
define a recursive type constant by an equation
X -> Y <= X' -> X' -> Y' -> <= X /\
There's no way to do this without a theory of lattices?

<https://theory.stanford.edu/~aiken/publications/papers/popl02.pdf>
<https://inria.hal.science/inria-00536817/document>  Entailment of Atomic Set Constraints is
PSPACE-Complete

```python
from dataclasses import dataclass, field
def find_down(T, x):
    # yT*x
    res = set([x])
    while True:
        new = {y for (y,x1) in T for x in res if x == x1}
        if len(new - res) == 0:
            return res
        res |= new

def find_up(T, x):
    # xT*y
    res = set([x])
    while True:
        new = {y for (x1,y) in T for x in res if x == x1}
        if len(new - res) == 0:
            return res
        res |= new

@dataclass
class LEUF():
    R : set = field(default_factory=set)
    S : set = field(default_factory=set)
    fresh : int = 0
    def makeset(self):
        v = self.fresh
        self.fresh += 1
        return v    
    def find_le(self, x, y):
        zSy = find_down(self.S, y)
        xRz = find_up(self.R, x)
        return len(zSy & xRz) > 0
    def assert_le(self, x, y):
        if x == y:
            return True
        zSy = find_down(self.S, y)
        xRz = find_up(self.R, x)
        

        if len(zSy & xRz) == 0:
            if x < y:
                self.S.add((x,y))
            else:
                self.R.add((x,y))
        else:
            return True
    def rebuild(self):
        # form all SR pairs and reduce them
        # Or do the rebuilding immiediately in assert
        pairs = {(x,z) for (x,y) in self.S for (y1,z) in self.R if y == y1}
        for (x,z) in pairs:
            if not self.find_le(x,z):
                self.assert_le(x,z)
        # possible remove redundant also


find_up({(1,2), (2,3)}, 3)
find_down({(1,2), (2,3)}, 3)

uf = LEUF()
x,y,z = uf.makeset(), uf.makeset(), uf.makeset()
uf.assert_le(x,y)
assert uf.find_le(x,y)
assert not uf.find_le(y,x)
assert not uf.find_le(x,z)
uf.assert_le(y,z)
assert uf.find_le(x,z)
assert not uf.find_le(z,x)

uf = LEUF()
x,y,z = uf.makeset(), uf.makeset(), uf.makeset()
uf.assert_le(x,y)
uf.assert_le(z,x)
uf
```

    LEUF(R={(2, 0)}, S={(0, 1)}, fresh=3)

```python
class LEUF():
    uf : list[int]
    R : set[tuple[int,int]] # eid decreasing part of <=
    S : set[tuple[int,int]] # eid increasing part of <=
    def find(self, x : int) -> int:
        if self.uf[x] != x:
            self.uf[x] = self.find(self.uf[x])
        return self.uf[x]
    def union(self, x:int, y:int):
        x,y = self.find(x), self.find(y)
        if x != y:
            self.uf[max(x,y)] = min(x,y) # tie break by min.
    def is_le(self, x, y):
        x,y = self.find(x), self.find(y)
        zSy = find_down(self.S, y)
        xRz = find_up(self.R, x)
        return len(zSy & xRz) > 0
    def assert_le(self, x, y):
        x,y = self.find(x), self.find(y)
        if x == y:
            return True
        elif self.is_le(y, x):
            return self.union(x,y)
        elif self.is_le(x, y):
            return True
        else:
            if x < y:
                self.S.add((x,y))
            else:
                self.R.add((x,y))

```

```python
from collections import defaultdict
@dataclass
class BinRel():
    xy : defaultdict = field(default_factory=lambda: defaultdict(set))
    yx : defaultdict = field(default_factory=lambda: defaultdict(set))
    def add(self, x, y):
        self.xy[x].add(y)
        self.yx[y].add(x)
    def __getitem__(self, shape):
        x,y = shape
        if x == slice(None):
            return self.yx[y]
        elif y == slice(None):
            return self.xy[x]
        else:
            raise NotImplementedError()

b = BinRel()
b.add(0,1)
b.add(0,2)
b[:,1]
b[:,2]

```

    {0}

```python
class LEUF():
    # R holds x le y where y < x 
    R : dict = field(default_factory=dict)
    # S hold y le x where y < x 
    S : dict = field(default_factory=dict) # defaultdict(set)
    def find_up(self, x):
    def find_down(self, x):

    def find(self, x, y):
        # normalize x le y. is_le ?

    def assert_le(self, x, y):
        x,y = self.find_le(x, y)
        if x == y:
            return
        elif x < y:
            self.R[x].add(y)
        else:
            self.S[y].add(x)


```

I don't know

Dustin suggests
 link-cut tree <https://en.wikipedia.org/wiki/Link/cut_tree>
 euler tour

What about floyd warshall? but floyd wasrahjll is for graphs.
x - y <= 5 is proof relevant inequality sure.

reow subtyping. {a : A, b : B} <= {a : A', b : B', c : C'}
accessor form a(X) = a(Y)? but a(X) <= a(Y) really.
eids as records.
This is like object stuff.

<https://www.youtube.com/watch?v=3Dh-EG6JfyU> Generalized Rewriting | Jovan Gerbscheid  gcongr tactic 2023 heather macbeth  <https://icetcs.github.io/frocos-itp-tableaux25/slides/itp/lean4-gerbscheid.pdf>

```
≤ <
≡ [ZMOD n] n
⊆
→
∣
=ᶠ[ae μ] almost everywhere equality
μ
```

My subsort checker database is basically a congryuence database?

cong = {
    set.Union: kd.ForAll([A,B,C,D], A <= B, C <= D, Union(A,C) <= Union(B, D))
    set.Inter:
}

Var trick for opening binders? Is it sound?
Use original lambda as "name" of variable.
lam(var(i) + 1) -->  fvar(lam(var(i) + 1)) + 1
Don't use numbers when you don't have to
"Skolemization"
"Use the reason it exists"
"provenance"

Analog of the `let` trick.
The free varaible was certainly "caused" by opening the binder.

Is 0*bvar(0) = 0 a refinement? Kind of feels that way (if looking up a variable is )
0*bvar(0) --> 0
It errors out in strictly less contexts.

The point of refinment/undef behavior is to enable more rewriting.

```python
from kdrag.all import *
State = smt.DeclareSort("State")
Rel = smt.ArraySort(State, State, smt.BoolSort()) # Pair -> Bool?

comp = smt.Function(".", Rel, Rel, Rel)
kd.notation.matmul.register(Rel, comp)
id = smt.Const("id", Rel)
R,S,T = smt.Consts("R S T", Rel)
id.left = kd.axiom(smt.ForAll([R], id @ R == R))
id.right = kd.axiom(smt.ForAll([R], R @ id == R))
comp.assoc = kd.axiom(smt.ForAll([R, S, T], (R @ S) @ T == R @ (S @ T)))

le = smt.Function("<=", Rel, smt.BoolSort())
kd.notation.le.register(Rel, le)

le.trans = kd.axiom(kd.QForAll([R, S, T], le(R, S) & le(S, T), le(R, T)))
le.refl = kd.axiom(kd.QForAll([R], le(R, R)))
le.antisym = kd.axiom(kd.QForAll([R, S],
    le(R, S) & le(S, R) >> (R == S)))

# I could define them, but yolo

Set = smt.ArraySort(State, smt.BoolSort())
dom = smt.Function("dom", Rel, Set)
cod = smt.Function("cod", Rel, Set)

conv = smt.Function("conv", Rel, Rel)
conv.id = kd.axiom(smt.ForAll([R], conv(id) == id))
conv.comp = kd.axiom(smt.ForAll([R, S], conv(R @ S) == conv(S) @ conv(R)))
conv.inv = kd.axiom(smt.ForAll([R], conv(conv(R)) == R))

join = smt.Function("join", Rel, Rel, Rel)
kd.notation._or.register(Rel, join)
join.comm = kd.axiom(smt.ForAll([R, S], R | S == S | R))
join.assoc = kd.axiom(smt.ForAll([R, S, T], (R | S) | T == R | (S | T)))
join.le = kd.axiom(smt.ForAll([R, S], R <= R | S))
join.univ = kd.axiom(smt.ForAll([R,S,T], ((R | S) <= T) == (R <= T) & (S <= T)))

top = smt.Const("top", Rel)
bot = smt.Const("bot", Rel)

const = smt.Function("const", State, Rel)



```

# Boolean Valued Models

Boolean valued models <https://jdh.hamkins.org/a-gentle-introduction-to-boolean-valued-model-theory/>
a version of congurence closure with inequalites
`[[t0 = f(s)]] /\ [[t1 = f(x)]] <= [[t0 = t1]]``

If the set / boolean algebra in question is a proof set?

Is this true of separation logic or tla?

# Unification Subsumption and

# Setlog and set constraints

See clp_set notes

```python

```

```python
%%file /tmp/stuff.pl

hello("world").

```

    Writing /tmp/stuff.pl

```python
! scryer-prolog /tmp/stuff.pl -g 'hello(X), write(X), halt.'
```

    [w,o,r,l,d]

```python
%%file /tmp/minikan.rkt
#lang racket
(require minikanren)

(run* (q) (== q 'hello-world))
(run* (q) (fresh (x) (== x 'hello) (== q x)))
```

    Overwriting /tmp/minikan.rkt

```python
! racket /tmp/minikan.rkt
```

    '(hello-world)
    '(hello)

# Refinement Closure

---

title: Congruence Closure becomes Refinement Closure for Refinement E-graphs
---

Using the term E-graph maybe is a bit of a misnomer.

Even in refinement reasoning, equalities are pretty prevalent.

Congruence closure generalizes to refinement closure

cong close saturates
x = y -> f(x) = f(y)

ref closure saturates
x <= y -> f(x) <= f(y) for monotonic
x <= y -> f(y) <= f(x) for anti-monotonic

x0 <=^p0 y0, x1 <=^p1 y1, ... -> f(x0,x1,x2,...) <= f(y0, y1, y2,...)

Where pn are the polarity of position n in the function symbol f.

Arrow in subtyping has polarity signature
arr(-,+)

parents and upper are similar beasts kind of.

Is there a relationship between the dpeendent egraph and refinement egraph. Types kind of givey ou a handle on partiality.

Yea, maybe this is a point towards egglog.

```python
class REGraph():
    def __init__(self):
        self.enodes = {}

    def rebuild(self):
        # The quadatic loop version
        for enode1 in enodes:
            for node2 in enodes:
                if all(self.uf.is_le(x,y) in zip(enode.args, enodes1.args)):
                    self.uf.assert_le(enode1, enode2)
        
        for enode1 in enodes:
            # search through all upper sets of args
            # we can prune though things with smallest args set
            # indeed, good joins cure a lot of wounds.
        
        # alternative: Fill out the upper set of args
        for enode in enodes:
            for a in self.uf.le_set(enode.args[0]):
                e1 = self.enodes.get_make(enode with a)
                self.uf.assert_le(a, e1)
            





```

# Datalog Model

Datalog / Relational / Flattened model

Egglog also has datalog model. brute force eq(x,y) relation with symmettry and transitivity moves.

Refinement closure can either brute fore

```
f(x,y) ~  f(x,y,res) relation

% refinement closure

% don't generate new symbols
 le(z,z1) :- f(x, z), le(x, y), f(y, z1)

% Do generate new f ids
set f(y) <= z :- f(x) = z, x <= y

```

Generalized rewriting coq
FOLDS.
Lessons that baking in boring congruence may not be what you want.

# Ground Ordered Chaining

```python
type le = list[tuple[object,object]]


```

## Chain UF

The idea of an approximate LE via carefully picking how parents work is interesting.
Is there a domain where this can be thought of as precise? Not general partial order.
Maybe it can be precise if we guarantee a maximum width?

```python
# do you best to try and store good chains. https://en.wikipedia.org/wiki/Partially_ordered_set#Derived_notions
# chains are kind of like parent
class LEFind():
  chain0 : list[int]
  chain1 : list[int]

  def union(self, a, b): ...
    # seek lowest common ancestor?

  # .. chain
```

```python

```

# biunify kata

Everything I can do with terms

- matching
- unification
- egraphs
- knuth bendix
- subterm

Can i extend to "bi" versions?

- BiProlog . BiKanren

Based on the LEfind, should bi substutuitions be done as
{eq : , upper : [] , lower : []}
Presumably the equality case is more common (?) so should be pulled out.
`(<= a b)` in minikanren would branch or assert?
bi is the analog of e-unification in many respects.
So look more towards FLP for inspiration?

Would LEFind be useful for a CLP(Set)?

```python
type bisubst = tuple[dict,dict]
def apply(pat, bisubst): ...
def bimatch(t, pat): ...
def biunify(): ...



```

```python
from kdrag.all import *
def le_unify(t1, t2): 
    upsubst : dict[object, list[object]]= {} # nondet substitution
    downsubst = {}
    eqsubst : dict[object, object] = {} # equality substitution

    todo = [[(t1,t2)]]
    while todo:


```

# smt egraph

```python
from dataclasses import dataclass
from collections import defaultdict
@dataclass
class LEFind():
    parents : dict
    upper : defaultdict(set)
    lower : defaultdict(set)
    def __init__(self):
        self.parents = {}
        self.upper = defaultdict(set)
        self.lower = defaultdict(set)
    def assert_le(self, x, y): # assert to LEFind that x <= y
        x,y = self.find(x), self.find(y)
        if x == y:
            return
        self.upper[x].add(y)
        self.lower[y].add(x)
        if self.is_le(y, x): # propagate antisymmettry x <= y and y <= x implies x == y
            self.union(x, y)
            for z in self.le_set(x) & self.ge_set(y): # anything between the two is squeezed
                self.union(z, y)
            for z in self.le_set(y) & self.ge_set(x): # anything between the two is squeezed. Is this redundant?
                self.union(z, x)
    def assert_ge(self, x, y): # assert to LEFind that x >= y
        self.assert_le(y, x)
    def union(self, x, y): # assert that x == y
        x, y = self.find(x), self.find(y)
        if x != y:
            self.parents[x] = y # refular union find
            self.upper[y].update(self.upper[x]) # merge upper sets
            self.lower[y].update(self.lower[x]) # merge lower sets
    def find(self, x : int) -> int:
        while x in self.parents:
            x = self.parents[x]
        return x
    # The next 3 functions are very similar. is_le can early stop when it hits y.
    def is_le(self, x, y) -> bool:
        # DFS search for y in upper set of x
        x,y = self.find(x), self.find(y)
        if x == y:
            return True
        todo = [x]
        seen = set(todo)
        while todo:
            x = todo.pop() # invariant is that x is already representative
            for z in self.upper[x]:
                # Is there a way to use lower set for pruning?
                z = self.find(z)   # compression could be updating z in place in upper[x]
                if z == y:
                    return True
                elif z not in seen:
                    seen.add(z)
                    todo.append(z)
        return False
    def le_set(self, x) -> set[int]: # all solutions to x <= ?
        x = self.find(x)
        todo = [x]
        seen = set(todo)
        while todo:
            x = todo.pop()
            for z in self.upper[x]:
                z = self.find(z)
                if z not in seen:
                    seen.add(z)
                    todo.append(z)
        return seen
    def ge_set(self, x) -> set[int]: # all solutions to x >= ?
        x = self.find(x)
        todo = [x]
        seen = set(todo)
        while todo:
            x = todo.pop()
            for z in self.lower[x]:
                z = self.find(z)
                if z not in seen:
                    seen.add(z)
                    todo.append(z)
        return seen
```

Hmm. You know, if there is no further interpretation of le, Having the solver backed version does not help anything.

FALSE. Kind of. Refinement closure. But we can't express monotonicty to smt without using quantiufiers.

forall x <= y -> f(x) <= f(y)

There is also an issue that I don't really know how to encode a model of undefinedness into SMT.
The relational model? That's more like the contextual egraph right?
The option model?

```python
from kdrag.solvers.egraph import EGraph

class LEGraph(EGraph):
    def __init__(self):
        super().__init__()
        self.lefind = LEFind()
        self.le_prim = smt.Function("le", smt.IntSort(), smt.IntSort(), smt.BoolSort())
        self.le = smt.TransitiveClosure(self.le_prim)
    
    def assert_le(self, x, y):
        self.lefind.assert_le(x, y)
        self.solver.add(self.le_prim(x, y))

    def is_le(self, x, y):
        return self.lefind.is_le(x, y)
        with self.solver:
            self.solver.add(smt.Not(self.le(x, y)))
            return self.solver.check() == smt.unsat
    def le_set(self, x):
        return self.lefind.le_set(x)




```

```python
@dataclass
class EGraph():
    lefind : LEFind
    enodes : dict


```
