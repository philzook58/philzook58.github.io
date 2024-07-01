---
title: EGraphs as Ground Completion Talk and EGRAPHS 2024 notes
date: 2024-07-01
---

I'm back from Copenhagen! It was really fantastic time. Thanks everyone for the chats and saying you read my blog / enjoyed my talk! I really wish I had stayed for Thursday and Friday as I was still having great conversations. It wasn't clear when I was booking if I would get any time from work, so I tried to hedge things a little. I looked into changing my flights around and it would've doubled the cost of my trip. Oh well, live and learn.

I rerecorded a version of my talk while I still remember roughly how to give it. Unfortunately, it seems the stream of my high energy audience version has a stuttering problem

<iframe width="560" height="315" src="https://www.youtube.com/embed/74VP0SbNHDE?si=FFaR9ExzA_GMM-yD" title="YouTube video player" frameborder="0" allow="accelerometer; autoplay; clipboard-write; encrypted-media; gyroscope; picture-in-picture; web-share" referrerpolicy="strict-origin-when-cross-origin" allowfullscreen></iframe>

# The Big Takeaway From My Talk

Ground completion gives a canonical rewrite system that is as visualisable as regular egraphs, but has better scoping and is more ready for extensions.
The standard [egg](https://egraphs.org/) example of ground equations describing multiply by two = shift by 1, and noticing a division cancellation becomes upon equational/knuth bendix completion the ground rewrite system

$$  mul(a, two) \rightarrow shift(a, one) $$

$$  mul(a, one) \rightarrow a $$

$$ div(two, two) \rightarrow one $$

$$  div(shift(a, one), two) \rightarrow a $$

Can be drawn as (representing rewrite arrows as red dotted arrows)

![ground rewrite egraph](/assets/egraph2024/egraph2.svg)

Whereas the egg diagram looks like

![egg egraph ](/assets/egraph2024/egraphs_1.svg)

Note that

- The enodes in the egg diagram have eclasses as children, whereas the GRS egraph is actually about terms
- Red arrows connect things in the same eclass, but they are directed towards the better terms. This gives a useful and principled directionality internal to an eclass.

# EGRAPHS 2024

Another great year!

<iframe width="560" height="315" src="https://www.youtube.com/embed/JPA8QwLHNzo?si=73qlWZNhvUF4cVPh&amp;start=1572" title="YouTube video player" frameborder="0" allow="accelerometer; autoplay; clipboard-write; encrypted-media; gyroscope; picture-in-picture; web-share" referrerpolicy="strict-origin-when-cross-origin" allowfullscreen></iframe>

- The highlight may have been the slotted egraphs talk, which I actually missed (I was chatting in the hall but I watched it that night). I think they are really on to something. For my money, I just want a solution to alpha equivalence in the egraph, which this may be a functioning version of. I have a suspicion that their solution can be cast as ground nominal completion if that's what you're into. <https://pldi24.sigplan.org/details/egraphs-2024-papers/10/Slotted-E-Graphs>. Slots are wires. Maybe integrate the permutation union find (you can tag the dges of a union find with group elements <https://www.philipzucker.com/union-find-groupoid/>)? This seems similar to why Kmett was thinking about such things anyway. He was doing something nominal. <https://youtu.be/KxeHGcbh-4c?t=1254>
- The hyperegraphs talk was attacking some things along lines I have been musing about. I have not been going category theory, but I think there is an argument that we keep trying to model graphs (usually program graphical IRs) as terms by cutting them up in fairly arbitrary algebraic flavored ways. There _is_ an possible indirection for graphs/hypergraphs analogous to that in the egraph. If I wanted to cut a little chunk out of the egraph and replace it using a rewrite rule, I can keep both copies if I put a boundary class hyperedge around the region I'm cutting. Non overlapping graph/hypergraph rewriting can chare a lot of structure in this way. For overlapping structure, you need to expand out / push this boundary enough that you can find your complete pattern. Maintaining this mushing around of hypedge eclasses seems annoying. Recollecting up shared structure / "canonization" I think can be done greddily and imperfectly via something analgoous to the FM algorithm for greedily improving partitioning. I think in their presentation they did not give any clues to how to implement such a thing, so the idea of "baked in structure" seems false without that. Maybe mathematically its baked in but that isn't quite enough. <https://en.wikipedia.org/wiki/Fiduccia%E2%80%93Mattheyses_algorithm>  <https://pldi24.sigplan.org/details/egraphs-2024-papers/9/Equivalence-Hypergraphs-E-Graphs-for-Monoidal-Theories>
- The SpEQ paper is honestly shocking (in an impressive way). I would describe it as kind of like instruction selection for big kernels like MKL. The use case barely skirted around issues of alpha equivalence in the egraph. Rules are intrinsically alpha equivalent so that's fine, but also because they weren't generating new stuff. It also reminds me a bit of Jimmy Koppel's code search YOGO <https://www.jameskoppel.com/publication/yogo/>
- Hardware continutes to be very intriguing. A lot of promise there. Clock gating. Data gaating. Transparent latch
- Test Set reduction. Interesting use case
- The monoidal category talk reminds me a lot of a line of work I was pursuing and actually brought me into egraphs [Rewriting Monoidal Categories in the Browser with Egg](https://www.philipzucker.com/rust-category/)
- The disequality talk I thought was quite enjoyable and illuminating. "Forbid" is a magic word for disequality in egraphs and was considered by Nelson. Disequality edges in the graph. Things you aren't equal to is kind of a set/lattice like analysis you can tag. Maybe it would be nice to just have a pull request into egg putting this feature in there if its as easy to do as the slides suggest? <https://pldi24.sigplan.org/details/egraphs-2024-papers/14/Disequalities-in-E-Graphs-An-Experiment>. Would it be nice to reify equality edges in the diagram too? Is it not meaningful?

## Other notes / thoughts from conference

- Max B is into serialization and hashing. The Ground completion egraph is easy to write down canononically, whereas the egg egraph it is not obvious (general graph hashing / isomorphism techniques?). Each rewrite rules is a tuple. Terms have an ordering to them. Write down the tuples in order. That is a canonical representation of the egraph that is hashable via the usual structural means.  <https://www.philipzucker.com/hashing-modulo/>
- The GRS egraphs might be nice for the "use egraph to get full equational system" problem of QEL <https://pldi23.sigplan.org/details/egraphs-2023-papers/8/Partially-Complete-Quantifier-Elimination> (they wanted to use it for fast quantifier elimination)
- Refinement in egraphs. A possibly a very useful thing if it can be straightened out. ALive2, refining optimizations. Good question from Zach
- Seems like someone in the UW crew as attacking the hyperreals. Fantastic!
- I'm excited for possible future collaborations with Max B and CF in more serious compiler work. Good convos.
- Z3 inside Z3 for hilbert choice
- JIT is interesating. Linearized control flow but with contexts coming from guards/asserts. Superposition on inline vs not in egraph a la Oliver?
- Cheney List copying
- Householder <https://www.cs.princeton.edu/~zkincaid/> ? What was Zach talking about?
- Eva compiler for Reals. Daisy. Comparison of float32 vs float16 instead of attack reals? More useful even sometimes since the "spec" is some program people know works and we just want to reduce bitwidth for speed or something. Also if changing float size does something weird, something is fishy anyway.
- Bombe game <https://store.steampowered.com/app/2262930/Bombe/>. Is prolog like?
- Hydra <https://users.cs.utah.edu/~regehr/generalization-oopsla24.pdf> Hydra: Generalizing Peephole Optimizations with Program
Synthesis
- "Coninductive" Egraphs. Useful for PEGs? Mark some things as object like identifiers. Observations go in ground completion egraph `head(s) -> 3; tail(s) -> s1`.Run automata minimization on them.
- Solver for arbitrary bitvector length?
- Rudi thinks I should seriously bench mark bottom up ematching. It is important to have an outsider believe in something.
- Gotta get in on that sparse tensor shit
- SSI is kind of like ASSUME nodes <https://dspace.mit.edu/bitstream/handle/1721.1/86578/48072795-MIT.pdf>
- Hyperreal Asbtract rewrite system and lyapunov functions? Insane talk.
- Refcells lambdas. Linear typing. Prolog lambdas. Unification variables are a "resource"
- Prolog continuations  / CPS and Nat decuct -> sequent calc
- Their geese are like ours, but wrong.

# My Talk Abstract

Pdf here <https://github.com/philzook58/egraphs2024-talk/blob/main/egraphs2024_abstract.pdf>

Introduction
============

Term simplification is a natural and intuitive concept. It can be used
to both solve algebra problems and optimize compiler output.

A first simple but effective impulse is to treat simplification via
greedy rewriting.

Like many heuristic greedy methods, it is possible that a locally greedy
move can lead to globally suboptimal results. It is sometimes necessary
to travel up the mountain to escape the valley. To fix this, some amount
of breadth first or backtracking exploration is necessary.

The field of automated reasoning has been aware of and refining these
notions for a long time.

- Paramodulation [@NIEUWENHUIS2001371] is a breadth first technique
    for (possibly conditional) equational reasoning

- Completion[@traatbook] is a method to convert an equational system
    to one with good guaranteed greedy rewriting properties. It can also
    be seen as equational reasoning with strong redundancy removal
    principles.

- Superposition [@braniac] combines properties of completion and
    paramodulation.

E-graphs [@eggpaper] are a compact data structure for representing a
collection of ground equations over terms and their congruence closure.
They are an intuitively appealing technique for theorem proving and
simplification. No small part of this intuition is provided by the
bipartite graphical diagram of e-classes and e-nodes. There is a lower
theoretical and technical barrier to entry in e-graph rewriting than for
navigating the complex automated reasoning literature. This conceptual
simplicity has been essential for the e-graph's flourishing
applications.

There is also a difference in attitude between the mainstream of the
automated reasoning community and the e-graphs community. The majority
of the literature in automated reasoning is concerned with theorem
proving problems. The e-graph literature has a healthy contingent
concerned with simplification/optimization/compiler problems. The
e-graph community wants a controllable quasi operational view of the
search process and desire for completeness of the search does not
override pragmatism. This is similar to the viewpoint of the Argonne
school of automated reasoning [@ottermanual] [@wosautomated], which
supported a more tweakable operational approach to automated reasoning.

This talk is about explaining some of the connections between different
techniques and how they may give clues to fundamental problems in
e-graphs.

Union Finds as Completion
=========================

The union find is a key component of the e-graph. It can be seen as an
instance of completion [@groundegraph]. Indeed many algorithms,
including Gaussian elimination, Grobner bases, resolution and others,
can be viewed in this light.

A union find is a forest of equivalence classes. The pointers in the
tree point upward to parents rather than downward to children. This can
be viewed as a discrete dynamical system describing a convergent flow to
a canonical member of the class. In other words, a convergent rewriting
system.

For example, the following rewrite system is a representation of a union
find where $b$ and $c$ are children of a canonical member $a$ and $e$ is
a child of the canonical member $d$.

$$b \rightarrow a$$ $$c \rightarrow a$$ $$e \rightarrow  d$$

Completion can be described as an inference rule system [@traatbook],
orienting equations into rewrite rules and simplifying them. This
simplification is a perspective on the path compression step in the
union find.

The pieces of a simple union find algorithm can be dignified via
reference to these rules.

```python
class UF():
  def __init__(self):
      self.rules = {}
  def find(self, x):
      # `find` reduces x with respect 
      # to the current rules (x -R-> retval)
      while self.rules.get(x) != None:
          x = self.rules.get(x)
      return x
  def union(self, x, y):
      # Do incremental completion starting with
      # (E,R) == ({x = y}, self.rules )
      x1 = self.find(x) # SIMPLIFY  ( {x1 = y} , R)
      y1 = self.find(y) # SIMPLIFY  ( {x1 = y1}, R)
      if x1 == y1: # TRIVIAL ({x1 = x1}, R)
          return x1 # (Empty, self.rules)
      else:
          if x1 < y1: # the "term order"
              x1,y1 = y1,x1 # swap
          # ORIENT  (empty, R U {x1 -> y1})
          self.rules[x1] = y1 
          return y1
  def canon(self):
      for lhs,rhs in self.rules.items():
          self.rules[lhs] = self.find(rhs) # r-simplify
```

E-graphs as completion
======================

Performing a regular completion procedure on ground terms is guaranteed
to terminate. By putting the system in a flat canonical form, it is
easier to see the correspondence with more familiar e-graph notions.

The flattening transformation can be achieved by creating fresh ground
symbols for every function application in the original set of equations.

For example,

$$foo(biz(baz), bar) = bar$$

becomes

$$bar = e1$$

$$baz = e2$$

$$biz(e2) = e3$$

$$foo(e3,e1) = e4$$

$$e4 = e1$$

With an appropriate ground term ordering that puts every $e$ less than
any function symbol will orient the system into the form

$$bar \rightarrow e1$$ $$baz \rightarrow e2$$

$$biz(e2) \rightarrow  e3$$

$$foo(e3,e1) \rightarrow e4$$

$$e4 \rightarrow e1$$

Completing a ground system of this sort will put it in a canonical form.
The rewrite rules can be separated into two classes, those that rewrite
e-nodes to e-classes and those that rewrite e-classes to other
e-classes. The first represents the membership of e-nodes to their
e-class and the second class represents a union find.

If we write $e$ as $q$, this becomes the definition of a tree automata
as has been noted [@treeautomata]. Tree automata implicitly describe
classes of trees using functional folds over finite state accumulators
as acceptor functions, which can be described by tabulatable data. The
ground rewriting point of view of e-graphs is the same observation as
identifying e-graphs with tree automata but with a different emphasis of
ideas.

The flattening transformation is not necessary for ground completion,
but it does make the system more uniform. Notions of binding and context
can be an impediment to this flattening transformation, so this
complication may have a purpose.

Extraction
----------

The idea of a term ordering has not made an explicit appearance in the
modern e-graphs literature to the author's knowledge. Term ordering is a
generalization of the notion of comparing terms for simplicity
[@traatbook]. We typically want to rewrite a big term into a smaller
one. With a completed ground rewrite system, running the system against
the initial term will compute an equivalent smaller term. This is the
analog of the e-graph extraction process, and picking a term order picks
the extraction goals. Giving symbols extraction weights corresponds to a
similar notion that appears in knuth bendix ordering.

E-matching
==========

The first component of e-graph rewriting is to have an e-graph. The
second component is e-matching.

An e-graph implicitly represents a possibly infinite set of terms that
are equivalent to terms inserted via the ground equations.

A ground completed rewrite system represents a possibly infinite set of
terms that rewrites to something that is a right hand side of the
system. Alternatively, the set is generated by running the rules
backwards.

E-matching is trying to find a term in this set that matches a pattern.
This can be described in the terminology of the GRS without explicit
reference to e-graphs [@ematchground].

Bottom up e-matching is the simplest naivest method. One makes a
nondeterministic guess to fill in variables in the pattern with a choice
of right hand side in the GRS. Then one reduces the grounded pattern and
see if reduces to a right hand side or not. Top down e-matching can be
achieved by narrowing the variables in the pattern according to current
rewrite system. Every narrowing will ground out the pattern, since the
rewrite system is ground.

Saturation
==========

Saturation is not a unique property of e-graph rewriting. Traditional
automated reasoners are also saturating systems.

It is a known technique in the automated reasoning community that it is
useful to separate clauses into at least two groups that are not treated
symmetrically. Sometimes these are called unprocessed/processed or
usable/set of support [@ottermanual]. Naive resolution or paramodulation
considers every possibly pair of interaction between currently derived
clauses. The given-clause algorithm is a form of semi-naive evaluation
that only further processes fresh clauses from the unprocessed set
against the processed set.

Something quite similar to e-graph rewriting can be made to occur by
restricting a superposition prover to only allow superposition between a
ground rewrite rule and a non-ground rewrite rule. This is similar to
some mixture of hyper-resolution, UR-resolution, and set of support
strategies [@wosautomated].

Hints for a Road Forward
========================

There are a number of possible tantalizing expressivity extensions to
the e-graph. The extreme sharing and destruction of context in the
e-graph make many extensions hard to talk about. The connection back to
term rewriting and automated reasoning sheds light on possible
implementation methods.

Context
-------

Superposition is a technique for equational theorem proving. It extends
Knuth Bendix completion to equational clauses. A clause of terms
$a \neq b \vee b = c$ can be seen as an implication
$a = b \rightarrow b = c$.

Horn encodings [@hornformula] are a technique for getting context into
pure completion solvers. It is similar in character to ASSUME nodes
[@coward2023automating].

Another suggested technique for context is colored e-graphs
[@singher2023colored]. I am not aware of a similar notion in the
automated reasoning literature.

Lambda
------

Recently superposition has been extended to support lambda terms
[@bentkampsuperposition]. A restriction of this capability should be
sufficient to implement an analog of e-graph rewriting for lambda terms.

It is not clear that full lambda unification or matching is necessary or
desirable. It depends on the application and performance trade offs.
More limited but efficient forms of matching that nevertheless treat
variable binding correctly such as Nominal unification [@nominal] or
Miller patterm unification [@miller] may be preferred.

Backwards Reasoning
-------------------

E-graph saturation is a bottom up technique analogous to datalog. A
natural question is raised as to what a natural top down like prolog
would look like.

Datalog and prolog can be viewed as incomplete strategies for resolution
in a similar way that egglog [@egglog] and functional logic programming
are incomplete strategies for superposition.

Understanding this connection may be useful in possible applications of
e-graph techniques to typeclass or trait resolution.

AC
--

The automated reasoning community has been aware of the issue of
associativity and commutativity from the beginning. These rewrite rules
are difficult to orient, commonplace, and very structural. There is a
large literature on this subproblem and modern automated theorem such as
E and Vampire have some intrinsic support for this.

Eager Rewriting
---------------

Demodulation is terminology used for eager rewriting in theorem provers.
The ground rewrite system perspective of e-graphs lends some clarity to
the lack of completeness that may result.

E-matching in the e-graph's community refers to matching over an
e-graph. E-matching in the automated reasoning community refers to the
more general mechanism of matching with regards to a background
equational theory, often theories that are confluent and terminating.
This is another approach to building in rewriting with respect to an a
priori well behaved set of rewrite rules.

Universal Variables
-------------------

Proving universal goals using e-graphs requires some slight of hand and
preprocessing. Standard automated reasoning techniques support true
unification variables, which are an assertion of the universal
applicability of the fact derived. They are scoped to their clause and
are alpha renameable, which makes them distinct from the e-graph's
equational constant symbols. Some degree of inter-emulation is possible.

Sketches and Hints
------------------

The two communities have separately invented similar notions of sketches
[@sketch] and hints [@hints].

Conclusion
==========

E-graph rewriting and other automated reasoning techniques are deeply
interconnected. Neither is strictly better than the other and lessons
can flow in both ways. The e-graph has a intuitive appeal and by
focusing on a subproblem is simpler to implement and hence fast.
Automated reasoning systems implementing completion or superposition
have a long history of theoretical and implementation refinement. It is
seemingly conceptually simpler to extend these systems than to extend
the highly shared and context destroying e-graph, but perhaps a new
efficient and expressive perspective can emerge by pumping insight
between the two.

This material is based upon work supported by the under Grant No.  and
Grant No. . Any opinions, findings, and conclusions or recommendations
expressed in this material are those of the author and do not
necessarily reflect the views of the National Science Foundation.

# Talk Slides

Actual talk file here <https://github.com/philzook58/egraphs2024-talk/blob/main/egraphs_talk.ipynb> I used RISE, a jupyter extension. It worked ok. Had to tweak some sizes and it still didn't end up perfect. I didn't end up having as much interactive code running as I thought. That was overly ambitious.

# Egraphs and Automated Reasoning

### Looking Back to Look Forward

Philip Zucker

June 22, 2024

# The Main Points of The Talk

- <b>Simplification & Completion</b>
- Union-find is Ground Atomic Completion
- E-Graph is Ground Term Completion
- ? is Lambda, Context, Destructive
- Compilers from Automated Reasoners

In the Beginning...

# 💥 SIMPLIFICATION 💥

# Greedy Simplification

- ex: $a + 0 \rightarrow a$
- Good
  - Fast
  - Simple
- Bad
  - Rule Interaction / Phase Ordering $\{a * 2 \rightarrow a \ll 1; (a*b)/b \rightarrow a \}$
  - Non termination $a + b \rightarrow b + a$
  - Incompleteness / Suboptimality

# [E-Graphs](https://egraphs-good.github.io/) 🥚

- They're Good
  - Graphical, Simple
  - Declarative-ish
  - Operational-ish
  - Fast-ish
- Many applications
- Usage Modes
  - Proving: `Term -> Term -> Bool/Proof`
  - Simplifying: `Term -> Term`

<center><img width="50%" src="./egraphs.svg"></center>

$$ a * 2 = a \ll 1 $$
$$ (a * 2) / 2 = a *(2 / 2) = a * 1 = a $$

# Refinements

- Paramodulation (60s) - Go breadth first and conditional
- Completion (70s) - Make greedy good, remove redundancy
- Superposition (90s) - Combo

# Completion

- Make Equations into "Good" Rules
  - Terminating
  - Confluent - No phase ordering problem
- Early Stopping
  - Goal Driven
  - Simplification Driven

# Basic Completion

1. Orient according to Term Order
   $$[X * 2 = X \ll 1] \Rightarrow \{X * 2 \rightarrow X \ll 1\}$$
2. Add critical pairs (CPs) as equations
   $$\{X * 2 \rightarrow X \ll 1;  (X*Y)/Y \rightarrow X\} \Rightarrow $$
    $$ [(X \ll 1) / 2 = X]$$
4. Reduce Equations
    $$[a = b], \{a \rightarrow c\} \Rightarrow [c = b], \{a \rightarrow c\}$$
5. Repeat

# More Advanced Completion

![image.png](egraphs_talk_files/image.png)

Src: Baader and Nipkow

# [Twee](https://nick8325.github.io/twee/)

- Theorem prover for equational logic
- It is built around completion
- Optimized Haskell
- [TPTP](https://www.tptp.org/) input
- [CASC UEQ](https://tptp.org/CASC/)

```python
%%file /tmp/shift.p
fof(shift, axiom, ![X] : mul(X,two) = shift(X, one)).
fof(cancel, axiom, ![X,N] : div(mul(X,N),N) = X).

fof(goal, conjecture, true = false).
```

    Overwriting /tmp/shift.p

```python
!twee /tmp/shift.p
```

    Here is the input problem:
      Axiom 1 (shift): mul(X, two) = shift(X, one).
      Axiom 2 (cancel): div(mul(X, Y), Y) = X.
      Goal 1 (goal): true = false.
    
    1. mul(X, two) -> shift(X, one)
    2. div(mul(X, Y), Y) -> X
    3. div(shift(X, one), two) -> X
    
    Ran out of critical pairs. This means the conjecture is not true.
    Here is the final rewrite system:
      mul(X, two) -> shift(X, one)
      div(mul(X, Y), Y) -> X
      div(shift(X, one), two) -> X
    
    RESULT: CounterSatisfiable (the conjecture is false).

# The Main Points of The Talk

- Simplification & Completion
- <b>Union-find is Ground Atomic Completion</b>
- E-Graph is Ground Term Completion
- ? is Lambda, Context, Destructive
- Compilers from Automated Reasoners

# Union Finds as Atomic Rewrite Systems

- Egraph ~ union find + hash cons
- Union find
  - forest of equivalence classes
  - Pointers up to parents
- Find = Convergent Dynamical System
- Convergent Dynamic System = Confluent Abstract Rewrite System

| TRS | UF |
|------|---------------|
| Run TRS  |           Find    |
|  Add equation   |        Union     |
| R/L simplify | Compression |
| Term Ordering | Tie Breaking |

```python
%%file /tmp/unionfind.p
cnf(ax1, axiom, a = b).
cnf(ax2, axiom, b = c).
cnf(ax3, axiom, c = d).
cnf(ax4, axiom, d = e).
cnf(ax5, axiom, f = g).

cnf(false, conjecture, true = false).
```

    Overwriting /tmp/unionfind.p

```python
!twee /tmp/unionfind.p
```

    Here is the input problem:
      Axiom 1 (ax5): f = g.
      Axiom 2 (ax1): a = b.
      Axiom 3 (ax2): b = c.
      Axiom 4 (ax4): d = e.
      Axiom 5 (ax3): c = d.
      Goal 1 (false): true = false.
    
    1. g -> f
    2. b -> a
    3. c -> a
    4. d -> e
    5. e -> a
    
    Ran out of critical pairs. This means the conjecture is not true.
    Here is the final rewrite system:
      b -> a
      c -> a
      d -> a
      e -> a
      g -> f
    
    RESULT: CounterSatisfiable (the conjecture is false).

{% raw %}

```python
import graphviz
def node(e):
    #print(e, e.get_id())
    return str(e.get_id())

def graphviz_of_z3(e, dot):
    #label = "<head>" + e.decl().name() + "| {" + "|".join([ f"<p{n}>{n}" for n in range(e.num_args())]) + "}"
    if e.num_args() == 0:
        label = f'{{<head>{e.decl().name()}}}'
    else:
        label = f'{{<head>{e.decl().name()}|{{{"|".join([f"<p{n}>" for n in range(e.num_args())])}}}}}'
    #print(label)
    dot.node(node(e), label, shape="Mrecord") # id?
    for n,c in enumerate(e.children()):
        a,b = node(e) + ":p" + str(n) , node(c) + ":head"
        if (a,b) not in dot.added_edges:
            dot.added_edges.add((a,b))
            dot.edge(a,b)
        graphviz_of_z3(c, dot)

def show_rewrite(R):
    dot = graphviz.Digraph()
    dot.added_edges = set()
    for l,r in R:

        dot.edge(node(l) + ":head", node(r) + ":head", style="dashed", color="red")
        graphviz_of_z3(l,dot)
        graphviz_of_z3(r,dot)
    return dot
from z3 import *
a,b,c,d,e,f,g = Consts("a b c d e f g", IntSort())
```

```python
R = [
    (b,a),
    (c,a),
    (d,a),
    (e,a),
    (g,f)
]
show_rewrite(R)
```

![svg](egraphs_talk_files/egraphs_talk_20_0.svg)

$$ b \rightarrow a $$
$$  c \rightarrow a $$
$$  d \rightarrow a $$
$$  e \rightarrow a $$
$$  g \rightarrow f $$

```python
%%file /tmp/unionfind.p
% Twee's "union find" is proof producing
cnf(ax1, axiom, a = b).
cnf(ax2, axiom, b = c).
cnf(ax3, axiom, c = d).
cnf(ax4, axiom, d = e).
cnf(ax5, axiom, f = g).

cnf(false, conjecture, a = e).
```

    Overwriting /tmp/unionfind.p

```python
!twee /tmp/unionfind.p
```

    Here is the input problem:
      Axiom 1 (ax5): f = g.
      Axiom 2 (ax1): a = b.
      Axiom 3 (ax2): b = c.
      Axiom 4 (ax3): c = d.
      Axiom 5 (ax4): d = e.
      Goal 1 (false): a = e.
    
    1. g -> f
    2. b -> a
    3. c -> a
    4. d -> a
    5. e -> a
    
    The conjecture is true! Here is a proof.
    
    Axiom 1 (ax1): a = b.
    Axiom 2 (ax2): b = c.
    Axiom 3 (ax3): c = d.
    Axiom 4 (ax4): d = e.
    
    Goal 1 (false): a = e.
    Proof:
      [32ma[m
    = [1m{ by axiom 1 (ax1) }[m
      [32mb[m
    = [1m{ by axiom 2 (ax2) }[m
      [32mc[m
    = [1m{ by axiom 3 (ax3) }[m
      [32md[m
    = [1m{ by axiom 4 (ax4) }[m
      e
    
    RESULT: Theorem (the conjecture is true).

{% endraw %}

# The Main Points of The Talk

- Simplification & Completion
- Union-find is Ground Atomic Completion
- <b>E-Graph is Ground Term Completion</b>
- ? is Lambda, Context, Destructive
- Compilers from Automated Reasoners

# E-Graph is Ground Term Completion

- Egraph = Completed Reduced Ground Rewrite System
- Ground completion "solves" ground equalities
- E-graph "solves" ground equalities

| TRS | Egraph |
|------|--------|
| Canonical Term | EClass |
| R/L-simplify | Canonization |
| Run Rules | Extract |
| Term Orders | Extract Objective |
| KBO Weights  |  Weights |

```python
%%file /tmp/groundshift.p
fof(shift, axiom, mul(a,two) = shift(a, one)).
fof(assoc, axiom, div(mul(a,two),two) = mul(a,div(two,two))).
fof(cancel, axiom, div(two,two) = one).
fof(unit_mul, axiom, mul(a,one) = a). 
fof(cancel, axiom, start_term(q,q,q,q,q,q,q) = div(mul(a,two), two)).

fof(goal, conjecture, true = false).
```

    Overwriting /tmp/groundshift.p

```python
!twee /tmp/groundshift.p
```

    Here is the input problem:
      Axiom 1 (cancel): div(two, two) = one.
      Axiom 2 (unit_mul): mul(a, one) = a.
      Axiom 3 (shift): mul(a, two) = shift(a, one).
      Axiom 4 (assoc): div(mul(a, two), two) = mul(a, div(two, two)).
      Axiom 5 (cancel): start_term(q, q, q, q, q, q, q) = div(mul(a, two), two).
      Goal 1 (goal): true = false.
    
    1. div(two, two) -> one
    2. mul(a, one) -> a
    3. mul(a, two) -> shift(a, one)
    4. div(shift(a, one), two) -> a
    5. start_term(q, q, q, q, q, q, q) -> a
    
    Ran out of critical pairs. This means the conjecture is not true.
    Here is the final rewrite system:
      mul(a, two) -> shift(a, one)
      mul(a, one) -> a
      div(two, two) -> one
      div(shift(a, one), two) -> a
      start_term(q, q, q, q, q, q, q) -> a
    
    RESULT: CounterSatisfiable (the conjecture is false).

```python
BV = DeclareSort("BV")
mul = Function("*", BV, BV, BV)
shift = Function("\<\<", BV, BV, BV)
div = Function("/", BV, BV, BV)
a,one,two= Consts("a 1 2", BV)
start = Const("start", BV)
R = [
  (mul(a, two) , shift(a, one)),
  (mul(a, one) , a),
  (div(two, two) , one),
  (div(shift(a, one), two) , a),
  #(start , a)
]
from IPython.display import SVG, display
display(show_rewrite(R))
show_rewrite(R).render("./egraph2.txt")
display(SVG(filename="./egraphs_1.svg"))
```

![svg](egraphs_talk_files/egraphs_talk_29_0.svg)

![svg](egraphs_talk_files/egraphs_talk_29_1.svg)

# WAKEUP! THE MOST IMPORTANT SLIDE

<center> <img src="./egraph2.svg">
<img src="./egraphs_1.svg">
</center>

$$  mul(a, two) \rightarrow shift(a, one) $$
$$  mul(a, one) \rightarrow a $$
$$ div(two, two) \rightarrow one $$
$$  div(shift(a, one), two) \rightarrow a $$

# Where are the E-classes and E-nodes?

- Flattening
  - Introduce fresh constants for every term
  - Make them less in term ordering

$$foo(biz(baz), bar) = bar$$

---------------------

$$bar = e1$$
$$baz = e2$$
$$biz(e2) = e3$$
$$foo(e3,e1) = e4$$
$$e4 = e1$$

$$foo(biz(baz), bar) = bar$$

----------------------

$$bar \rightarrow e1$$

$$baz \rightarrow e2$$

$$biz(e2) \rightarrow  e3$$

$$foo(e3,e1) \rightarrow e4$$

$$e4 \rightarrow e1$$

- Two types of rules
  - $foo(e7,e4) \rightarrow e1$ = enode table
  - $e3 \rightarrow e1$ = union find
- Observations:
  - _Not_ obviously possible for scoped terms. Slots? $e1(X,Y)$
  - Completion _is_ an egraph with Universal (forall) variables / first class rules
  - Tree Automata $cons(q1, q2) \rightarrow q2$

# E-matching

- Equality saturation
  - E-match into egraphs
  - Add new equality
- Run rules in reverse to generate all equivalent terms
- Top down and bottom up

## Bottom up E-matching

- The simplest e-matching algorithm
  - Completely guess each pattern var
  - Build term corresponding to pattern
- Plays nicer
  - Theories (Commutativity via sorting)
  - Containers
  - Grobner bases?
  - Destructive rules?
- Perhaps related to aegraph

# Strategies

 $\frac{A \lor B \quad \neg A \lor C}{B \lor C} $

- Incomplete but pragmatic limitations on resolution
  - Set of Support - Rules vs EGraph
  - Prolog
  - Datalog ~ Hyperresolution + UR-resolution

| Prop | Equational |
|------|------------|
| Resolution     |   Paramodulation         |
| Ordered Resolution | Superposition |
| ?  | Completion |
| Ground Ordered Resolution | E-graph / Ground Completion / Ground Superposition |
| Prolog | Functional Logic Programming |
| Datalog | Egglog |
| ASP | ? |
| Lambda Prolog | ? |
| Hypothetical Datalog | ? |
| Minikanren | ? |

# The Main Points of The Talk

- Simplification & Completion
- Union-find is Ground Atomic Completion
- E-Graph is Ground Term Completion
- <b>? is Lambda, Context, Destructive</b>
- Compilers from Automated Reasoners

# Mysteries and Promises

- Context
- Lambdas
- Destructive

# Context

- Twee
  - Efficient encodings of first-order Horn formulas in equational logic - Claessen & Smallbone
  - In Twee today.
  - Similar to ASSUME nodes
- Ground Superposition _is_ a contextual egraph
  - Negative literal ~ context
  - Terminating but possibly explosive

$$\frac{s \approx t \quad \neg u \approx v \lor R}{\neg u[s / t] \approx v \lor R}$$

$$\frac{s \approx t \quad u \approx v \implies R}{ u[s / t] \approx v \implies R}$$

[E – A Brainiac Theorem Prover](https://wwwlehre.dhbw-stuttgart.de/~sschulz/PAPERS/Schulz-AICOM-2002.pdf)

# Lambda

- Complete and Efficient Higher-Order Reasoning via Lambda-Superposition - Alexander Bentkamp, Jasmin Blanchette, Visa Nummelin, Sophie Tourret, and Uwe Waldmann
  - Zipperposition and E
- A Combinator-Based Superposition Calculus for Higher-Order Logic - Ahmed Bhayat, Giles Reger
  - Vampire
- Lambda Free Higher Order Logic (LFHOL)

# Destructive Rewriting

- Combination Problems (Chapter 9 TRAAT)
- Under what conditions does completion of Ground Eq + Rules stay well behaved?
  - Term Ordering of destructive rules probably informs how ground should work
- Two senses of "E-matching"

# The Main Points of The Talk

- Union find E-Graph $\leftrightarrow$ Ground Atomic Completion
- Clues: Lambda, Context, Destructive
- Automated Reasoning $\rightarrow$ Compilers
  - Fast Implementation?
  - Simplifier Oriented `Term -> Term`

# Thank You

- Abstract <https://github.com/philzook58/egraphs2024-talk/blob/main/egraphs2024.pdf>
- Blog posts:
  - <https://www.philipzucker.com/egraph-ground-rewrite/>
  - <https://www.philipzucker.com/ground-rewrite-2/>
  - <https://www.philipzucker.com/bottom_up/>
- References
  - Term Rewriting and All That (TRAAT)
  - Handbook of Automated Reasoning
  - Automated Reasoning: Introduction and Applications

```python
%%file /tmp/context.p
% Twee as a contexual egraph/union find
fof(shift, axiom, (a = b) => b = c).
fof(cancel, axiom, c = d ).
fof(cancel, axiom, e = f ).

fof(goa,conjecture, true = false).
```

    Overwriting /tmp/context.p

```python
!twee /tmp/context.p
```

    Here is the input problem:
      Axiom 1 (cancel): e = f.
      Axiom 2 (cancel): c = d.
      Axiom 3 (ifeq_axiom): ifeq(X, X, Y, Z) = Y.
      Axiom 4 (shift): ifeq(a, b, b, c) = c.
      Goal 1 (goa): true = false.
    
    1. f -> e
    2. c -> d
    3. ifeq(X, X, Y, Z) -> Y
    4. ifeq(a, b, b, d) -> d
    
    Ran out of critical pairs. This means the conjecture is not true.
    Here is the final rewrite system:
      c -> d
      f -> e
      ifeq(X, X, Y, Z) -> Y
      ifeq(a, b, b, d) -> d
    
    RESULT: CounterSatisfiable (the conjecture is false).

```python
def simplify1(x):
    match x:
        case ("add", ("const", m), ("const", n)):
            return ("const", m + n)
        case ("add", ("const", 0), y) | ("add", y, ("const", 0)):
            return y
        case _:
            return x
def simplify(expr):
    match expr:
        case ("add", x, y):
            return simplify1(("add", simplify(x), simplify(y)))
        case _:
            return simplify1(expr)
simplify(("add", ("const", 3), ("const", 4)))
```

    ('const', 7)

```python
class UF():
    def __init__(self):
        self.rules = {}
    def find(self, x):
        # `find` reduces x with respect to the current rules (x -R-> retval)
        while self.rules.get(x) != None:
            x = self.rules.get(x)
        return x
    def union(self, x, y):
        # Do incremental completion starting with
        # (E,R) == ({x = y}, self.rules )
        x1 = self.find(x) # SIMPLIFY  ( {x1 = y} , R)
        y1 = self.find(y) # SIMPLIFY  ( {x1 = y1}, R)
        if x1 == y1: # TRIVIAL ({x1 = x1}, R)
            return x1 # (Empty, self.rules)
        else:
            if x1 < y1: # the "term order"
                x1,y1 = y1,x1 # swap
            self.rules[x1] = y1 # ORIENT  (empty, R U {x1 -> y1})
            return y1
    def canon(self):
        for lhs,rhs in self.rules.items():
            self.rules[lhs] = self.find(rhs) # r-simplify
```

# Tree Automata

- Strings ~ single argument terms $aaabb = a(a(a(a(b(b(\epsilon))))))$
- Term rewriting formulation of DFA
  - $a^*b^* = \{a(q1) \rightarrow q1, a(q0) \rightarrow q1, b(q0) \rightarrow q0\}$
  - $a(a(a(a(b(b(q0)))))) \rightarrow^? q1$
- Generalizes to Tree. Finite State Folds
- Call $q1$ $e1$ and we have a flattened egraph

![](./res_cube.png)
Src: [Blanchette](https://events.model.in.tum.de/mod23/blanchette/Lecture3-Lambda-Superposition.pdf)

```python
%%file /tmp/groundshift.p
fof(e, axiom, a = e0).
fof(e, axiom, two = e1).
fof(e, axiom, mul(a,two) = e2).
fof(e, axiom, div(mul(a,two),two) = e3).
fof(e, axiom, one = e4).
fof(e, axiom, shift(a, one) = e5).
fof(e, axiom, div(two,two) = e6).
fof(e, axiom, mul(a, one) = e7).

fof(shift, axiom, mul(a,two) = shift(a, one)).
fof(assoc, axiom, div(mul(a,two),two) = mul(a,div(two,two))).
fof(cancel, axiom, div(two,two) = one).
fof(unit_mul, axiom, mul(a,one) = a). 
fof(cancel, axiom, start_term(q,q,q,q,q,q,q) = div(mul(a,two), two)).

fof(goal, conjecture, true = false).
```

    Overwriting /tmp/groundshift.p

```python
!twee /tmp/groundshift.p
```

    Here is the input problem:
      Axiom 1 (e): one = e4.
      Axiom 2 (e): a = e0.
      Axiom 3 (e): two = e1.
      Axiom 4 (e): shift(a, one) = e5.
      Axiom 5 (e): div(two, two) = e6.
      Axiom 6 (cancel): div(two, two) = one.
      Axiom 7 (e): mul(a, one) = e7.
      Axiom 8 (unit_mul): mul(a, one) = a.
      Axiom 9 (e): mul(a, two) = e2.
      Axiom 10 (shift): mul(a, two) = shift(a, one).
      Axiom 11 (e): div(mul(a, two), two) = e3.
      Axiom 12 (assoc): div(mul(a, two), two) = mul(a, div(two, two)).
      Axiom 13 (cancel): start_term(q, q, q, q, q, q, q) = div(mul(a, two), two).
      Goal 1 (goal): true = false.
    
    1. one -> e4
    2. a -> e0
    3. two -> e1
    4. shift(e0, e4) -> e5
    5. div(e1, e1) -> e6
    6. e6 -> e4
    7. mul(e0, e4) -> e7
    8. e7 -> e0
    9. mul(e0, e1) -> e2
    10. e5 -> e2
    11. div(e2, e1) -> e3
    12. e3 -> e0
    13. start_term(q, q, q, q, q, q, q) -> e0
    
    Ran out of critical pairs. This means the conjecture is not true.
    Here is the final rewrite system:
      a -> e0
      two -> e1
      e3 -> e0
      one -> e4
      e5 -> e2
      e6 -> e4
      e7 -> e0
      mul(e0, e1) -> e2
      mul(e0, e4) -> e0
      div(e1, e1) -> e4
      div(e2, e1) -> e0
      shift(e0, e4) -> e2
      start_term(q, q, q, q, q, q, q) -> e0
    
    RESULT: CounterSatisfiable (the conjecture is false).

```python
BV = DeclareSort("BV")
mul = Function("*", BV, BV, BV)
shift = Function("\<\<", BV, BV, BV)
div = Function("/", BV, BV, BV)
a,one,two= Consts("a 1 2", BV)
e0,e1,e2,e3,e4,e5,e6,e7 = Consts("e0 e1 e2 e3 e4 e5 e6 e7", BV)
start = Const("start", BV)
R = [
    (a, e0),
    (two, e1),
    (e3, e0),
    (one,e4),
    (e5,e2),
    (e6,e4),
    (e7,e0),
    (mul(e0,e1),e2),
    (mul(e0,e4), e0),
    (div(e1,e1),e4),
    (div(e2,e1), e0),
    (shift(e0,e4), e2),
    #(start, e0)
]
show_rewrite(R)
```

![svg](egraphs_talk_files/egraphs_talk_54_0.svg)

```python
%%file /tmp/shift.p
fof(shift, axiom, ![X] : mul(X,two) = shift(X, one)).

fof(assoc, axiom, ![X,Y,Z]: div(mul(X,Y), Z) = mul(X, div(Y,Z))).
fof(cancel, axiom, ![X]: div(X,X) = one).
fof(mul_one, axiom, ![X]: mul(X,one) = X).

fof(goal, conjecture, true = false).
```

    Overwriting /tmp/shift.p
