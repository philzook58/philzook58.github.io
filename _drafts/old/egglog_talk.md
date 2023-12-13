Hatching a Datalog: Horn Clauses Modulo Equality with Egg
Hatching a Datalog: Horn Clauses Modulo Congruence with Egg
Egglog0: Adapting Egraph Rewriting to Horn Clauses
Extending Egraphs
Datalogs are all around you
Egglog0: A prototype system for horn clauses modulo equality reasoning
Snappier titles:
EGGLOG NOW
I herd you like horn clauses, so i put them in your egraph
Everything is a datalog
The Hidden Datalog inside Egg
Hatching A datalog
Hatching a Datalog: Solving Horn Clasues Modulo Equality with Egg
in Egg
Hacking Horn Clauses Modulo Equality into Egg
contaminating egg with horn clauses
scrambling, frying, cracking, laying, poached, emulsifying,contaminating egg with horn clauses. salmonella, rotten. sulphur, eggnog, humpty dumpty souffle.
Poaching Egg: 
green eggs and ham, yolk,          white, duck, fish, protein,


member(X,cons(X,Xs)). % not a good example
member(Y, cons(X, Xs)) :- member(Y, Xs)

append(cons(), append, cons(X, ) :- append(, cons())

Multipatterns are distinct from term-rewriting guards in that they may bind new variables. Horn clauses are distinct from rewriting rules in that the is not an implicit equality between the head and body of a rule.

In Egglog0 there is no distinction between the storage of relations and terms. Because of this, stating a fact `add(a,b)` operationally corresponds to inserting the term into the e-graph.

It can also be usefully interpreted as an assertion of  truth that `add(a,b)` is a term, or an assertion that Socrates is human `human(socrates)`. The convinced of these interpretations depends on human stuff.

 `a(X) :- p(X), q(y), r(X)` logically corresponds to stating the axiom $ \forall x,  p(x) \land q(y) \land r(x) \rightarrow a(x) $, a subclass of formula known as Horn clauses.

Egglog0 has a prolog inspired syntax for stating Horn clause axioms with equality.


TODO: We can do better than this example
\begin{lstlisting}
y = x.
\end{lstlisting}

This relation can be used in clauses.

In terms of modelling, it is not always desirable to state a complete set of rules for how something can become true, both because one needs more rules and the e-graph will explode with unnecessary terms in many situations.

NOTE: It is not 100\% clear to me but I think this is how SMT works too. Predicates are modeled as boolean functions.


\section{Introduction}


% maybe just have a table here.

\section{Term Rewriting and Logic Programming}
I don't have space for this.

Explain why interesting predciates and terms are identified. This is odd but can also be useful.

NOTE: show multiheads?


In principle \lstinline{=} could be used in a `-+` mode, efficiently generating members of an eclass, however the details of the egg interface prevent this as a user of the library.

A related axiom is that describing the properties of projectors of a pair.

\begin{lstlisting}
pair(A,B) = Z :- proj1(Z) = A, proj2(Z) = B.
proj1(Z) = A, proj2(Z) = B :- pair(A,B) = Z.
\end{lstlisting}

From these rules, one can derive the computation rule
\begin{lstlisting}
Z <- pair(proj1(Z), proj2(Z)).
A  <- proj1(pair(A,B))
B <- proj2(pair(A,B))
\end{lstlisting}

However this rule is weaker and the left to right direction will never saturate and choke the e-graph with terms.
No I was missing the rule. Meh.

This is not a rewrite rule persay, but instead manipulating the equation itself. 

(or other truth values)

ot merely that is has been failed to so far be proven true

They are a method by which to model functional dependencies and foreign keys among other things.

 (alpha renaming if necessary)

$ \forall x_1, \ldots, x_n . \phi(x_1, ... , x_n) \rightarrow \psi(x_1, \ldots, x_n, y_1(x_1,\ldots,x_n),... y_m(x_1,\ldots,x_n))$

Which in turn is modellable in Egglog0 as

Under a logical reading pattern variables are implicitly universally quantified.

An additional useful trick is of queries.

Clauses are axioms, Queries can be thought of as theorems to be proved. Upfront backchaining of the logical query can allows are larger class of theorems to be exprssed in Egglog0. Universal quantifaction can be backchained into a fresh symbol generation and implication in the query can be backchained into new clauses and base facts.

SMT and ATP provers (exemplars of which are Z3 and Vampire) 

It can be nontrivial but useful to translate insights between them.
the worlds of term rewriting, logic programming, and databases.

he cross fertilization of these fields


$$\forall x_1, ..., x_2 . \psi(x_1, ... , x_n) \implies \exists! y_1,\cdots,y_m, \psi(y_1,... y_m) $$

$$\forall x_1, ..., x_2 . \psi(x_1, ... , x_n) \implies \exists y1,..,ym \psi(y_1,... y_m)
 \land \forall x_1, ..., x_n, y1,..,ym, x'_1, ..., x'_n, y'1,..,y'm,  . \psi(x_1, ... , x_n) \land \psi(y_1,... y_m) \land \psi(x_1, ... , x_n) \land \psi(y_1,... y_m) \rightarrow y_1 = y'_1 \land .... \land y_m = y'_m 
 $$

 Here we also see the multiple heads feature of Egglog0, which performs both heads effects upon a successful multipattern match from the body.


As an example, a monoidal category has morphisms of type Hom(a,b),
TODO: possibly talk about kronecker product rewriting

If you don't need to bind new variables, you can get away with guards.
The rewriting paradigm requires a special term on the left and right hand side.


# Rewrite Rules and Horns Clauses
There are many striking similarities between the worlds of term rewriting and logic programming (and databases). It can be nontrivial but useful to translate insights between them.

For many term rewriting systems, the actual behavior depends strongly upon the ordering of the rules. This is known in the compiler community as the phase ordering problem. A common approach is to attempt to complete a system of rewrite rules to guarantee termination and confluence, but this often difficult and in general impossible. Equality saturation using egraphs is a compelling technique for term rewriting because of it's declarative and monotonic nature. Equality saturation proceeds monotonically, never forgetting previously discovered equalities.

There is a similar difficulty in the realm of logic programming. Prolog eagerly attempts to resolve it's goal stack on its program clauses in order, but this can lead to infinite loops without care. The incompleteness of prolog search can be ameliorated in a few ways. One is to use tabled logic programming (SLG resolution) which memoizes already seen queries, another direction is to use a complete search like minikanren or iterative deepening.

While it may not be surprising given that both term rewriting and logic programming are such powerful frameworks, it is not difficult to model them with each other.
A rewrite rule $ l \rightarrow r $ can be turned into a clause.
```
term(l) :- term(r)
```

Likewise, SLD resolution can be modelled as rewrite rules of terms that explicitly contain the goal stack. The only complication is dealing with associativity of

```prolog
a :- p,q,r,...
```

$$
a \rightarrow cons(p,cons(q,r))
cons(cons(a,b),c) \rightarrow cons(a,cons(b,c))
$$

Rewrite rules are often implemented without backtracking semantics.
Is this even right? Don't we need unification which rewrite rules don't typically offer?

pattern matching vs unification

More similairites:
- Z3 e-matching machine has a great deal of the flavor of a Relation Abstract Machine RAM and to a lesser degree a Warren Abstract Machine
The abstract machine of ematching [bjorner and de moura] is quite similar to the relational abstract machine. Partially, this is just that all abstract machine in the PL , but both are also imperative search engines. The relational e-matching paper demonstrates this point by taking the viewpoint that the pattern matching over an egraph can be fruitfully implemented under a database lens.
- One relationship between rewrite rules and Horn clauses is SLD resolution.
SLD resolution can be considered as a rewriting system on the goal state.
Alternatively bottom up evaluation can be considered a rewriting system.

l -> r | term(l) :- term(r)
p -> {q,r,s}  | p :- q, r, s
ematchign machine | WAM RAM
Equality saturation | Fixpoint Semantics

There are multiple approaches to how to deal with the nondeterminism available from the choice of rewrite rule or horn clause.
Some systems perform destructive rewrites (mathematica, Symbolics.jl, linear prolog), others perform backtracking search (prolog, minikanren), and others maintain and expanding set of all reachable states (egg, datalog).

This talk is about the extended modelling power equality saturation gains have when extended with logic programming constructs and a prototype implementation Egglog0 built upon the e-graph framework library egg.

### Datalog
Datalog is often considered as being back by the equivalent of a traditional indexed database. It is however agnostic in many respects to it's backing store. This is seen for example in bddbddbdd which uses binary decision diagrams.

There is no universal definition of what the term Datalog may mean.
- only simple constants allowed, not term trees. This guarantees termination of datalog programs.
- stratified uses of negation
- Every variable in the head of a clause must be bound in the body
- Bottom up evaluation

The first is sometimes considered the most vital characteristic of datalog, and yet it can be fruitfully dropped. Indeed many datalog systems do allow terms.

By flattening, terms can be desugared into relations with one essential extra feature: the ability to produce fresh identifiers when a term has not previously appeared.

# Egglog0

Egglog0 is a prototype system built around the egg equality saturation library. It is designed to extend egg with multipatterns and bring the forefront the logical view of the system.
Multipatterns are distinct from guards in that they may bind new variables.

In Egglog0 there is no distinction between the storage of relations and terms. Because of this, stating a fact `add(a,b)` operationally corresponds to inserting the term into the egraph.

```prolog
/* Base egraph insertions. No implied equalities. For "seeding" the egraph. */
f(x).
bar(boo).
plus(p,r).
```

It can also be usefully interpreted as an assertion of  truth that `add(a,b)` is a term, or an assertion that Socrates is human `human(socrates)`. The convinced of these interpretations depends on human stuff.

Clauses are represented using prolog convention of capitalized names for variables. `a(X) :- p(X), q(y), r(X)` logically corresponds to stating the axiom $ \forall x,  p(x) \land q(y) \land r(x) \rightarrow a(x)`, a subclass of formula known as Horn clauses.

```prolog
path(X, Y) :- edge(X, Y).
path(X, Y) :- path(X, Z), edge(Z, Y).
edge(a,b).
edge(b,c).
```

Operationally a tern appear on the right is a multipattern to seek in the egraph. A ground term on the right is built and inserted into the egraph by      instantiating the variables.
Multiple heads are allowed, an correspond to the applying both possible heads in parallel. In the logical reading, multiple heads are the conjunction of heads.

```
multiheadexample
```

So far the egraph has not been used in any intrinsic way. This subset of the language, "hashlog", could be implemented by a backing hash cons data structure instead.

There is a special built in relation `=` denoting egraph equality. Base facts may be inserted into the egraph.
```prolog
/* Base equality facts */
y = x.
z = y.
```
Operationally, an `=` the body corresponds to a check that the patterns were found in the same class,
in the head of a clause correspond to called `union!` on two eclasses of the consturcted terms. In principle `=` could be used in a `-+` mode, efficiently generating members of an eclass, however the details of the egg interface prevent this as a user of the library.

Rewrite rules can be encoded as horn clauses. Pattern variables do not bind to terms, they bind the eclasses.

```
add(Y,X) = E :- add(X,Y) = E
```

Because standard equality saturation is a common use case, there is custom syntax sugar for it.

```prolog
/* rewrite rules. Variables denoted by capitalization */
plus(X,Y) <- plus(Y,X).

/* bidirectional rewrite. A useful syntactic shorthand for two rewrite rules. */
plus(X,plus(Y,Z)) <-> plus(plus(X,Y),Z).

/* Guarded rewrite. Maybe just don't talk about this. */
fiz(baz) <- bar(boo), x = z.
```

Finally, as a simple but limited mechanism to recover information out to the egraph, there are queries. Queries are run after termination of the equality saturation after hitting saturation or a variety of limits. They are very simply implemented via the exact same mechanism as the body pattern matchers. A subtition dictionary of variables to eclasses is returned. To print out a concrete ground term, the choice is made to use eggs built in extractor which selects a small representative term out of the eclass.

```prolog
?- f(x) = x.
?- add(x,y) = z, add(b,x) = q /* multipattern query */
?- x = x.
?- y = x.
?- plus(p,r) = plus(r,p).
?- junk(boo) = otherjunk(baz).
```


## Implementation
egg is an e-graph library optimized for equality saturation. Because of this, the abstractions offered are slightly awkward for the purposes of horn clause searching. Without changing the implementation of the library is is impossible to implement egglog search in an efficient way.

Searcher
Applier

The basic data returns by a `Searcher` is a `Subst`. Substitions are a mapping from pattern variables to eclass ids. Substitions can be combined and check for consistency.
Egglog `MultiPatterns` run an ordinary ematching search using conventional `egg` e-matching and merge the returned susbtitions. If this merging succeeds it sends the result to the `Applier`

In equality saturation, the intent is that the Applier will construct a new term using bindings from the `Subst`, and then assert equality between this term and the toplevel term of the pattern. This is not the result desired from the head of horn clauses. The head may either be an atom or a usage of the built in `=` predicate. In either case the appropriate instantiated terms are constructed. In the case of the `=` predicate these two terms are asserted equal. In contrast to rewriting, these terms set equal may have very little relation to the terms appearing in body.

The toplevel loop compiles the terms into a set of egg `Rewrite` objects, runs the stock egg quality saturation to a timeout, and then applies the queries to the resulting egraph.

Queries are operationally identical to the bodies of clauses. They are implemented as Searchers and all the resulting `Substs` are printed.

# Expressivity
## Equality Generating Dependencies, Tuple Generating Dependencies

## Injectivity
```
x = y, xs = ys :- cons(x,xs) = cons(y,ys)
```

Another amusing example of multipatterns / egglog. Something like eta conversion of pairs
```
pair(A,B) = Z :- proj1(Z) = A, proj2(Z) = B.
proj1(Z) = A, proj2(Z) = B :- pair(A,B) = Z.

//Why not
pair(proj1(z), proj2(z)) -> z
// because the other direction is horrible
```
## Reflection
While the mere presence of "predocate" terms in the egraph database can be considered as an assertion of their truth, an different embedded method ollows one to manipulation and talk about predicates in the absence of a priori knowledge of their truth. Preidcate can be modelled as functions into `Bool`. The existance of a predicate term in the same eclass as `true` is then seen as evidence of it's truth. More interestingly, the existence of being in the same eclass as `false` can be seen as evidence that the predciate has detemined not to be true. The analog of the lack of a predicate in the egraph cannot be seen as evidence of it's falsehood. Equality saturation as a reasoning tool has constructive character in this sense. This is the analog of the situation in datalog implementations, where negation may only be considered in the presence of a stratification. In terms of modelling, it is not always desirable to state a complete set of rules for how something can become true, both because one needs more rules and the egraph will explode with unnecessary terms in many situations.

note: It is not 100% clear to me but I think this is how SMT works too. Predicates are modelled as boolean functions.

`true` `false`
```
eq(a,b) = true :- a = b
a = b :- eq(a,b) = true
```

## Equation Solving
y = sub(z,x) :- add(x,y) = z

## Matrix Rewriting
Hmm. Maybe this one is ok. Oh no. Because we need rewriting on n possibly.
 :- kron( A, B) dot kron(C,D), rows(A) = plus(n, ),   ,rows,  ,   

## Generalized Algebraic Theories
generalized algebraic theories. [catlab and whatsies. the GAT guy]

Algerbaic theories are those described by equational axioms. Generalized algebraic theories introduce a limited version of dependent types. The types also have an equational theory and the equational axioms only hold between terms of the same type. 

As an example, a monoidal category has morphisms of type Hom(a,b)

The typing requirements of a GAT axiom naturally map to horn clauses. It is possible to build an encoding using type tagging and guards rather than multipatterns, but it is extremely burdensome and inefficient.


https://julialang.zulipchat.com/#narrow/stream/230248-catlab.2Ejl/topic/Getting.20started/near/232361036
https://julialang.zulipchat.com/#narrow/stream/230248-catlab.2Ejl/topic/Automatic.20Theorem.20Proving/near/207926668

Indeed it was building a reasoning system for Catlab.jl which is based around the concept of GATs that the present work was derived.

## Type derivations
Vec<n> example
"dependent types" 



## Comparison with SMT solvers, Prolog, those CHR things

## Comparison with Souffle



# Future Work




# Monotonicity, Lattices, and Saturation
The semantics of 


Theorem proving vs eq sat. Retruning sat vs unsat compared to returning proofs vs returning "query data". Vs extracting.
Extaction and Analsysis
Egglog0 focused on the term representation. The extraction chosen is a simple smallest term representation. Even in the context of terms other extractions may be desirable.
Flags could change the extraction mode. This is unsatisfying. It is desirable for user programmable extraction.




# Acknowledgements

Yihong Zhang
Remy 
Max Willsey
Zach Tatlock
Alessandro Cheli
Cody Roux




Patterns are terms with named holes
Substitutions are a mapping from pattern variables to terms Map PVar Term
Pattern matching over a term is a function Term -> Pattern -> Subst
Complete pattern matching over a term is Term -> Pattern -> [Subst]
One semantics of what egraphs represent is a partition of terms


Multipatterns [Pattern] are a sequence of patterns
The bodies of clauses almost correspond to multipatterns, except for the one special relation of equality, which corresponds to egraph equality.

Guards :: Subst -> Bool


Guards


There are a number of very striking similarities between theory, algorithms, and implementation of the worlds of term rewriting and logic programming. Both realms are often turing complete and strongly influenced by the traditions of mathematics and logic.


The guarantees are both a gift and curse. It allows human cleverness to be injected into the system and achieve great feats, but it compromises on the logical declarative roots of the language.


 e-graph rewriting