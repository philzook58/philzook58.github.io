---
date: 2022-11-25
layout: post
title: "Datalog as a Theorem Prover: Harrop Clauses-lite"
description: 
tags: datalog
---

Datalog is a really cool technology because it is both declarative, intuitive and high performance. The core algorithms can be accomplished using database technology for queries, which has become very refined ovr the years.

Datalog is a relative of prolog. Prolog programs are Horn clauses, which can be considered a subset of first order logic.

Datalog as a theorem prover is discussed even less than prolog's character as a theorem prover.
The Nadathur and Miller book [Programming with Higher Order Logic](https://www.google.com/books/edition/Programming_with_Higher_Order_Logic/xKsgAwAAQBAJ?hl=en&gbpv=1&printsec=frontcover) has an excellent discussion of the logical semantics of prolog. This book is a classic. It is a book so rich with insight, I'm hard pressed to think of book that it is's equal.

This blog post is trying to illuminate in the style presented in the book the class of formulas that datalog is a prover for. 

I actually kind personally de-emphasize this perspective. Instead I like the think of datalog/prolog rules as corresponding to inference rules (the horizontal line) and datalog/prolog predicates correspond to judgements. See these [Pfenning notes](https://www.cs.cmu.edu/~fp/courses/15317-f17/lectures/18-datalog.pdf).
Datalog is an engine for breadth first exploration of forward inferences. Every piece of knowledge that datalog asserts is _justified_. One can extract a judgemental proof tree for any fact derived by a datalog execution using some lightweight extra tagging. This is in distinction to traditional resolution based theorem provers or SMT solvers which have a much more classical bent. They can make guesses. Datalog has a more constructive feel from this perspective.
From a pragmatic standpoint, every datalog operation has an operational as well as logical character. Only inferring justifiable rules enables the datalog inference process to be more predictable and controllable in my experience than classical solvers. Perhaps as Zach put it "You can play computer".


# Horn Clauses and Prolog
Prolog works via what can be described as top-down, backwards, or goal-directed inference, trying to construct a proof tree backwards from a given goal.

One presentation of Horn clauses is (Section 2.3)

```
G ::= Top | A | G ∧ G | G ∨ G | ∃τ x G
D ::= A | G ⊃ D | D ∧ D | ∀x, D
```

[Bounded Quantifiers](https://en.wikipedia.org/wiki/Bounded_quantifier)
bounded quantification

An operational interpretation can be given to the sequents in prolog.

The state of a prolog interpreter can be represented as
`P ; S |- G`
where G is the goal, P is the clause database and S is the signature of constants in scope.

Really a list of these, which represent the current leaves of a partially constructed proof tree.

Breaking down a compound goal is automatic and does not represent a backtracking step. These rules are invertible https://www.cs.cmu.edu/~fp/courses/oregon-m10/04-focusing.pdf, meaning we have not committed to a possibly bad thing by taking them.

`P ; S |- G1 /\ G1` --> prove `P ; S |- G1` and then `P ; S |- G2`


```
`P ; S |- G1`           P ; S |- G2
----------------------------------- /\ R (I?)
        P ; S |- G1 /\ G1`  
```

`P ; S |- G1 \/ G1` --> try proving `P ; S |- G1` and if that doesn't work try `P ; S |- G2`

`P ; S |- exists X, G` introduce a fresh unification/metavariable X. 

There is something a bit weird about not tracking existential metavariables in the sequent. They allow spooky action at a distance in the proof search, which can be disconcerting. Minikanren is more explicit on this point, purely functionally carrying a substitition dictionary.

Prolog for free will prove a stronger theorem than the one asked for. A metavariable in the answer represents a universal quantification when all you asked for as an existential one. This is very cool.

A subtle point. If the answer is ungrounded, this is proving a universal quantification, but a universal only proves an existential if the sort in question is non empty, so actually it is returning a stronger theorem and a proof obligation for non emptiness.  In the unityped setting this is less apparent.

# Harrop Clauses
 
There is an extension of horn clauses called hereditary Harrop clauses which also have an operational character. [Lambda prolog](https://www.lix.polytechnique.fr/~dale/lProlog/) directly supports these. Enriching the set of formula you support is good. 


```
G ::= True | A | G ∧ G | G ∨ G | ∃τ x G | D ⊃ G | ∀x G
D ::= A | G ⊃ D | D ∧ D | ∀x D
```

The additions compared to the above Horn clause structure is implication and forall are allowed in the goal formula.

`P ; S |- D -> G` puts a new program clause into the database ` (D :: P) ; S |- G`. 

`P ; S |- forall x, G` introduce a new fresh constant `P ; (x :: S) |- G`

We can see that implication and forall are related. In dependent type theory implication is just a forall where you ignore the argument in the rest of the type `A -> B = forall x : A, B`. Likewise bounded quantification $\forall_S x, P$ can be usefully expanded as $\forall x, S => P$ when you are modeling this construct in a first order theorem prover.

What's really beautiful and powerful seeming is that the program and goal formulas are mutually recursively defined. There is a certain symmetry.

The forall rule also gives us a principled way to generate well scoped fresh names. This interplays with lambda prolog's ability to talk about lambda terms, which I won't touch on further today.

# Backchaining
The above rules break down the goal formula, but eventually it becomes atomic. What then?
Then comes the backchaining phase where the logic program selects a rogram clause to resolve against the goal.


Prolog's default depth first search strategy hurts it's character as a theorem prover. There is much to be gained from this convention, as it increases it's predictable character as a operational programming language.

Datalog is superior on this count. It breadth first searches trough forward inference and cannot get caught digging down as dusty alley. 
# Datalog


Datalog does not support either of these.
Datalog does not support Horn clauses in the sense described above. "Outrage!" you scream at me, readying to tear me apart limb from limb. 

What does datalog support.
We can assert `A` as a fact. 
We can assert rules. Logically speaking, these are similar to statements of `forall a, (exists b, G) => D` but only if the variable in D are bound in G. This is a subtle distinction for which I am not aware of a readily available comparable logical notion.

What kind of queries can we make? Essentially conjunctive queries. We can run the rules up until a goal condition is satisfied

We can support a priori bounded universal quantification.

# Bounded Horn Clauses
```
G ::= Top | A | G ∧ G | G ∨ G | ∃τ x G
D ::= A | G ⊃ D | D ∧ D | ∀x:bounds, D
```

In a sense, the requirement of needing a G is


```
G ::= Top | A | G ∧ G | G ∨ G | ∃τ x, G
D ::= A | G ⊃ D | D ∧ D | ∀x y z..:A, D
```

where G is a formula that grounds the variables being introduced.
(Hmm. But is it ok tht G includes \/? The DNF expansion must include the variables being introduced.
So undert more complicated conditions that A can become a 
The bounds can also be a primitive enumerator like `range` or `nats`.
Using A is a bummer because 
`forall x (b(x) \/ c(x)), q(x)` is fine but we have to reformulate it as `forall x: b(x), q(x) /\ forall x: c(x), q(x)`


)

This is all basically non surprising.

D formula can be expanded into a normal form expected by a typical datalog engine.

Souffle datalog supports the or operator in rule bodys `;` and multiheaded rules

Goals G can be expanded into 

```souffle
// exists x, g(x)
proven() :- g(_x).

// G1 /\ G2
proven() :- g1, g2.

// G1 \/ G2
proven() :- g1.
proven() :- g2.
// or identically
proven() :- g1; g2.
```

```
D1 /\ D2 :- G    --> {D2 :- G, D2 :- G}
D :- (G1 \/ G2)  --> {D :- G1, D :- G2} 
D :- (exists x, G1) --> {D :- G1}
D :- (G1 /\ G2) --> {D :- G1, G2}
```


# Harrop-Lite

This is essentially the set of formula that can be operationally interpreted in datalog without too much agony. By agony, I mean with the true bulk search occuring in the datalog engine itself and where the proving process proceeds va generative metaprogramming and not deeper matching on the structure of the program clauses.

We stratify goals into two kinds. One is in essence the same as it appears in horn clauses, and one is how goals appear in horn clauses.

```
G ::= PG | G ∧ G | G ∨ G | ∃x G | D ⊃ G | ∀x G
D ::= A | D ∧ D | ∀x..:PG, D
PG ::= True | A | PG ∧ PG | PG ∨ PG | ∃x PG
```

`G /\ G` is dealt with by forking the database into two process and waiting for both to come back true.
`G \/ G` is dealt with by forking the database search into two processes and seeing if one comes back proven
`D -> G` can be backchained by inserting the clause D into the datalog program.
`∀x G` can be dealt with by creating a fresh constant and instantiating it in the formua.



The truth values aren't booleans. The two values are unknown and proven, not true and false. They are like Marshall B's sierpinski trth values

`CoInductive Sierp := Unsure Sierp | Proven.`

```python
def goldbach():
    i = 4
    while True:
        i += 2 # even numbers
        for j in range(i):
            if isprime(j) and isprime(j - i):
                return True
        yield None

```


# Existentials and Skolemization and Egglog


```
G ::= Q | G ∧ G | G ∨ G | ∃x G | D ⊃ G | ∀x G
D ::= A | D ∧ D | ∀x..:PG, D | ∃x D
Q ::= True | A | Q ∧ Q | Q ∨ Q | ∃x Q
```

A bottom up technique 

Each one of these additions is hard fought.



A gensym or autoinc counter can be used to invent new symbols.
Significantly better is to use skolem functions. These essentially record the reason by .
What is weak or subtly undesirable about this is that creating a skolem function as a _datatype_ is that the existential doesn't guarantee a new thing. There may be something that already exists to satisfy the need of the existential.
It also is somewhat implying that there is a unique element that satisfies the existential. This is why we can't use egglog union to "delete" the skolem.
It is not easy to tell when you can soundly assume the outputs of the skolem function are != from other types.




These are rules that are called tuple generating and equality generating in the database community. They can be used to specify functional dependencies.
a = b :- f(x,a), f(x,b).
f(x,a) != :- a != b. // coinductive rule


# Is that it?
No, but this is the core of what you can prove using a stock datalog. Going beyond that requires funky features or weird encodings and it appears thus far that the farther you go afield the 

Contextual datalog / hypothetical datalog / scoped datalog.
https://www.philipzucker.com/contextual-datalog/
[Implementing Tabled Hypothetical Datalog](http://www.fdi.ucm.es/profesor/fernan/FSP/Sae13c.pdf)

Support higher order constructs.
Curried rules can be supported in a different way via defining new predciates.
There's kind f a cute normal form for datalog programs of binary lcayses. Ths presuppose a query ordering, which maye be indesirable since a benefit of the datalog approach is to have big queries that the database has descided how to break up.

Egglog supports an intrinsic notion of equality. It is a presentational choice to decide whether equaliy is part of the logic or not. It is such an important notion it often is.

slog 