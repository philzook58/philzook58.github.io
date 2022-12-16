---
layout: post
title: Automata, Regex, Coinduction, Bisimulation
---

- [Regular Expressions](#regular-expressions)
    - [Matching algorithms](#matching-algorithms)
    - [equivalence](#equivalence)
    - [theory](#theory)
  - [Automata](#automata)
- [Kleene Algebra](#kleene-algebra)
  - [KAT](#kat)
- [Bisimulation](#bisimulation)
  - [Codata](#codata)
  - [Coalgebra](#coalgebra)
  - [Coinduction](#coinduction)


See also:
- automata
- regular expression
- imperative proving
- model checking

Breaking up into these categories is kind of arbitrary

# Regular Expressions
See also note on automata

https://en.wikipedia.org/wiki/Regular_expression

https://regex101.com/
https://regexr.com/

https://en.wikipedia.org/wiki/Kleene%27s_algorithm
https://en.wikipedia.org/wiki/Thompson%27s_construction
https://en.wikipedia.org/wiki/Glushkov%27s_construction_algorithm
Finding minimum regex for given string (or set of strings). Identify groups within a given string https://cs.stackexchange.com/questions/109583/what-is-the-best-algorithm-known-to-learn-the-regular-expression-from-a-set-of-p  Is this related to invariant inference I wonder?


Knuth morris pratt
regular expression rewriting or optimization. Slightly difference from equivalence but related. Minimization https://cs.stackexchange.com/questions/115739/algorithm-to-minimize-a-regular-expression?rq=1


Z3 checking regex containment https://www.philipzucker.com/z3-rise4fun/sequences.html
https://microsoft.github.io/z3guide/docs/theories/Regular%20Expressions
[An SMT Solver for Regular Expressions and Linear Arithmetic over String Length cav'21](https://people.eecs.berkeley.edu/~fmora/cav21.pdf)
```z3
(declare-const a String)
;(assert (str.in.re "ab" (str.to.re "ab")))
(assert-not (str.in.re a (str.to.re "ab")))
(assert (str.in.re a (re.++ (str.to.re "a") (re.++ (re.* (str.to.re "b"))))))


(check-sat)
(get-model)
```

### Matching algorithms
- backtracking search
- convert to dfa
Brzozowski derivatives https://www.ccs.neu.edu/home/turon/re-deriv.pdf

Matching is state inference perhaps of traces.

https://types.pl/web/@maxsnew/109422022028474251 Regular Expressions : Logic Programming :: DFA : Functional Programming 
### equivalence
regex equivalence can check containment of string. also regex containmnt a + b = a means b  <= a 
https://www.drmaciver.com/2016/12/proving-or-refuting-regular-expression-equivalence/
one he says do the dumb rewrite rules.
hmm. We could egglog these hopcroft karp examples.

See kleene algebra. This is an equational method for equivalence checking of regex expressions 

Normal Forms are usually a good way of checking equivalence when you can. Automata are kind of a normal form

### theory
[pumping lemma](https://en.wikipedia.org/wiki/Pumping_lemma_for_regular_languages) used to prove languages are not regular
Whenever a sufficiently long string is accepted it must be in the same state twice
Find an inifnite family of string that isn't pumpable

myhill nerode theorem https://en.wikipedia.org/wiki/Myhill%E2%80%93Nerode_theorem necessary and sufficient condition for languasge to be regular
define an equivalence relation. Sort of this relation is defining a notion of observably different traces.
If there is no suffix z where xz fails but yz accepts or vice versa, the strings x y are considered equivalent.
These equivalence classes correspond to states in a minimal automata. Given the classes, I can append letters to them to find the transitions between classes. By the definition all the elements in the class have to go to the same other class, because they can't be distinguished

characterizing
NFA <-> DFA <-> regexp <-> regular grammars

https://en.wikipedia.org/wiki/Regular_grammar left regular or right regular. Linear production rules + always has to be on the left or right. swapping left and right may not be regular anymore. Regular grammar nonterminals can be considered states in an NFA


kleene algerba


"In 1991, Dexter Kozen axiomatized regular expressions as a Kleene algebra, using equational and Horn clause axioms.[34] Already in 1964, Redko had proved that no finite set of purely equational axioms can characterize the algebra of regular languages.[35]"

powerset construction


[proof pearl regular expressions isabelle](https://www21.in.tum.de/~krauss/papers/rexp.pdf)


MOnadic second order logic


## Automata
See also note on Parsing regularexp

Determinization - turn nondeterministic automaton to deterministic


https://github.com/ondrik/libvata
[Tree Automata Techniques and Applications](https://jacquema.gitlabpages.inria.fr/files/tata.pdf)


[E-Graphs, VSAs, and Tree Automata: a Rosetta Stone](https://remy.wang/reports/dfta.pdf) [slides](https://docs.google.com/presentation/d/1oDNmzxJpsdLE51lmybcfzzzv4jRLDdrVpmMhMpFEoFk/edit?usp=sharing) [merge only rules](https://gist.github.com/remysucre/1788cf0153d7db240e751fb698f74d99)


https://en.wikipedia.org/wiki/Tree_automaton



Computing regex from automata
Kleene's algorithm
Tarjan's algorithm
Basic algorithm of going back an forth is simple.
Consider edges to be labelable by regexs. regex is equal to simple 2 state automata then with 1 edge
You can eliminate states by performing the product of their in and out edges.
You can create states and edges by expanding the regexp. Sequence is a new intermiedtae state. alternate is two parall arrows


Myhill Nerode theorem
Pumping Lemma


Automata minimization https://en.wikipedia.org/wiki/DFA_minimization - Partition refinement https://en.wikipedia.org/wiki/Partition_refinement
Separate into separate sets those which are definitely distinguishable (the remaining in same partition may or may not be). Things that transition into distinguishable things are distinguishable from each other. This is finding the nerode congruence


Datalog partition refinement?
Sets. Things definitely not in set.

DAWG - transitions are single labelled edges. Transitions are

[Hopcroft and Karp’s algorithm for Non-deterministic Finite Automata](https://hal.archives-ouvertes.fr/file/index/docid/648587/filename/hkc.pdf)


# Kleene Algebra

## KAT

https://link.springer.com/chapter/10.1007/978-3-030-81685-8_3 algerbaic program anlaysis
graphs and paths can be represent by taking the letters of the alphabet to representedges in the graph. The paths from a to b can be represented as a regex
Tarjan's algorithm http://i.stanford.edu/pub/cstr/reports/cs/tr/79/734/CS-TR-79-734.pdf "path expression problem"
If you have the path expression, you can just intepret it to calculate program quantities.

Kleene algerba with tests
MOdelling language for 
horn equational?
Relative of Propositional Hoare Logic. Which is a neat idea on it's own

tutorial https://alexandrasilva.org/files/talks/kat-tutorial.pdf https://popl20.sigplan.org/details/POPL-2020-tutorialfest/7/-T7-Programming-and-Reasoning-with-Kleene-Algebra-with-Tests
https://www.cl.cam.ac.uk/events/ramics13/KozenTutorial1.pdf

GKAT  guarded kleene with test https://arxiv.org/abs/1907.05920 https://www.youtube.com/watch?v=Dp68j9Wi_84&ab_channel=ACMSIGPLAN - verifcation of uinverrpeted programs in nearly linear time. The choice operators leave evidence. A "fundemantal theorem of clauclus" for loops?

Kleene algebra modulo theories
https://github.com/mgree/kmt
https://arxiv.org/pdf/1707.02894.pdf
https://github.com/mgree/katbury hmm. guess invariants

[On the Coalgebraic Theory of Kleene Algebra with Tests](https://www.cs.cornell.edu/kozen/Papers/ChenPucella.pdf)
Automatic proof generaton via derivatives? That sounds neat.
Chen and Pucella - coalgerba theory of KAT

[Automated Reasoning in Kleene Algebra](http://www.hoefner-online.de/home/pdfs_tr/trCS-07-04-Shef.pdf) Prover9/Mace4

[Symbolic Algorithms for Language Equivalence and Kleene Algebra with Tests](https://dl.acm.org/doi/10.1145/2775051.2677007) bdds + union find for language equivalence

topkat incorrectess logic and kat https://www.youtube.com/watch?v=gLLlrnxB5Jg&ab_channel=ACMSIGPLAN popl22

NetKat - kat for network reasoning
[Kleene Algebra with Tests and Coq Tools for While Programs](https://arxiv.org/abs/1302.1737)

syntax are kleene expressions / logic is kleene algebra manipulation. logic is algebra on steroids
semantics are strings

algerbraic laws + leastness of fixed point

hmm. 2x2 matrices have a schur complement representation theorem. hmmm.

a <= b <-> a + b = b


Well, this is basically doable

```
(datatype K 
 (+ K K) ; choice
 (* K) ; iterate
 (Fail)
 (Skip)
 (# K K) ; sequence
)
(define a K)
(define b K)
(# (* a) b)
(: (+ One a) (+ One b))
(* (+ a b))

; idempotent semiring
(rewrite (+ e Fail) e)
(rewrite (+ e f) (+ f e))
(rewrite (+ e f)) ; assoc
(rewrite (+ e e) e)

(rewrite (: ))

; star is least fix point

(rewrite (: (+ One a) a) (* a))



```

efficient procesure - antichain doyen upto bis9mualtion bonchi-pous 2015

kleene algerab with tests Add booleans as subset of kleene stuff

if b then p else q = b;p + ~b;q
while b do p = (b;p)* not b

booleans commute under seq

guarded semantics. a kleene command is every possible pre and post condition.
sequence needs the bools to meet in the middle

(Bool K Bool)

propositional hoare logic.
{b}p{c} = bp~c == 0
what does that mean? oooooh. b p not(c). Ok that's neat.

Models
Language models - just actions
Trace models - interspersed with states in btwee
relation models - relation compose, relation closure
tropical semiring and convex polyhedra
matrices over another kleene algerba


# Bisimulation
[BisPy is a Python library for the computation of the maximum bisimulation of directed graphs.](https://bispy-bisimulation-in-python.readthedocs.io/en/latest/index.html)
I'm confused. Is it partition refinment or union find?



Of what relationship is bisimulation to non-interference proofs? Bisimulation is kind of a way of saying the state is unobservable from the actions/observations.

Graph isomorphism - too striog?
Trace equivalence - Too strong?

There is a distinction between saying a given relation is a bisimulation and _defining_ it to be a bisimilar closure of something.

Least vs greatest fixed point

## Codata
[Data-Codata Symmetry and its Interaction with Evaluation Order](https://arxiv.org/pdf/2211.13004.pdf)
https://blog.sigplan.org/2019/10/14/how-to-design-co-programs/
Howw to design co-porgrams - gibbonsd

https://en.wikipedia.org/wiki/Corecursion
https://arxiv.org/abs/2103.06913v1 - Classical (Co)Recursion: Programming
Paul Downen, Zena M. Ariola, examples in python scheme, agda

codata is productive, meaning recursion is guarded by applications of constructors

copatterns
https://agda.readthedocs.io/en/v2.6.1.3/language/copatterns.html
Are copatterns simple? They just explain what to do on every application of an accessor functiojn
on a record. This is the same thing as giving the record explicility
https://www.youtube.com/watch?v=-fhaZvgDaZk&ab_channel=OlafChitil altenrkirch coinduction in agda

## Coalgebra
Rutten and Bart Jacobs

## Coinduction
Coinduction. What up? https://en.wikipedia.org/wiki/Coinduction

[coinduction he](https://paulhe.com/2019/04/17/coinduction.html) nice blog post. Greatest fixed point takes everything and prunes away stuff that can't be proven.
Least fixed point starts with nothing an adds stuff that can be proven.

bisimulation
graph isomorphism between two systems is too strong. Why?
it only requires that each system has some way of finding corresponding states.

What is induction really?



[[POPL'22] Coalgebra for the working programming languages researcher](https://www.youtube.com/watch?v=Qb0z1FWT5bw&ab_channel=ACMSIGPLAN)

A pointery circular list is a labelled transition system if which node you're on is the state, and tail takes you to the nexxt state and head is an action that takes you to the same state.
Two observationally eqauivalnt cirucils lists ones = 1 : 1 : ones and   ones = 1 : ones
are bisimilar

A more natural definition is observation O, S states, A actions.
head would then be an observation on the state.

Egraphs as transition systems? Observations of head, argument choice as action?
This suggests we don't have to canonicalize it?

The existential form of a coinduccutive type
exists s, (s, s -> f s)
Is the analog of a closure form  exists s. (s, (s,a) -> b)
We can defunctionalize the possible states and put all the s -> f s things in the apply function?

Ones | Inc1 n |

apply (Inc1 n) = Cons a (Inc1 (1 + n))
A closed data type of all my possible streams


CoCaml

bisimulation goes hand in hand with condicution.

What does it mean for two systems to be equal?

Automata traditionally just worry about the trace they accept.
Nodes are labelled with somethign and edges are labelled with somethign. not persay atomic actions.

Hmm. So the record type condictive in coq. Each accessor is a message or action
And I suppose each value of the conidcutive is a state.
Is this a bisimulation under that understanding?
```
CoInductive bisim {A : Set} (x y : stream A) : Set :=
  | bisim_eq : head x = head y -> bisim (tail x) (tail y) -> bisim x y.
```

https://poisson.chat/aquarium/defunctionalization.pdf - lusxia - shows an interesting defunctionalization trick to define fix.
Is the point to close the universe of possible functions so that coq can see that we're only using productive ones

https://arxiv.org/pdf/1906.00046.pdf interaction trees
conor mcbride turing completeness


A process in coq.
The labelled trasnition relation. Ok sure.
Inductive trans s1 a s2 :=

Then what?
Definition bisim ta tb sa1 sa2 := 
   forall s1
Definition IsBisim r ta t2 := forall sa1 




Sangiorgi Book


Connection to recursion schemes. Categorical perspective. Meijer.


"Biggest Fixed Point"

`a -> f a` building up a functor f

`f a -> a` breaking down a functor f



Coinduction ~ object oriented.
Observations / messages are sent to a data object
Existential encoding - Strymonas paper
exists s, {state : s ;  observation1 : s -> yada ; observation2 : s -> yada  }
As compared to universal encoding (Bohm berarducci) of inductive types (their fold)



LogTalk -
Co-LP (logic programming), rational trees. Could one fold together the lambda prolog perspective and 
https://www.youtube.com/watch?v=nOqO5OlC920&t=3644s&ab_channel=MicrosoftResearch a talk by gupta
Vicisou Circle - book
Aczel in 80s?


Co-LP is dual to tabling
The metinterpeter looks very simple. What is a metaintepreter for tabling. Is it similarly simple?
https://personal.utdallas.edu/~gupta/meta.html
Keep list of previous calls. Attempt to unify with a previous call. This recognizes cycles.
co-auto for Coq? Does paco do something like this?
Interesting connection: Sequent as a virtual machine, lambnda prolog sequents describe logic programming, This coniductive metainterpreter reifies the goal stack. So does the delmittied continuation based tabling. Coinductive = negative types
Sequent calc as a virtual machine is already kind of how lambda prolog is described. But Downen was talking classical logic, and Miller nadathur almost exclusively constructive logic. Miller and nadathur do have function types, distinct from implication (I think). 
Could one make a prolog on this basis. Should the coinductive predicates somehow be connected to continuations? The tabled version reifies a goal stack for delimitted continuations. No wait. I'm remembering achieving tabling via delimitted conts.

<   |   > :- < | >,  <  |  >
Or this as a notation for callcc, shift/reset? In scheme or whatever the conitnuation is not omnipresent in notation.
p(X,Y) :-  < K |     >  % this is binding a K with callCC or something
Downen and Ariloa are saing classical logic does have an operational semantics, some what maybe in contradictin to the feel of what Miller is saying,.


https://personal.utdallas.edu/~gupta/ppdp06.pdf  Co-Logic Programming: Extending Logic Programming
with Coinduction L. Simon, A. Mallya, A. Bansal, G. Gupta
https://twitter.com/sivawashere/status/1364734181545238532
https://logtalk.org/papers/colp2012/coinduction_colp2012_slides.pdf



Downen. Connections back to sequent calculus papers. Computing with classical connectives.




Bisimulation
Coinductive proof


Coq and coidnuction
Chlipala's chapter
Breitner blog post - https://www.joachim-breitner.de/blog/726-Coinduction_in_Coq_and_Isabelle
https://www.joachim-breitner.de/blog/727-How_is_coinduction_the_dual_of_induction_

Older notes - Nice ones by
Eduardo Giménez and Pierre Castéran (2007). "A Tutorial on [Co-]Inductive Types in Coq"  http://www.labri.fr/perso/casteran/RecTutorial.pdf
Paco
Computability theory library

Basic interesting proofs:

techniques - unfold via a match function.
Condinductive records are smarter?
Positive and negative types


https://www.cs.cornell.edu/~kozen/Papers/MetricCoind.pdf metric donictuction
What is this

https://www.cs.cornell.edu/~kozen/Papers/Structural.pdf practical coinduction - kozen

https://github.com/dpndnt/library/blob/master/doc/pdf/abel-adelsberger-setzer-2017.pdf
Interactive programming Agda - Objects and GUIs.


The smallest coinductive is unit
The smallest inductive   is void

Finite enum types = inductives

Mixing in enums, you can make finite product types as coindcutives.

Taking it more hard core, you could make a record for every body of an inductive.

Primitive inifinite condinductive is Forever
primitive infiniter indcutive     is nat


Negative types and positive types. They come together to create activity.
Push streams and pull streams

Neel - 
Hi, this is a surprisingly complicated question.
For lazy languages, least and greatest fixed points coincide. (The jargon is "limit-colimit coincidence" or "bilimit-compactness".)
For strict languages, they do not coincide, and while you can still encode them, the absence of coinductive types is arguably a language deficiency.
For languages with first class continuations, they are perfect duals -- the negation of an inductive type is a coinductive type, and vice versa. This also means that the eliminator for an inductive value is a coinductively defined continuation, and vice versa. (See David Baelde's Least and Greatest Fixed Points in Linear Logic.)
This duality does not hold in languages without first class continuations, since there is an asymmetry between how you can use values and how you can use continuations.
You will sometimes see people talking about how inductive types are strict and coinductive types are lazy. This is a misconception -- in a language with continuations, you can have both strict and lazy inductive types, and strict and lazy coinductive types. Due to the aforementioned asymmetry, in a language withouts control, you can have strict and lazy inductives, but only lazy coinductive types. (This is in Baelde's paper, but you have to squint to realize it, because he was doing proof theory rather than language design.)
https://arxiv.org/pdf/0910.3383.pdf Balede's paper