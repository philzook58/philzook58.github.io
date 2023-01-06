

- [Applications and Ideas](#applications-and-ideas)
  - [ASP](#asp)
- [Z3 triggering](#z3-triggering)
- [Lemma Command](#lemma-command)
  - [Command Ideas](#command-ideas)
- [Alternating quantifier](#alternating-quantifier)
  - [Looks like partial horn logic uparrow. Define as an assertion / judgement. That's the analog of](#looks-like-partial-horn-logic-uparrow-define-as-an-assertion--judgement-thats-the-analog-of)
  - [or](#or)
- [Puttting insertion into the equals operator.](#puttting-insertion-into-the-equals-operator)
- [Timestamps](#timestamps)
- [Metaprogramming](#metaprogramming)
  - [first class when](#first-class-when)
- [Context](#context)
- [Macros](#macros)
- [Modules](#modules)
- [Proof relevance](#proof-relevance)
- [ASP](#asp-1)
- [Contexts](#contexts)
- [cofunctions](#cofunctions)
- [Backchaining - harrop](#backchaining---harrop)
  - [Observational Disequality](#observational-disequality)
- [Prolog vs egglog](#prolog-vs-egglog)
- [These variabes _are_ branch local because we have a backtrackable egraph. The egraph operations will _never_ unify uvars.](#these-variabes-are-branch-local-because-we-have-a-backtrackable-egraph-the-egraph-operations-will-never-unify-uvars)
- [Logical models](#logical-models)
    - [Chalk](#chalk)
- [Egg Chatathon 2022-10-31](#egg-chatathon-2022-10-31)
  - [attendees](#attendees)
  - [notes](#notes)
    - [The problem](#the-problem)
  - [GATs](#gats)
  - [](#)
- [Resolution](#resolution)
  - [Paper](#paper)
    - [Reflection and Truth Values](#reflection-and-truth-values)
- [Unification modulo egraph](#unification-modulo-egraph)
  - [potential roadblocks](#potential-roadblocks)
    - [Unification modulo egraph](#unification-modulo-egraph-1)
    - [Partial horn clauses](#partial-horn-clauses)
  - [Grobner](#grobner)
  - [Gilbert Imp](#gilbert-imp)
- [guards](#guards)
  - [Souffle egglog](#souffle-egglog)
  - [disequlity (ne graphs)](#disequlity-ne-graphs)
  - [Indicator functions](#indicator-functions)
  - [Linear Database](#linear-database)
  - [Semantics](#semantics)
  - [Raw Egglog (Salmonella)](#raw-egglog-salmonella)
  - [Symbolic Execution](#symbolic-execution)
  - [Disassembly, Compiliation I dunno](#disassembly-compiliation-i-dunno)
- [eggsmol](#eggsmol)
- [e-unification](#e-unification)
  - [Differential / Incremental egglog](#differential--incremental-egglog)
  - [Union Find Groups](#union-find-groups)
  - [Defaults](#defaults)
  - [Egraphs and Terms at the same times](#egraphs-and-terms-at-the-same-times)
  - [CHC](#chc)
  - [refinement typing](#refinement-typing)
  - [Gam |- e =\> A    A = B](#gam---e--a----a--b)
  - [Interval arithmetic](#interval-arithmetic)
  - [Destructive Rewriting](#destructive-rewriting)
  - [Macro System](#macro-system)
  - [Proof provenance = extraction?](#proof-provenance--extraction)
  - [Proof](#proof)
  - [ASP for ILP extraction?](#asp-for-ilp-extraction)
  - [the chase](#the-chase)
  - [Prolog v Datalog v Egglog](#prolog-v-datalog-v-egglog)
  - [Egglog vs SMT](#egglog-vs-smt)
  - [Egglog vs Flix vs IncA](#egglog-vs-flix-vs-inca)
  - [Gogi](#gogi)
  - [Related systems](#related-systems)
    - [Egg](#egg)
    - [SMT](#smt)
    - [Datalog](#datalog)
    - [Chase Systems](#chase-systems)
    - [Prolog](#prolog)
    - [Formulog](#formulog)
    - [Flix IncA](#flix-inca)
    - [Proto-Egglogs](#proto-egglogs)
  - [Lattices as egraphs](#lattices-as-egraphs)
  - [Harrop Clauses](#harrop-clauses)
  - [Top down evaluation](#top-down-evaluation)
  - [Constraint handling rules CHR](#constraint-handling-rules-chr)
  - [CAS](#cas)
  - [Quoting out of egraph, reflection](#quoting-out-of-egraph-reflection)
  - [Bisimulation finest partition](#bisimulation-finest-partition)
  - [Typeclasses and Rust Chalk](#typeclasses-and-rust-chalk)
  - [provenance](#provenance)
  - [Semiring smenatics](#semiring-smenatics)
  - [Lambda](#lambda)
    - [Extract and do stuff](#extract-and-do-stuff)
    - [Yinhong let binings](#yinhong-let-binings)
  - [Scoped union find](#scoped-union-find)
  - [Higher order rules](#higher-order-rules)
  - [Semantics of Egraphs](#semantics-of-egraphs)
  - [/](#-1)
  - [NE graph](#ne-graph)
  - [Egraphs over programs. Program analyiys](#egraphs-over-programs-program-analyiys)
  - [Metatheory and EGraphs](#metatheory-and-egraphs)
    - [Bits and Bobbles](#bits-and-bobbles)
- [A More Naive EGraph](#a-more-naive-egraph)



# Applications and Ideas
Applications I guess
- staged egg
- higher order egglog, skolemization
- A = C - B :- A + B = C. A = Lit(1/C) * B :- Lit(C) * A = B, C != 0 (* Hmm. Recipricating C over and over probably isn't good. *)
- Coq tactic
- Dependent programming proof relevant union find
- Applications: Category theory proving, solving systems of equations, patching compiler
- Lambda terms / binding forms
- efficient encoding to souffle

- instruction matching modulo equality
- xor linked list pointer analsyis
- cos^2 + sin^2 = 1+ interval analysis. Some expression better than others. Tighter interval bounds/
- `pos(x), sqrt(x**2) -> x, neg(x), sqrt(x**2) -> -x`
- x * x -> beter upper bound. Sharing problem

- instruction matching over egraph of cfg. Maybe just a single block
- knot diagrams as braiding algebra? Prove unknot

- Rewrite query to equivalent query for a database. Instruction matching modulo equality.
- any application of the chase. Data migration.

- Carette inspired guarded rewriting. Datalog style fixpoint analysis makes sense
- Reified sets using SMT style union axioms and such.
- Reified lattices in similar way. Lattices defined via generators quotiented by relations

- refinement typechecking a la liquid haskell?
- The "Sub" rule of bidirectional type checking. We can do typechecking modulo equality.

LADDDER benchmakr
incA compile from source
arifact
dll-bench

https://github.com/remysucre/dll-bench



Remember my point about Ocaml Set data structure, except `compare` is changing under the hood
Union Find dict.
Lattice ranged dict.

Tuples of union find

https://www.swi-prolog.org/pldoc/man?predicate=dif/2 prolog supports `dif` constraint. Pretty interesting duality to egglog that only supports = constraint
ephemeral union find - how to support provenance?

Could there be an example where egglog is superior to formulog with respect to symbolic execution? In some sense, egglog is a much tighter integration of a piece of smt + datalog. Maybe equational reasoning could see that different paths are equivalent at join points?

[composing data analysis and trasnformation - sorin lerner](https://cseweb.ucsd.edu/~lerner/UW-CSE-01-11-01.pdf)


Dynamic rules and macro based compilation aren’t necessarily mutually exclusive. I think you could call rustc and then dynamically link in new rule. A somewhat complex architecture though https://docs.rs/libloading/latest/libloading/

guy(_,_,)
guy(null,_,)

foo(proj1(guy(null,null)) ) = guy(foo(null) ,null)
Has some flsavor of theory of arryas.
guy(_,_) is a two port graph
foo(proj(a, guy(a,b))) = guy(proj(a, f(a)),b)

named ends. edges kind of are named. Is this better than monoidal style?
dup(_, _,_)
cup(_,_)
Do we actually have cases where signigicant graph rewriing can happen? Graphical linear algebra?

distributed egg


What is truth value
bottom - unit
bottom - true - false

but we have named unknown. not just bottom.
They can be unknown but equal
what does that mean. We're talking about 1 value...????
It's "relational"? like parametric typing?
between runs?
between two instances?

what is the semantics of a no argument relation (or single argument?)
rel()
() -> ()
( , ) -> _|_ + ()

() -> partial equiv rel over (int  + ())

Miller patterns in egglog.
What if you didn't need to extract and normalize. You need to make rules and the heads normalize as a built in functor? Hmm. But miller stuff is enodes.
I guess you could continue searching until you find a term that you know is free of disallowed variables?
You'd basically need to extract a term that only contains the allowed vars. 


add(x1,x2,):- add(x1,x2,x3), add(x1,x2,y3)


eq(z1,z2) :- add(x,y,z), add(x,y,z2)

yz = fresh, add(y,z,yz), add(x,yz,xyz) :- add(x,y,xy), eq(xy,xy1), add(xy1,z,xyz).


add(x1,y1,z2), add(x2,y2,z1) :- add(x1,y2,z), eq(x1,x2), eq(y1,y2), add(x2,y2,z2)

yz = fresh, add(y,z,yz), add(x,yz,xyz) :- add(x,y,xy), eq(xy,xy1), add(xy1,z,xyz).


table to resolve functional dependencies.
multiple delta

matching mod union find is same as just regular match

is congruence.

if fixpoint exists, it is unique.


existential don't add. lookup existentials
merge only - chase

Maybe this don't add existential method makes no sense not in egglog? Maybe it doesn't

exists x, p(x), g(x) :- q(y).  becomes

g(x) :- q(y), p(x).
p(x) :- q(y), g(x).

exists! x, p(x), g(x).

p(x) :- q(x).
q(x) :- p(x).



only shrink
only grow expanded database
dmt datalog modulo theories
how is dmt not CLP(X)? It is basically. With tabling.
The question is: is datalog a good idea or not? Why is it better than tabled prolog? Simplicity? An actual reason?


depth bound - ac 

rewrite + rebuild

search only

ree automata
https://jacquema.gitlabpages.inria.fr/files/tata.pdf 
pick root node

might as well merge
hopcroft
nerode congruence

 backtracking souffle egglog


what are the claims
figure out the eval

sam coward bitvector
eqsat + datalog

text format
compositionality of analysis
increentality
herbie
benchmarks from datalog
benchmarks from egraph

"techaing match papers"
relational ematchig compare

pods
core from chase

alexa?
herbie lang - right prims

parser
benchmarks
examples

Termset algebra
https://www.cs.cornell.edu/~kozen/Papers/gentzen.pdf
f symbols are comprehensions.
Something almost self reflective about this, because egraphs are kind of similar things themselves
https://www.cs.cornell.edu/~kozen/Papers/lasc.pdf
"set constraints" phi n f(x,y,z) = 0. Kind of reminds me of 
CLP(SC) jaffar lassez
phi n g = phi as a subset constraint I was suggesting for CHCs.
https://www.cs.cornell.edu/~kozen/Papers/sclp.pdf set constraints and logic programming

Modelling egglog itself equationally? Each clause is a moonotoicn expansion operator
clause(r1,r2,r3)
clause(r1,r2,r3) U cluase() = clause(r1,r2 U r2',r3)
prog(r1,r2,r3) = clause1(r1,r2) U ... .
proj_r1()




Doing datalog entirely in first class sets.
set(x : set)
 :- set(x : set), 

clark completion semantics turn horn clauses into boolean equations

Ruler vs inductive logic programming vs datalog synthesis


Is egglog more parallelizable / distributed than hashcons based terms.
If two pieces were isolated and churning, when they came back togehter they could repair themselves.

Maybe putting linear inequalities in the the context is the most bang for buck. But why is that not just a preidcate?


tagging is powerful
Every program label can be a tag - egraphs floating, except they aren't uncoupled.
l |- ?a + ?b
We don't really need to do this for all l we can
l |- ?b + ?a <- l |- ?a + ?b.
variables represent sets of values at that position or something.
Everything has ctx tag. Is it a lattice? Mayyybe. {{l1,l2,l3} , {l4,l5}}. first class eqclass?
Map gives first class eqclass

CLP(B) uses BDDs. If we made datalog modulo B, would we have bddbdbddb?


local union find in terms of global union find. In a certain sense, the global union find is anti monotonic feeling. We would want to subsumpt into more general things foo(X,Y,Z) from foo(X,X,X), but the global union find does the opposite.
Instead of normalized terms, we could use labelled nulls. Whenever we do a new thing, we need to search that the term doesn't already exist (skolemization?).
We never perform unification? hmm.
foo($,$,$) :- !(foo(x,y,z), null(x), null(y), null(z).
lazy incrementing of freevars. (just lazy lazy de bruijn). Shift(n,t). Then you can do it at the end. 
[n, t] store number of free vars at top to avdoi retraversal


query containment solver. data migration solver

universal model
A --> B
B |= Sig
But, the intermediate steps have the following property
A --> C --> B
"under approximates the universal model"


Named things. define is a certain kind of naming
but then (function named (String) Foo) is another kind of naming.


Improvements:
- better line-col error. use code-spans
- point out variables used once. Support _
- (prove a b) command. Run until check a b passes
- (calc a b c d e f) as a chained version of prove



(cast "i64"  ). No it doesn't receive arguments at typing time.
StringSet. is default equaltiy ok?
StringMap. Map to sorts is probablly fine... uhhhh. 

The new sort functionlaity 

```
(datatype (BitVec n))
(function concat ((BitVec n) (BitVec m)) (BitVec (Add n m)))
(function extract ((i Math) (j Math) (BitVec n)) (BitVec (Add (Lit 1) (Sub i j))))
; All the regular Math axioms
```

Collect insufficient type checking examples


https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.145.7977&rep=rep1&type=pdf
Type Checking with Open Type Functions
https://www.microsoft.com/en-us/research/wp-content/uploads/2009/09/implication_constraints.pdf


rete
hierarchical rule schedular
unification modulo egraph

partial function being defined often implies something
sqrt(x) being defied implies x >= 0

freejoin
leapfrom triejoin

mobius inversion


partial lattice
homorophism function between consistent partial attices
flix meet is eq-join


lattice homomorphism
Canonicalization is two separate things.

You'd want to put the queries themselves in an egraph as a way to hash cons?
Maaaaybe.


decompiler

blogging/tweeting
matrix example
unification - resolution/prolog
python datalog
timestamp proofs

examples 
vec n example
related work

gappa
hlint
avail expr

24 days deadline


datalog modulo rewriting?

eqrel + min leader finder. smart

```
eq eqrel
leader
leader :- eq

```

could encode resolution theorem prover into?


You know, extraction and proofs are similar. They are doing a top down prolog-ish process over the final database.


[oeirented equational clauses as a programming language](https://core.ac.uk/download/pdf/82591236.pdf)


Should egglog have a (var ) form? Use var as entities in rules, but also in theorems.
(calc (x y z)
    foo
    bar
    biz
)

=>

(push)
(function a (unit) Sort)
(define a (a))
(assert)
(check)
(pop)



(calc
    a => b (introduce fresh vars, insert a, stop on b.)
    b => c
    c => d
)

Perform just the back chaining we can and terminate.

(forall (x Biz) (=> a b))

(calc ->
  a
  b
  c

)
(prove (forall (x y z) (=> )) :assert)
(assert (forall (x y z) ))
(prove )


Special symmettry reduction. add3(x,y,z)

lambda lifting.
(lambda )
Can we support higher order harrop via context as timestamps. "forking the database"
contexts are dags?
(G -> D)

G ::= True | Q | G ∧ G | G ∨ G | ∃x G | D ⊃ G | ∀x G
D ::= A | | Q ⊃ D | D ∧ D | ∀x..:Q, D
Q ::= True | A | Q ∧ Q | Q ∨ Q | ∃x Q


G ::= True | Q | G ∧ G | G ∨ G | ∃x G | D ⊃ G | ∀x G
D ::= A | | Q ⊃ D | D ∧ D | ∀x..:Q, D | G -> D 
Q ::= True | A | Q ∧ Q | Q ∨ Q | ∃x Q

What's the point?

G ::= Q | D ⊃ G | ∀x G
D ::= A | | Q ⊃ D | D ∧ D | ∀x..:Q, D | G -> D  
Q ::= True | A | Q ∧ Q | Q ∨ Q | ∃x Q

Maybe restricting some things to be propositional or monadic? That forall table is kind of interesting. It kind of feels like  the signature Sigma that nadathur and miller talk about.

D ::= A | | Q ⊃ D | D ∧ D | ∀x..:Q, D | p -> D  


Termination competition is another source of benchmarks. Again, it isn't clear these are good benchmarks.
It would be a genuinely helpful thing for me the setup a CI benchmark suite

## ASP
ASP kind of has it's own notion of worlds or contexts.
Branching. Sets of possibilities.
ASP is justifiable according to greenberg. I'm not so sure.

The choice cnstructor is compileable to negation?


# Z3 triggering

Intead of using equality in triggers, use a dummy uaxiliarlu predicate.

x = y :- f(x) = g(y) 
becomes

(forall (x y)  (check (f x) (g y))
(forall (x y)  (x = y) :trigger (check (f x) (f x)) (g y))


# Lemma Command
If we make egglog solve a goal.
And then assert that goal back as a rule

Ok but can this be done. G and D are not the same.

G ::= Q | G ∧ G | G ∨ G | ∃x G | D ⊃ G | ∀x G
D ::= A | D ∧ D | ∀x..:PG, D | ∃x D
Q ::= True | A | Q ∧ Q | Q ∨ Q | ∃x Q

Q -> D
A | Q ∧ Q | ∃x Q , but not Q ∨ Q... uhh, we need to know which branch worked. Ok. Interesting.

G -> D
Q  yes
| D ⊃ G. Not really. Q -> G?
| ∀x G

Let's worry about these later
| G ∧ G | G ∨ G | ∃x G |


Is it `lemma` or `cut`?

Hmm. Lemma is actually kind of relatedt to Maude memo.
We are memoizing one particulr link of the rewrite system.
Memo isn't hash consng a single term. It's mapping an unnomrliazed term to a normalized one



## Command Ideas
DONE - include is idiot modules. Would be a nice little feature~
Wow. let is super goofy.
Wildcards would be appreciated.
A demand creating form for :when would be appreciated.
overloadable regular functions would be appreciated.
string concat
refine command - (run extract) loop. (refine N M)
DONE simplify command - run - extract. If not going down or satruated run again.
add scriping language / embedded interpreter
extensible parsing. Extension points
refactor main loop to have egraph callback
Enable sorts to participate in canonization/propagation
The sort interface sucks.


sketch command (calc (forall (x ) (exists y)  t1 = t2 = t3  ))
DOn't bother 
exists! uniqueness qauntification / definite description

What about a tactic or high levrl scripting language rather than macros.
(for ... ())
(chain )
(define-command foo (a b c) ??? what are the parameters here?
(while cond
  (begin
  ;(or a b c) allow commands to fail
  ;(not) turn failure into good
  ;(and)
  (if cond
    command1
    command2
  )
  )
)
)
The database is a context.
Goals are goals
(lemma 
   (foo -> bar -> biz)
   :tactic
   (begin
    (intro)
    (exists (foo x)) % hmm. But we don't assume things exists. so this tactic looks up that the term exists first?
    
   )
)

We could allow expression invarious positions and eval them. And they better eval to integers.



Tactics
https://www.cl.cam.ac.uk/~gp351/moura-passmore-smt-strategy.pdf
Hmm. In a sense, my G formula \/ is the par tactic.
Guarden Commands
(when c com)
Cond => Com.


https://en.wikipedia.org/wiki/Tabu_search
A*
Hill Climbing

Term distance metric - For proving, you want to extract 2 terms that are getting closer to each other.
Or extract a term that is a closest to fixed term


# Alternating quantifier



D formula of Void can be translated to panic. They can also be backpropagated via gfp lp 
D formula of true are pointless


Sketch command, don't bother with the exists, just let insertion fail and ride.
Hmm. If we eagerly pick an extract solution, it might be wrong...
We really need to run them in parallel and intercommunicate.
forall exists forall exists ( a = b /\ b = c /\ c = d /\ d = e /\ e = f)
calc does exactly the same thing as this goal.
We could dump it all in one egraph...? Interpret /\ as Q operators rather than G.
Lexicographic ordering of quant depth, then term height.
- we have to have solution with cost less than 2
This is a logically motivated version of which constructors are allowed.
The outer forall is stuff that's allowed everywhere
forall do_include exists forall do_not_include
birewrite should just warn on failure on one rule. fail on failur of both.

Hmm. What about that idea of running grounded terminating prolog. Does that let me extend the G formula?
Q formula?

(generic-function cost )
cost

do program clauses have to worry about the quantification? Noooo...? 
What if a program clause captures one? Yikes.

exists x: Q, G 



(function )
(set quantifier_cost(a) 1) ; quantifier depth basically
(set quantifier_cost(b) 2)
(size)
Both size and quantifier cost need overloading / are annoying to define.
We might perform some pre-unification in the query... But unification happens in the query anyhow?

I guess we're impliitly asserting the terms exist
(define foo) /\ (define bar) -> foo = bar 
Looks like partial horn logic uparrow. Define as an assertion / judgement. That's the analog of 
--------
Gam ctx,   ===>  (define Gam _ Context)  vs (ctx Gam)
or 
-------
T Type     ====> (define T _ Type)  vs (Type T)


In my presentatin of the rule T and Gam are metavraibles. In actual situtions they are some term that goes in the _
THe existence of terms has to be justified.


equation solving as a quantifier alternation
 (exists x, x + y = 0) -> exists  

forall x y, (x + y = 0) -> exists z, (x + z = 0) ->  
exists z, forall w, ((exists x y, x + y = 0) ->  (z + w  =  0))
Oh. No. For equation solving I don't want the answer to contain _itself_
exists x, foral y, exists z, 
exists x, forall y

forall a (exists b )


forall y, exists e, forall x, (x + y = 0) -> e = x
e cannot contain x or else this is a scope escape

So there are restrictions of where lambda terms can go huh...
Maybe we can only support them in G also?

(calc (exists (forall ))) is also doable. That's synthesis. 
exists-forall is synthesis. The pattern variables cannot include the forall variables.
How many layers of nesting can we do? Well, basically it's a scoping issue. We can only extract exists terms that do not contain vars. Is this equation solving as a command? This scoping issue is exactly a thing...
forall q, exists p, () /\ () /\ (). The forall are the variables to keep. Quantifier elimination is also a form of equation solving.
Unification _is_ equation solving, just in the initial theory. It makes it easier, which is kind of counterintuitive. Full injectvity is a really powerful axiom.
raising is skolemization on G formula
skoemization is on D formula.

forall exists -> forall become new constants, exists become, Gt the queries, filter them in order, need to extract.
How do I reoncile this wth the dea that unification is done by gensyming? The existenstials are the ones that work?
foral y, exists x {t = s},   exists becomes unifcation vars.Well, that could help seed.
creating a fresh var is upcoverting an exists to a forall, which is a harder goal. But then we assert.
(forall y, forall x, t = s -> exists x2, t[x2] = t[x1] )  -> forall y, exists x {t = s}




(exists x)
Is this higher order unification? (unify ...)
Hmm. Even in my grammar I allowed nested exists forall in G.

(calc )
(synth ?)

SHould checks seed? Queries? (check (= t1 t2)) if they are _ground_ posibly should add in t1 t2.
the mixed quantifier problem already fits into harrop lite.
Puttting insertion into the equals operator.  
=
:= (set)
:=:
The logical motivation for this is light.
rewrite expands to
(rule (lhs) (and when (rule when rhs)))




(birewrite (compose (compose f g) h) (compose f (compose g h)) :when ((= (type A) Ob) (= (type B) Ob) (= (type C) Ob) (= (type D) Ob) (= (type f) (Hom A B)) (= (type g) (Hom B C)) (= (type h) (Hom C D))))
(birewrite (compose f (id B)) f :when ((= (type A) Ob) (= (type B) Ob) (= (type f) (Hom A B))))
(birewrite (compose (id A) f) f :when ((= (type A) Ob) (= (type B) Ob) (= (type f) (Hom A B))))
This ought to be possible to infer

[compositional preprocessing for smtcoq](https://arxiv.org/abs/2204.02643)

tptp benchmarks
import maude benchmarks?
fstar and dafny? Prbably tougher? Liquid haskell?




Yeah, there was this idea that (Set foo) already exists in GJ if the sets are treated last.
GJ automatically does group by
relation becomes
(fuunction (a b) c) 
is curried to (-> a (Map b c))
(relation a b c) =
 (function (a b c) unit) curri to (a b) (Map c unit). (Map _ unit) is Set


Justified models. Define justification (proof) objects.
Why is this not just proof theory? Well, we want to go modulo theories.

Justified SAT - unit propagation and learned clauses.

ATP and resolution SAT.
vs
datalog and ?

ATP is inference spray. SMT is model driven.

Just unit propagation of SAT is almost trivial. We can output learned clauses.
THe goals are totally different. You don't _want_ to find sat models. you want to find "good" clauses / find maximal unit propagation power.
Given a formula, fill in the bools that are tht value in every model.
Record SAT models. If we see bools take on multiple values, they can never be forced
Like a sudoku. Sudokus are nt solvable by pure unit prop. But they have unique solutions, so it is justified.
This gives a new form of hypothetical or head disjunction.

Hmm. But if I have a loop that takes the formula and forces the head vs it's negation, I can get the justified model.
2N Sat calls. hmm.

I could also enumrate the 2-formla for connected stuff. and 3-formula.
This sounds a bit like an asp.
(function foo (i64) SATVAR) as a new form of truth value compared to (relation foo) or (function foo bool)

Oh really, I can ask for a sat model, and then force each var to it's negation.
Depending on the interface that may be eaiser or harder. The model might need to be saved.
Save the model, check if required.



in SMT, SAT is the master, and the thepries are the salves, egraphs are the mediator
Here, datalog/egraphs are the master, theories are slaves and bools/sat is just a theory
We focus on theory propagation and not theory conflict. Conflict is not a notion since we're not doing refutation.

Linear arithemtic as theory. Sure we can asert inequalities. We could ask smt a model.
We could then see the stability of the values and concretize them
enum SymInt = {Concrete(i64), Sym(z3Int)}
Perhaps we can have justifiable observations?
(observation gt (z3int i64) bool). It could co-merge that if somehow gt becomes >= 3 = true through some other means, we should assert this about the z3int in the comerge operation. And that _might_ concretize it. That's not co-merging. There isn't a functional dependency conflict.
elem(x,p) --> elem(z3var, z3pred)

We don't split the z3int..? Or do we.
x1 >= 0 /\ (x0 = x1 \/ x0 = x2) /\ x2 < 0 - this is the analog of splitting part0 into part1 part2, s.t. part0 = part1 union part2
Then the z3 variable represents a set??? The projected set of all integers in that position. A quantifier elimination.


Is this method of querying the sat slver analogous to the iterative egraph expansion?
QUery z3. Get model. Question every assumption. Is it consistent that x1 != x2? If so add it. Still, you can't trust the model ever.



SATVAR = True | False | Var(n)
"Canoniclization" checks a SAT solver wherher both true and false are still consistent. Very short timeout

(assert (p and q))
(assert (p or q))

file:///home/philip/Downloads/Decision%20Procedures%20for%20Equationally%20Based%20Reasoning.pdf
Decision procedures for equationally based reasnign
order sorted theores - sort have inequalities on them/overloadin
That sounds cursed.
membership equatinal logic


# Timestamps
Bloom had timestamps for modelling dist systems. We have timestamps by default for seminaaive purposes. Blooom gives a syntax to access them
 ctc  |- q  :-  
Bloom


```
db = []
db.append(("foo", 0,1)) # assert fact
db.append(("+", 0, 1))
db.append(("=", 0, 1))

class DB():
  def append(ctx, fact):
    self.db.append(fact, time, ctx)
    time += 1
  def find(self, x, t, ctx):

  def union(self,x,y,t,ctx,assume=False):
    px = self.find(x, t, ctx)
    py = self.find(y, t, ctx)
    if px != py:
      # is assume redundant? There is a distinction between a union that is a "guess" and one that follows from other rules
      if assume:
        ctx = ctx.add((=, x, y))
      # one or both of these logs?
      self.append( (x,y), t, ctx)
      #self.append( (px,py, ) )

class Context():
  def __init__(self):
    #?
  def add_eq(self,x,y):
    #?

class Context_UF():
  def __init__(self):
    self.log = []
    self.t = 0
  def find(self, x, t, ctx):
    for entry in self.log:
      #?
  def union(self, x ,y, t, ctx?, reason?):
    px = self.find(x, t, ctx)
    py = self.find(y, t, ctx)
    if px != py:
      #?
```


and yeah thinking of contexts as “labels” on rows I think is fine. The timestamps come in if you want to process everything incrementally: the contexts and timestamps have to interact in the “right” way to avoid recomputing everything.
I wonder if, once you have support for contexts like this, you'd want to also want forall to live in a separate context as well. If all you had was forall, I think you'd be able to do something else.
I think “compile-time” contexts sound cool, but is there a concrete concern you have with allowing contexts to be defined dynamically/based on rule evaluation? Is it harder to analyze?
I think you definitely do want a hierarchy of contexts: basically you want to associate every context with a (potentially time-indexed) table of deltas from all contexts below it in the dag/partial order.
"as for how to do this incrementally, I think the basic gist is you have your DAG of contexts (ste of function entries + equalities); this’d essentially be the Haas Diagram for subsumption (not sure how much of the full subset lattice you need to make traversals easy. Not too big I think).
The root/bottom of each DAG is just the “real” empty-context DB. That marches along from time 0,1,…t
Each node contains a full UF (we’d use functional data-structures here I think, along with a node-local log of new ids/equalities). It also contains all of the records that would have been introduced due to the assumptions in that context and not in any weaker one (i.e. lower-down the DAG). These are also ordered by timestamp; so time increases both “up” and “to the right.” Here’s a sketch of how to get the core operations to work:
Queries: To perform a join against a function at a particular context and timestamp range, you join with each table below (inclusive) the function at that node in the DAG and union the results. The actions should all land as deltas at this context, once everything has been deduped.
Maintenance: How do you maintain all of these precise deltas per-context? I think you take the same rules for seminaive but you run them for each node in the dag, at each node you interpret the “delta” relations as the relations at that node for the relevant ‘recent’ timestamp range. The stable relations are unions of all relevant relations at lower nodes; and you can do the joins pairwise (though we may want to build cross-delta indexes of some kind). This works because our DAG is “locally finite”: any given node has a finite number of nodes under it. The differential dataflow folks have the same requirement, for exactly the same reason (but they target groups not partial orders, so you may have to subtract values at lower nodes in the partial order to get the right answer, sound familiar?)
Rebuilding: Rebuilding at the empty context works as before, except it also needs to rebuild/shrink the context DAG (e.g. if you proved one of the assumptions). Merging two nodes in the DAG unions all the deltas there.
Rebuilding a function at nodes further up needs to first add any new unions from lower nodes, and then look at all the nodes at lower contexts and promote re-canonicalized versions to the current node.  (there’s some subtlety here in figuring out the Ids that are different at that level but I think keeping a set per node will suffice.
I also think that you could join in non-canonical ids “by accident” if you aren’t careful here.)
Anyways, I think this is the basic recipe. I hope it kind-of makes sense! I think there’s a good amount of overhead here compared to our current execution model, but, even if we can’t optimize this further:
I think we can still batch updates to higher nodes over multiple iterations lower down. That will help amortize the O(|DAG|) portions of this.
It’s the only option I see that allows us to “share” work between distinct contexts that share assumptions, which I think is neat. If it’s overkill, though, we still have the option of storing a “flat” structure with every unique context sitting above the empty context, with no extra structure.
And this whole structure still feels fairly naive. I suspect there are ways to optimize and simplify too, such as avoiding O(|DAG|) lookups when seeing if something is in a context. Functional data-structures could help here I suspect.
"

# Metaprogramming

1. Simple macros. a form `(macro-rule    )` that pattern matches on essentially the rust Expr type or alternaitveky s-exp. There are 3 architectures for this 1. a simple new recursive expander. 2. reflecting the syntax of egglog into the egglog database as a `Syntax` sort and use egglog rewriting and extraction before running the extraction as regular egglog programs. This is an interesting feature that I feel like could open some cool weird stuff like runtime generation of rules, verification of rules, etc.
2. Extended Type systems. It's really hard to build egglog libraries without some more magumbo. Maybe Hindley Milner, maybe typeclasses. Possibly a module system. Possibly manual `@i64` type annotations insetad of lways relying on inference. I think there is a possibility to do "dependent types lite" in a sense without Pi types and without lambdas. Something like `(datatype (BitVec Math))` and `(function zerovec ((n i64)) (BitVec (Lit n)))`
3. Python metaprogramming using  

## first class when

```egglog
(define-dataype Proof (Yup)) ; sierp, liftedunit, semidec

(function check (Env Term Type) Proof)

(function when (Proof Proof) Proof) ; alternative |- , =>
(= (when (Yup) (Yup)) (Yup)) ; when is also a bit like an and in a certain sense.
; currying x :- y :- z is (rewrite z (when y x))
; higher order rules can exist then.

; or (rewrite (when Yup a) a) which is even better in some cases. Polymorphism would be real nice

(function eq (A A) Proof)
(rule ((= (eq a b) (Yup))) ((union a b)))
(rewrite (eq a a) (Yup))



(rewrite (check env t ty) (When ()))


```
When serves the double purpose of creating demand for the when condition.
It is convenient, but may spray in a way you might  not like

(Sig scope t)


(rewrite (check env (VCons x xs) (Vec n a)
  (when 
    (check env x a)
    (check env xs (Vec (- n 1) a)
  )
)

(rewrite (check env (vecrec nilcase ) (Vec n a)
  (when 
    (check env x a)
    (check env xs (Vec (- n 1) a)
  )
)

Named lambdas only? More in haskell/agda equational def style type check?

iso
Iso f g
f g x = x, g f y = y.
hmm

# Context

Datalog relations correspond to judgments. Datalog rules correspond to inference rules.

$\Gamma \turnstile A$ is in it's entirety a judgement. Written in datalog notation this is `turnstile(gamma, a)`

Two points of possible confusion here:

Propositions that are derivable in empty contexts $ \{\} \turnstile A$ can be conflated with a judgement called $A$, but this may lead to confusion about the difference between propositions and judgements.

It is very confusing that judgements are often written in multiple infix notation (something you barely ever see in computer science except `a ? b : c`) and using bizarre latex symbols.


There are two encodings to talk about contextual equality. Contextual equality is a judgement that looks like this
`\Gamma \turnstile a = b$. In datalog syntax this is `eq(gamma,a,b)`

Egglog has a notion of in built global context free equality. This judgement is written `a == b`. It is not at all apparent how to encode. 

Certainly it should be the case that.
$a == b  \Gamma ctx  \BinaryInf \Gamma \turnstile a = b$

In egglog this is written `(rule ((= a b) (ctx Gamma)) ((eq ctx a b)))`.

Also if we derive in an empty context, that can be lifted to definitional equality.

$ \{\} \turnstile a = b \UnaryInf a == b$

In egglog this is written `(rule ((eq Empty a b)) ((union a b))`.

This contextual equality judgement needs to be explicitly made transitive and reflexive with rules. It needs to be made congruent also via rules.
It automatically normalizes by definitional equality though, so there is a big jump
Contextual equalites can subsume each other. `eq(ctx1,a,b) <= eq(ctx2,a,b) :- ctx1 <= ctx2.` This says that you only need to keep around the weakest contexts. Contexts may be incomparable. They are partially ordered.

It is clear that symmetric bnary relations, or relations that are symmettric under some permutations of arguments might fruitfully be deduplicated and joined a bit faster.

It is less clear that transitive relations can have a fast join / be stored efficiently.


The beauty of the union find is that the relations can be normalized and then joins can be performed modulo equality by just doing a regular join.

We think we have thrown away the need for explicit eq-joins by doing this, but the clearest method dealing with contextual equality is to reatin them in the case of contextual equality. It is a small almost syntactic feature to enable flattening to work with it's joins mediated via arbitrary relations.


There is a regular datalog model of everything we do explicitly representing $a == b$ as a relation `eq(a,b)`. Then we need to do our joins by flattening and making evey equality mediated by an `eq`, whic quickly blows up.

The tagged encoding is a different judgement is $\Gamma_1 \turnstile a == \Gamma_1 \turnstile b$. This correspond to tagging. We may define a function `turnstile(gamma, a)`. The intent here though is that `a` is _recursively_ in the context gamma. So all the subterms are also of the form `turnstile(gamma, t_i)`. This is awkward. It does kind of make sense though for alpha equivalence ${x : a} \turnstile x == {y : a} \turnstile y$ does kind of make sense.

# Macros

# Modules

Obj modules vs ocaml modules

Hmm. Scoping at time of definition is annoying.

There is a possiblity I should change many many identifiers to scoped identifiers

Hmm. By accident I've put a union find and tables in each module.
The tables _should_ be in there. (?) The module should own it's own tables.
You can add to a modules tables. You can query them.

But the union find being separate is odd and interesting.

I have tree like mdule relatinships
It's very common to allow dag like

I can't refer to parent stuff. Is that a problem really?
The parent can write it's rewrite rules that combine child and parent


Ooof. Yeah, the timestamps and union finds and saturated markers in the scopes are super duper fishy.




# Proof relevance

`x : T` is this notation of proof relevance.
`Gamma |- x : T` even more so.


Options of "truthhood"
(relation foo i64) is raw relation to unit. 
`(function foo (i64) unit)`

Proof irrelevant. Truthhood is reprented by being in the same eclass as `True`. A prop not in eclass True is considered unproven as of yet.
```
(datatype Prop (True))
(function foo (i64) Prop)

```

Proof relevant encoding


```
(datatype Type)
(function foo (i64) Type)
(relation proof (Proof Type))

(datatype Type)
(function lte (i64 i64) Type)
(datatype LTEProof)
(relation elem (LTEProof Type))

; rules and proofs are in 1-1

(function PZero LteProof)
(union (elem PZero (lte 0 0)))
(function PSucc (LteProof) LteProof)
(rule ((elem p (lte i j)))
      ((elem (PSucc p) (lte (+ 1 i) (+ 1 j))))
)
; A little demand driven
(function PZero2 LteProof)
(rule (= t (lte 0 j)) ((elem PZero2 t)))



(function elem (Proof) Type) ; This is type theory's `:`

; the path query could be rewritten
(elem p (path x y))

; So a coq inductive types
;Inductive le : nat → nat → Prop :=
;  | le_n (n : nat) : le n n
;  | le_S (n m : nat) (H : le n m) : le n (S m).
(function le (i64 i64) Prop)
; The following would be neat.
; Could it possibly mean anything other than the next two rules?
; (function le_n ((x i64)) (le x x))
(function le_n (i64) Term)
(rule ((i64 x)) ((elem (le_n n) (le n n))))
(rule ((= p (le_n n)) ((elem p (le n n)))))

; This is context free type theory
; {} |- a : T 
; but with inductive types? But no lambda?

; can I 



```
Do we really care about all proofs?
Not particularly. Do we care about all deductions? not particularly.

Can I prove addition commutes?

```
; This is extensional type theory
(rule (proof p (eq a b)) (union a b))

(rule ((proof p (eq a b)) (proof  (f a))
)
```

refl is the only constructor of eq. But, we can axiomatically asert new equalities. I mean, odds are they are inconsistent.

(proof PZeroZero (Eq (plus zero zero) zero)))
This is ok. because we also have a rule that makes it eventually true
(rewrite (plus zero a) a)
if we don't have that rule, I dunno.
Other rules/constants that may be of interest. comp/trans,  sym, 
They reduce to meaninglessness if defined in term of the eliminator
subst(eq,pat_with_holes)

# ASP
I could use foreign functions to implement external union find. With all the associated problems.

# Contexts 
Is the frame problem related? ASP and K seem to be talking about the frame problem. An open notion of context requires frames? typing contexts kind of manually carry their shit through. Could use a frame-like system
Does context put us into non-monotonic reasoning (which _isn't_ synonymous with bad reasoning)?
Resources. Sometimes it feels like we need to _copy_ to make terms in new contexts, like freshening lambda terms. Separaton logic, linear logic, and so on. I dunno. Just spitballn.
ASP + theories might be a good place to look for egglg

ASP has ntion of partial model and well-founded model
Cyclic proofs?



context patterns?
eq(a,b), f[a] -> f[b]
first class contexts - somehow autoderive my zippers?
This is kind of like

Are contexts codata? There is this notion that maybe my lambda encoding shell (\x . foo x  and then set x = \x . foo x) game for alpha equiv could've worked if I had something that recognized isomorphisms in the graph. The game does kind of seem to work for let bindings, becuase let bindings have a canonical name. `let x = 1 in let y = 1 in 1` doesn't distinsuih between the inner and outer in this encoding. Which is fine in a sense. The landin's knot fails because it represents it finite expansions, not it's infinite expansion (stream, codata type).

Ok, crazy talk, are contexts a good place for using the partition refinement data structure.https://en.wikipedia.org/wiki/Partition_refinement. We start in 
Partitiona refinement is very greatest fixed point flavored.
Something to do with the tree automata perspective? Arrows in the egraph are reversed. Reversed arrows is exactly how I define zippers.
My zippers _are_ continuations, which are canonical codata. Our encodings are call-cc, turning continuations into data.
Zippers are defunctionalized continuations?
datalog is natural deduction (? Is that right? what makes something natural deduction? It's just a judgement system. That isn't the same is it?). WHat if instead it was sequent style


https://en.wikipedia.org/wiki/Coffman%E2%80%93Graham_algorithm Hmm. Layered graph drawing. Breaking a partial order into layers.

Hmm. Nadia and jimmy's presentation had a notion of equality that seemed like scoping forms but had something to do with automata.

Hmm obervational type theory became quantitiative type theory? A notion of linear usage became importan
Using eids for unification, diff lists, substitution destroys them.
Using a lambda term in two locatins needs a copy made.
eids are a resource.

partition ids?
You could take a thing and split it. Keep a tree of splits which you can traverse up to containment
a and b are diseqal (partitioned) if they do not lie on the path of one another to the root (representing a <= b or b <= a)
canonicalzatin is taking records with a, b->a<-c and making two records b and c. Destroig over eager equality. Probably we want to be lazier though.
For set feeling contexts, the observations are is x in the context or not. This is eager expansion of power set. 

https://en.wikipedia.org/wiki/Observational_equivalence C[M] C[N] evaluate to same value v for all C, then M and N are observationally equivalent.
https://www.pls-lab.org/en/Observational_Equivalence. Holes are capturing rather than capture avoiding
https://www.cl.cam.ac.uk/~amp12/papers/typor/typor.pdf Somehow this is related to logical relations. Great.

Ok but contextual equivalence is a more concrete thing to target. A meta theoretic framework that can dirctly reason abut this stuff

Varialble capture contexts.
The zipper is a stack frame representation. The other representation is a top down one.

Contextual equality vs contextual equivalence
Contextual equivalence handles notions of references and other things that make sense from an mperative standpoint. That's good. We're squaring the circle between functional and imperative

Delmitted Contexts a la delimittied contninuations. Could this be a way to make the diff list example work


Compare to twelf. No need for terminatin checker. Everything is sound in datalog right?


This thing of tagging vs recusrively tagging is an idea that keeps coming up.
Recursviely tagging with logical context, recursively taggin with programmatic contxt
recursiely taggin with proof

https://pat.keldysh.ru/~grechanik/doc/indprover-eqsat-extended.pdf
https://github.com/remysucre/egg/tree/minimize

Maybe having both modules with database/function associated with them and
modules without corresponds to 



Wht is the meaning of a herbie expression?
[[e]] : (V -> R) -> R 
But sometimes they are partial.

[[Gam |- e]] :  (V -> R) -> Option R
[[x]] = \env -> env x
[[sqrt(-1)]] : ?
[[1/0]] : ?
[[Gam]] : (V -> R) -> Bool

Or is it the execution of a machine
[[(a + b)]] : s -> Error (v, s)


C = list of delimittation points? We could pattern match into that

K framework has a notion of contexts. Confirugatons
# cofunctions
We can't have identifiable objects.
We can perhaps associate a notion of identity to an (incomplete?) set of observations.
Adding an obsrvaton to an incomplete set forks it I guess? observations are edges that connect observation sets. Mostly that's just a product of maybe lattices?

We could perhaps require complete observation at definition time. Or some form of stratification?
Generating all possible objects. Explicitly representing all possible observations is bad seeming.
Also the stream example. What is tail producing?

Internal state? That's better than just an asbtract id. It's skolemized. But objects might be observationally equal even if their internal state isn't.


```
(sort state i64)
(sort action String)
(codatatype part)
(relation trans (state action state))
; (function trans (state action) state) ; DFA
; (observation transp (part action) part)
; ; (observation transp (part part) action) ?
(observaton observe (part part) action)
(relation member (state part)) ; (function member (state part) bool) ?
; (member (state) part)
(function start (state) bool) ; relation?
(function startp (part) bool)
; likewise for final
(rule ((trans s a s1) (member s p) (member s1 p1))
  ((= a (observe p p1)) ) 
)

(rule  ((start s) (member s p)) ((startp p)))
(rule ((start s)) ((member s p))


(rule (= b (start s))  (set (startp (member s) b)))
(rule ((= s1 (trans s a)) (set (transp (member s) a) (member s1)))

(relation not-member (state part)) ; hmmmm.

; The member functin is the problematics part
; Ok, so partition refinement discovers a split
; what happens to member? It keeps old id?
; it gets both new ids?
(function member (part) (Set state))


.decl trans(s : state, a : action, s1 : state)
.decl start(s : state)
.decl neg_part(s : state, s1 : state) ;  not in same partition

neg_part(a,b) :- start(a), states(b), !start(b).
neg_part(s,t) :- trans(s,a,s1), trans(t,a,t1), neg_part(s1,t1). // cocongruence?
// symmettry. this is redundant
neg_part(s,t) :- neg_part(t,s).


// gfp datalog?
start(t) :- part(s,t), start(s), 
part(s1, t1) :- part(s,t), trans(s,a,s1), trans(t,a,t1). // cocongruence?
// equiv relation
part(a,b) :- part(b,a).
part(a,a).
part(a,c) :- part(a,b), part(b,c).

// true... are only linear rules relevant?
// That seems weird.
// Well the maximal eq relation is just everyting is equal to everything.
neg_part(a,b) :- neg_part(a,c), part(b,c)

```


```souffle
.type state = symbol
.type action = number
.decl states(s : state)
.decl start(s : state)
.decl accept(s : state)
.decl trans(s : state, a : action, s1 : state)
// https://en.wikipedia.org/wiki/DFA_minimization
states("a"). states("b"). states("c"). states("d"). states("e"). states("f").
start("a").
accept("d"). accept("c"). accept("e").
trans("a",0,"b").trans("a",1,"c").
trans("b",0,"a").trans("b",1,"d").
trans("c",1,"f").trans("c",0,"e").
trans("d",0,"e").trans("d",1,"f").
trans("e",0,"e").trans("e",1,"f").
trans("f",0,"f").trans("f",1,"f").

.decl distinct(s : state, t : state)
distinct(a,b) :- accept(a), states(b), !accept(b).
distinct(s,t) :- trans(s,a,s1), trans(t,a,t1), distinct(s1,t1). 
distinct(s,t) :- distinct(t,s). //symmetry

.decl eq(s : state, t : state)
eq(a,b) :- states(a), states(b), !distinct(a,b).
.output eq
```
neg_part(a,b) :- start(a), states(b), !start(b).
neg_part(s,t) :- trans(s,a,s1), trans(t,a,t1), neg_part(s1,t1). // cocongruence?
// symmettry. this is redundant
neg_part(s,t) :- neg_part(t,s).


```

Copatterns

```
(codatatype Stream)
(cofunction next (Stream) Stream)
(cofunction val (Stream) i64)

; does the family of obervations need to be closed?


(codefine ((val ones) 1)
            (next ones) ones
) ; it searches, and if it doen't find anyhing it forks it.
;(function ones () Stream)
; (rule (= 1 (val a)) (= (next a) a))  
;        (set ones a))
; else
; (set ones make-part)
```


(cofunction ones
  (hd (ones) 1
  (tl one)
)
cofunction repeat (i64) Stream
  (hd (repeat n)) n
  (tl (repeat n)) (repeat n)
)
;desugars to



;(set (next ones) ones)

(codefine one )

(cofunction coeq () Prop
  (eqhd (= (hd )) ())
)


```
Hmm. This is more like the souffle theory of adts than like egglogs open universe.
Which is maybe fine?
Use expliit coinductive equaliy
An open family of observations is a huge pain in the ass.

partial cofunctions. Can that make sense? seems bad.

```
(codatatype coeq
    (hd Stream )
)
(cofunction
  ((hd a) (hd b)) 
  ((tl a) (tl b))
)

```


partition nodes are like loopy lists
When do we make a new partition.
Closed vs open




Should partition refiement just be a 
Should it just fit into merge? Well, the detection is different.




https://dl.acm.org/doi/pdf/10.1145/3428195
cofunctional dependencies
(cofunction foo)
cid and eid
If in all terms of use, the results are equal, then 
(a -> b)

(cofunction foo (a) b)
if a cofunction maps to two different things, then it's arguments must also

automata minimizatin

(function eval (ctx term) value)
functionall dependent on term
cofunctionally dependent on ctx?

No. doesn't make any sense.

(term, value) -> ctx
term -> ctx... I didn't understand this one from the paper.


Sebastien Erdweg's group has good stuff https://www.pl.informatik.uni-mainz.de/publications/

Very interesting. I somehow had never seen this one https://dl.acm.org/doi/10.1145/3428195 contexts and "co-functional" dependencies in datalog for typechecking (edited) 

https://www.youtube.com/watch?v=1lL5KGVqMos&ab_channel=ACMSIGPLAN it has a video (edited) 

I don't understand this cofunctional dependency thing, but it is tantalizing. It sounds like it jives with a lot of the vibe of egglog. "egglog with coterms". There's a set of vague and confusing ideas that if they could fall in place would be aesthetically appealing. Automata and observational equivalence, context/scope ids and eclass ids, partition refinement vs union find, terms and coterms, functional and cofunctional dependencies. (edited) 


Max Willsey
  10 hours ago
vibe driven development

yeaaa, it's an embarassing mantra. This mode of thinking has basically never actually worked for me. But it feels so good to think you're on the edge of something that I can't help myself. (edited) 

It's kind of a road to crankhood.

Max
I am sympathetic for sure

Lemme throw this one out there. (cofunction foo (A) B) . Maybe (observation foo (A) B) . It runs the contrapositive of congruence. If two rows of a cofunction map one partition to two different partitions, then the input partitions must be split/refined https://en.wikipedia.org/wiki/Partition_refinement. `f x != f y -> x != y` This seems like a thing that can be done. Not clear on it's utility (edited) 

This meshes with the idea that the good way to discover disequality on two things is to find some analysis that maps them into two different bools or different constructors or disjoint intervals or transitively to disjoint things (edited) 

I'm assuming partition ids (does that concept make sense?) and eclass ids are separate notions (edited) 

cofunctional dependency violations expand rather than merge

partitions of eids? (which would be a curious flavor of first class set) (edited) 

Maybe this is almost the only notion of first class set that isn't terrible. You can only refer to sets for which you have a known separating observation. Primitive datatypes are all separable (decidable equality) so referring to any of their finite sets are conceptually unproblematic. (edited) 

Canonicalization takes any record with a reference to a set that has been further partitioned and expands it into one record for each of it's partitions. Again, kind of dual to the egraph canonicalization. Expanding instead of contracting. Maybe the expansion should be lazy or implicit in some way, since expanding is bad. (edited) 

If partitions of eids is the right thing, at least the number of partitions is bounded above by the number of eids. So maybe expansion isn’t so terrible

I wonder if this could have any bearing on AC, since AC is about sets/observably distinct sums. Might as well pretend it does since I'm pretending to touch all the other big problems (disequality, sets, and context)

Partitions of eids in this way gives semidecidable disequality. If two different eids are in the same partition, you can conclude nothing. If two eids are literally, equal, they're equal. If they are in distinct partitions, they are provably (observationally) disequal (edited) 

:merge is like a fold or reduce. :expand is like an unfold

Actually merge is fold not reduce. We sometimes are usefully asymmetric between old and new (like the choice domain example)

But we don’t allow heterogenous typed merge?

Nothing in the operational semantics prevents heterogenous merge afaik. It’s the type system that does.

I wonder if Remy’s tree automata transformation could be literally performed internally in egglog by making rules transferring a function representation to a cofunction representation


Another way of putting is is one can coresolve a function dependency violation by splitting/changing/deleting inputs rather than merging outputs

I’m a little manic, but I’m pretty pleased with this idea


A particular kind of weird special case that seems particularly useful is partition refinement, like how unionfind is a weird special case of merge

Because they both cause this spooky action at a distance that is globally effecting things in a way unlike how lattice datalog is local

A fairly generic way to resolve functional dependencies is to just give a method that takes in a set of violating tuples and returns a new set of non violating tuples


parition refinement

Abstract refinement via ids.
Notions of compression? Forest?
```python
class Refiner():
  def __init__(self):
    self.parents = [0]
    self.leaves = {0}
    # self.left
    # self.right
  def split(self, x, N=2):
    if x in self.leaves:
      self.leaves.remove(i)
      n = len(self.parents)
      for i in range(N):
        self.parents.append(x)
        self.leaves.add(n+i)
      return n
  def subset(self, i, j):
      if i == j:
        return True
      while self.parents[i] != i:
        if i == j:
          return True
        i = self.parents[i]
      return False
  def expand(self,i): 
    # expand a non root to all it's leaf children
    # the analog of find.
    # This could be "compressed" I guess.
      if i in self.leaves:
        return i 
      else:
        yield from self.expand(self.left[i])
        yield from self.expand(self.right[i])

```

A partition _of_ eids needs
```python
class UF_partition():
  def __init__(self):
    self.parents = []
    self.partitions = [[]]

  def makeset(self):
    x = len(self.parents)
    self.parents.append(x)
    self.partitions[0].append(x)
    return x
  def refine(x, ):


```
Is partitions a annotated BDD of sorts?
Everything that points to the empty set of ids should be compressed.
ZDDs?
We need to pick an ordering to the questions. Hmm. Don't love that.
The set only has N elements in it, so that limits how bad it can get.

Or we could just label the partitions by their question signature vector.
is_red = true
smells = Unknown

There is no notion of disequals.
Or registering something as a cofunction allows iteration over all cofunctions

Abstract partition id as domain of cofunctin. That might work.
How to hook up x eqable, y splittable. The elem relation.
The elem relation is many-to-many. If we can canonicalize saprtition id's, it is many to one, a function from object to partition.
It's almost a master observation. A cofunctin for which there will never be a true conflict by design. 

( should-fail )


What about a prcoess that is doscivering obervations (which may also be new states)
And dfa minimizatin is performed on the database every iteration
Thing end up in partition. Being in a partition does not mean observationall equal
In different partitions does mean observationally disequal?
what about evntually discovering a loop that makes it equal to an old loop?
partial observations

automatalog : Automata as a datalog database
Set databases need deduplication
Egraph as a database uses the hash consing action
Hashlog
Automata 

A notion of compression, deduplication, propagation


observe as an action / head of rule
(observe e (foo a)) Looks a lot like define.
(observe (foo a) e) looks like set


Automatalog
Automata Minimization at each stage. New observations fork states? They then get deduplicatin by automata minizmiation

DFA is analog of Pathlog (unary constrcturo egglog)
Tree automata is analog of Egglog?

use python + ducklog as core?
Use rust just for fun? Reuse parser

There is state and you can pattern match into it?
val (iter N) = N
next (iter N) = iter (N + 1)

States have names. But the system does coalesce them into observable equal partitions.
 :-  7 = val s, (s is partition) 
(iter (n + 1)) <- next (iter n)

If we never called make-set it's straigtforward-ish
But if we do, blegh.
So once we build this index we can have known disequality.
Mybe the diseq table is better?
Can I get a stabe name of partitions between iterations?
Hmm. Inequalities/Intervals don't work. Not without a programmable notion of what it means to be known disequal.
Obervations are filters, monotonicity closed sets.

We can support part(eid) != part(eid2).
part(eid) = part(eid2) doesn't mean anything.

ok.. 
foo(1) foo(2).
bar(foo(2)) = 7
Is foo(1) observationally distinct? No. because we don't know what bar(foo(1)) might end up being.
So there can't be a partition.
So none of this makes sense

# Backchaining - harrop
If you're willing to run forked or interleave coroutined databases in parallel you can lift or and exists to Goal.


So what is the thing I'm avoiding? Ever actually performing resolution.

Generative metaprogramming like metaocaml. THe thing I'm constructing is opaque. I don't pattern match on it.

THere are layers of signatures
sig1
sig2
prog1 - building up a rule
prog2 - rule set

---------------
sig1, sig2, prog1, prog2  |- goal

The egraph database itself holds sig1 sig2.
Perhaps identifiers are living in sig1 and eids in sig2?

The trick is to never have to look in the program set.
I suppose I could have a hierarchy/tower of prog and sig?
Hmm. Could I use hierarchcal scheduling for this?
The context is structured. Which is interesintg. It's 
G 0 := PrimGoal
Prog 0 := G 0 => Prog 0, 
G (S n) := 
Prog (S n) := 

Go up a layer?
It's defintely a metaprogrammign feel to datalog.

Is there a logic that reflects this? Maybe some kind of modal metaprogramming thing like pfenning

I can definitely support existentials in the heads.
So I'm not done.
Barendregt convention.


Exists is not easy.
Neither are implications.
Both are doable in lambda prlog
Is magic set the way out? Magic set is a partial evaluation of prolog to datalog.
It is an abstract intrpretation of datalog also. a datalog analysis of a prolog program.


https://ncatlab.org/nlab/show/geometric+theory Hmm. Geometric theories look like Q formula
Geometric theories are datalog? eh. naw. They allow Q formula in the head
THe infinitary \/ is concerning

## Observational Disequality
Some chewing on observational disequality

Rolling back on the aggressiveness of the cofunction idea.

The union find is good because it factors an `N^2` equality relation into the linear sized root relation. Also having the root relation baked in makes the system more performant and easier to use as compared to manual congruence rules and manual root relation maintenance rules.

Factoring the `N^2` disequality relation seems desirable for the same reason. I think it is possible to factor this relation into a a relation mapping each eid to partitions of the eids. These partitions are ultimately grounded in primitive notions of disequality.

Some combination of datatype + merge function has a notion of disequality. `Nil != Cons`. primitive true != primitive false. Shrinking intervals can be known to be disjoint `[0,1] != [2,3]`. More generally, lattice values can be known to be in disjoint filters. I think this is a reasonable core of from where disequality comes from.

One function mapping into such a type produces a partition on it's input. `(function even (Math) bool)`

A Math expression x either has 1. `even(x) = true` 2. `even(x) = false` 3. `even(x)` not filled in.

If `even(x) = true` and `even(y) = false`, then x can never be equal to y. This is the contrapositive of congruence `f(x) != f(y) -> x != y`.

Hence, `even` generates a partition of two options. The elements that do not have a binding must be associated with both options unfortunately.

There may be multiple such functions of course. The combination of them produces many partitions.
There may also be transitive disequality. A `(function neg (Math) Math)` also can pull back known disequality on the outputs to the inputs even though

Multi-argument functions are a bit less powerful. The only inference in general you can produce is `f(x,y) != f(z,w), z = x -> y != w`.

An approach to doing all this is to regenerate this partition table during each rebuild, in the style of the throwaway union-find version of egglog. It is probably possible to do incremenetally, but it is more confusing.

The partition table is generated by a process very similar to the congruence propagation process. Because N binary observations lead to 2^N partitions being defined, it does not seem desirable to represent them explicilty. Instead using a variation of the partition refinement data structure that allows elements to stay in multiples of the partitions (in case of the observation being undefined) seems better. I am being vague here because such a data structure feels doable, but I'm not quite sure.

Then when a user asks x != y in the query, it looks up the partitions x can be in, and the partitions y can be in, and see if there is any partition that both can be in. If not, then they are known disequal.

Fresh eids could be in any of the partitions until they start gaining observations.

The story could be a bit simpler if observation function were _total_. That during the introduction of a new eid, one has to specify a complete set of observations. But it seems to go against the philosophy of egglog to require this.


A :disequal annotation for intervals?
eids have the default notion
primitives also have a default notion.

This again parallels equality discussion, although we didn't need :equals annotions. I guess this might be a way of discussing alternative mediation strategies on a per function argument / result basis.

The mediation needed for congruence vs query is different.


Does this have bearing on observational _equality_? Things that are currently observationally equal can become not observationally equal unless the set of observations is closed. Hmm. What about some kind of default logic? Non mnonotnic.
One could perhaps _require_ the set of observations to be closed. The root of the term is the only observation ofr example. 
It might be easiest if New observations only come from users. And they need to state them all before they hit run.
Or state them in a block with th introduction of terms. 

closed vs open and partial vs total seems to matter a lot in terms of what makes sense.
Also maybe strata / user given / metaness. The user is strata 0 in some sense. The most meta.


Sorts also give a primitive seperator of eids. But we don't even allow you to ask if eid1 != eid2

Side note, sorts also give you an a priori separator of eids. We don't even allow you to ask heterogenous a:S != b:T  but it's kind of intriguing.



# Prolog vs egglog

I feel like what prolog is doing is there is a fact under consideration of unknown truth exists x, append([], [1],x) .  This becomes append([],[1],X) . The truth of this fact remains unknown. I could model this as `(append  (nil) (cons 1 nil)  (skolem2 append (nil) [1] )


A prolog goal is exists x, append([], [1], a).
It is of unkown truth value.
(function append (list list list) True)


We skoelmize this goal and seed the question.
(I guess we could global skoelm if this is a global question. this is similar to lambda lifting)
(append (nil) (cons 1 nil) (skolem1))


So here is an attempt to model prolog inside of egglog.
I model prolog prodicates as functions to lifted unit.
If it points to `(proven)`, this is an asserted fact.
If doesn'y point to `(proven)` yet, this is a demand/question.

In prolog question are asked at the repl prompt.
Facts are asserted in the database.

a(X,Y) :- b(), c().
A normal form of prolog could require unique variables in the head, with explicit = in the body.
What does a rule compile into in this model?

(rewrite (head )
         (conj   ,Eq(a,b),   ))

(append [] a a)

This asserts new _questions_ about equality.
It does
(rewrite (append a b c)  (conj  (eq nil a) (eq b c)))
Hmm. Does this kind of do something funky with multiple rules?

(rewrite (eq a a) (I)) is fine

(define (append nil (Var "a") (var "b")))
Given (var "a") = (var "b") this succeeds.
You could extract (append a b c) to get different branche of the prolog search, and see if they have a unification solution. That's kind of interesting. It can extract all the prolog goal chains that don't egglog finish. Will anything block?

This is egglog metaprogramming for prolog kind of. Pretty neat. Partial evaluation of prolog?
But it fundamentally doesn't do unification.
The branches interfere.
But it does everything up to that.
Is that useful?
If extraction _knew_ that it needed structural unification under (Eq a b), that is kind of interesting.

It's kind of a brother of the extract normalize methodology for lambda terms.
It's extract, unify.


Producing new vars... exists?

prolog:
path(x,z) :- edge(x,y), path(y,z).

Where does y come from?
(rewrite (path x z) (conj (edge x y) (path y z))

 exists y, edge(x,y) /\ path(y,z) => path(x,z)

?
 (rewrite (path x z) (conj (edge x (trans x z)) (path (trans x z) z))

But trans x z will never unify with anything. and it won't be in edge.

rewrite (query env (path x z)) -> query env


This is making prolog as multiset rewriting.
The set is represented as conj.

So what?




Ok let's assume there _is_ a way to make this work. How?



(union (Clone usize) (I))
(rewrite (Clone (Vec A)) (Clone A))


```
((subst (fvar a) a b) )
```
Maybe the preprocess unin find is smart?

A prolog query can be ?- append([], A, B) and prolog would return A = B . I can ask ?- append([], [1], [2])  and prolog will fail.

ok
(rewrite (append nil a) a). boom.
ok.
(= (cons a b) (cons b d)) (!= a b) defive constradiction boom.

so is append fine because it is functional? So I need a non function example.

append(A, B, [1,2,3]).
I mean yes, I can derive all the solutions to append. Fine.

length(a, N)

lenght(nil , 0)
length(cons(A,Xs), N+1) :- length() 


(rule (length X) length()

append(A,B,C).

write rules for every modality of use.
why is returning the abstracted result so important?


Is the only difference that prolog can return a very big result very compactly if unification variables are left in the 
But the same holds for datalog. How is this changing anything?
magic set + includes sig and clauses?



CHR + ELPI to get a union find.


Unification variables are standins for something unknown but to be determined or perhaps representing an infinite class of all possible terms. Eclasses are standins for a constrained set of terms. 

Perhaps one way of looking at it is that prolog unification vars in answers are universal quantification, whereas egglog eclassids are bounded (over all terms in that eclass) quantification in answers. Semantically, since everything in the eclass is equal, there isn't any quantifaction at all. It's a quantification over a thing of size 1. Prolog is quantifying over a _ton_ of stuff.

uvars in queries are existentials, eclass ids in querie are... like term famillies??




What about <= as an example? A true relation
le(A,A).
le(A, succ(B)) :- le(A,B).

vs

le(z,A).
le(succ(A), succ(B)) :- le(A,B).


Non destructive subsittitution.


So Max shows that append in functional form is useful for demand on last argument. What about mutiple demand projectors.

append(A,B,[1,2,3]) --> demand1([1,2,3]) demand2([1,2,3])
eh. But there aren't unique solutions.

Egglog can be subservient to prolog (carried egraph. CHR possibly)
prolog subservient to egglog (called as FFI)
interpreters can be embedded.

ELPI CHR could get us a harrop enabled carried egraph.
Is putting unification variables in there ok? Seems like no.
It'll try to unify them to random garbage... uhhhh. we could guard on groundness. {ground(A)}
Or store ungrounded separately
unground(eid, X) <=> {}

Or
eclass(eid, uvar(X)). not eclass(eid, X). use a whatsy representation like triska says.
uvar(X, eid) is the flat representation of this.
uvar()
We do _not_ want the rule `uvar(X,E), uvar(X, E2) <=> link(E,E2).`
Detecting when X has been refined is tricky.
uvar(X, E) <=> {nonvar(X)}, refine(X,E).

The prolog to datalog translation:
A query becomes a demand predicate. The pattern of variables is different demand predicates. Traditional datalog has a countable number of demand forms for a single predicate. Datalog with terms does not obviously have such a countable form. 
D
A prolog clause becomes demand propagation clauses and answer propagation clauses. They are different interleacvings of demand possible.
Demand overapproximation is not a problem, although asking for more than needed. Answer underapproximation is not a problem, although hurt completeness.
With datalog with lattcies and egglog, answer and demand relations can be collapsed somewhat (hmm maybe not). Maybe types can be useed in _just_ demand to collapse all different demands to one.
Informatiobn passing strategies, One could imagine a prolog that executes all its goals in parallel rather than in sequence. Then it would merge them together in the asnwer pass. This is still a reasonable prolog variation.



Without first class union find, there is no notion of variable in answer?
If we can predict all possible shapes of answers, we can ahead of time make different answer predicates like we did for demand. Unlinked variables are fairly encodable as just a $Var.
Egglog might enable first class uf keyed. This is reminscent of my failed attempts in z3 to make a first class uf using uniterpeted functions.
uf(key,a) = uf(key,b) whre key is a label of the union find. Generating fresh keys is the job of skolemization.
(sort ufkey)
(function named_uf (String) ufkey)
(function uf (ufkey List) List)

(union (appendrule ufkey x) (uf (appendrule ufkey) y)) :- (demand )  (append ufkey x y z)
% if intended to be accumulating. Is there some way to get this by congruence?
(uf (appendrule ufkey) x) :- (uf ufkey x) = (uf ufkey y)
uf is apply. This is the usual first order named function encoding stuff.
Demand driven style
(rewrite (eq (uf (succ k) x) (uf (succ k) y))  (when (eq (uf k x) (uf k y)))

it is difficult or impossible to recover function extensionality
forall x, f x = g x -> f = g
That forall... maybe it's ok if the (partial) functions aren't going to become more defined. It isn't currently available though.

first class sets at  (function fcset(key a) Proof). We guarantee we'll never add to them. Nah. That's not good enough

These variabes _are_ branch local because we have a backtrackable egraph. The egraph operations will _never_ unify uvars.
=======
if x != 0 then 1/x else 0. 


Generalized union find- szalinksi, mark functions as invariant? Could we end up in eckert territory? Symmettry reduction of functions

groupoid. I don't really need totality. But equality modulo g-action has a unique arrow between. How can one deal with that? Attaching a set of groupoid elements (homset) between each object? path compression may then cartiesian expand these sets. Yikes. Porbably it's worth keeping as expanded as posisble or even defactoring.

hom(a,b) * hom(b,c) has a meaning. so does hom(a,b) * hom(a,c)^-1


Is congruence happening at an inner strata? Or rebuilding?



I just had a totally crazy idea walk

the generalized union find seems like it can be further generalized from annotations consisting of group elements to groupoid elements

Similar to how lattices are an algerba with meet and join, or a partial order
Groupoids are categories with reversible arrows or groups with _partial_ multiplication

The idea of a lattice is generalized mechanically in egglog to merge and default annotations which can refer to egglog functions themselves.
This enables symbolic lattices. These might actually be partial lattices as max has alluded to

Similar I think the group annotations can be written as
`(datatype MySort :compose :inv :id)`

And these functions can refer to egglog functins themselves, not only primitives

Groupoids are interesting because they are somehow related/generalize equality in the first place. They having something to do with HoTT like talia has been suggesting.

A canonical example of a groupoid are paths in a graph and path composition. This means that groupoid annotations seem like they can be used to implement proof recording, as that is essentially what proofs are in a proof producing union find.

These proofs can be reflected into an egglog datatype and the proofs may have their own interesting notion of equality or merging.

The manner in which group annotations propagate through functions is reminiscent of the setoid rewriting system in coq https://coq.inria.fr/refman/addendum/generalized-rewriting.html by which you can add . The group anotations can be seen as talking about equivalence quotiented by some group action in some contexts. This is a methodology for dealing with quotients.


isomorphisms are groupoids. We could annotate edges with isomorphisms.

Perhaps trying to model homotopy itself is clarifying

permutations are  group - nominal sets. permutation as a model of commutativty

add(x,y,z) = add(y,x,z)
But this requires us to have the group act on the tuple.
The eid of the add itself is a tuple? yesss. but this doesn't mesh
The group has to act on elements?

We can now express this.
P cons(b,cons(a)) = cons(a,cons(b,))

Before they are of no relation.
Before I could say
cons(a,cons(b,nil)) = cons(b, cons (a,nil))
But now I have a new notion of "equals". But I don't dave anything?
Well I can have permutation invariant functions without having them be literally equal.
(P a)
This is a sutble capability. But it is neato I guess.

We get the sharing of uses of them, without having them become indistinguishable.
"Benefits" of commutativity without actual requiring the axioms.
Functions that "don't care" ca store only root eid but not group action offset.

like a function
length() : list -> nat
contains() : list -> nat

This generates all permutations
rewrite cons(a,cons(b,xs))   swap * cons(b,(cons(a,xs)))

add(x-gx,y-gy,z-gz) --->   add(x,y,z, gx*gy*gz) what if we stored only some combo of the group offsets, but not all of them individually
Or some projection of and individual group annotation.

These are all possible. why would you want that
We can share all the orderings between mulitsets and lists.

A multiset is a list quotiented by it's permutations.
We can observe the ordering when we want to and ignore it when we don't

G-sets. And we can talk about quotients

if i idenitfy eids as objects, then there are sets of groupid arrows between.
Am i annotating the edges (a = b) -> annot
(a = b) * annot?
annot -> a = b 







# Logical models
f(X) -> a
f(X) -> b
needs to find an f(X) before it can fire.
X needs to be inhabited.

expanded form
forall X E, f(X) = E -> a = E

Logic has bidirectional equaloty. It doesn't have a good univdirectional equality.
forall X, f x = foo   does show there is something needed first  

```
tff(x_type, type, xty : $tType).
tff(a_type, type, aty : $tType).
tff(a_def, type, a : aty).
tff(b_def, type, b : aty).
tff(f_def, type, f : xty > aty).
tff(ax1, axiom, ![X : xty] : (f(X) = a)).
tff(ax2, axiom, ![X : xty] : (f(X) = b)).
tff(goal, conjecture, a = b).


Axiom X : Type. (* (dataype X) *)
Axiom A : Type. (* (datatype A) *)
Axiom a b : A. (*  (function a () A) (function b () A) *)
Axioms f : X -> A. (* (function f (X) A) *)

Axiom ax1 : forall x : X, f x = a. (* ? (rewrite (f x) a)  *)
Axiom ax2 : forall x : X, f x = b. (* ? (rewrite (f x) b) *)

Goal a = b. (* (check (= a b)) *)
```


?????
assertion universal proprties
(rewrite (foo a) (True)) is a meta level assertins of (forall a, foo a)
(rule () (foo a)) is also, but doesn't work since a isn't bound.

(forall x (foo x)) requires a binding form
Kiselyov points out that unifcation variables were a way of performing lazy herbrand universe enumeration
(rule ((univ a)) (foo a)) is a form of this.
These are all assertions of universality, not discovery.
We can perform a compile time shift like my category examples. Make fresh constant. If something is proven for this constant, for which the only assertion is that it is (univ fresh). This is performing meta level lambda prolog reduction though / intros backward reasoning.
Or rather, you can embed this but it gets stuck at the first choice point. That's interesting.
(rewrite (resolve ctx (forall x g))  
  (define y (fresh g ctx))
  (resolve (forall ctx) (subst y x g))
)
This is also alpha equivalent
(resolve ctx (=> a b)
    ()
)

Is embedding a full prolog intepreter including choice point really that bad? Maybe that's the way to do it. You do get a prolog that works modulo rewriting.



### Chalk
# Egg Chatathon 2022-10-31

## attendees

* elirosenthal
* max willsey
* remy wang
* oliver flatt
* philip zucker
* niko, jack

## notes

Chalk: https://github.com/rust-lang/chalk/

### The problem

We have associated types and their a pain in the butt
.


```rust
trait Iterator { type Item; }


impl<T> Iterator for Vec<T> {
    type Item = T;
}
//
//
// forall<T> { normalizes_to(<Vec<T> as Iterator>::Item => T) }
```

```
X = <P0 as Trait<P1...Pn>>::Item
---------------
<P0 as Trait<P1...Pn>>::Item == X


normalizes_to(<P0 as Trait<P1...Pn>>::Item, X)
---------------
<P0 as Trait<P1...Pn>>::Item == X
```

```rust

```

Leads to: https://github.com/rust-lang/chalk/issues/234
One test: https://github.com/rust-lang/chalk/blob/cadaba9881d78c9814d966e595cc978e64a8b76e/tests/test/projection.rs#L163

```
fn foo<T: Iterator>()
where
    T: Iterator<Item = u32>,
    T: Iterator<Item = <Vec<u32> as Iterator>::Item>
{}
```

```rust
trait Trait1 {
    type Type;
}
trait Trait2<T> { }
impl<T, U> Trait2<T> for U where U: Trait1<Type = T> {}

struct u32 {}
struct S {}
impl Trait1 for S {
    type Type = u32;
}
```

```rust
exists<U> {
    S: Trait2<U>
}
```

```rust
impl<T> Foo for Bar<for<'a> fn(&'a T)>
where
    for<'a> T: Trait<'a>
{
    
}
```

frex -- library in idris to extend normalization procedure done by type checker

smt solvers do something related

## GATs

```
normalizes_to(<P0 as Trait<P1..Pn>::Item<Pn..Pm>, T)
normalizes_to_trait_item(P0..Pm, T)
```

## 

```rust
trait Foo<b> {
    type Item;
}

impl<'a, 'b, T> Foo<b> for &'a T
where
    'b: 'a,
{
    type Item = u32;
}

fn main() {
    let mut x: u32 = ...;
    let p = &x;
    x += 1;
    ...
}

fn foo()
where
    for<'a, 'b> ('b: 'a => fn(&'a &'b u32))
{
    
}

```



Ok so we can put only ground (including universal introduced guys) in.



append([],X,Y) :- ground(X), ground(Y), X = Y.
; This is kind of the analog of taking a prolog goal append([],x,x) and accepting it, but not append([], X, Y).
(rewrite (append (nil) a a) (I))

; I don't know what this is from a prolog perspective. It's like a retroactive conclusion from a succeeded goal.
; it depends on the functional nature of append. This is not a general prolog feature.
(rule (= (Proven) (append (nil) a b))  (union a b))

; This is kind of like a prolog rule. It's not performing unification on the variable though.
; congruence kind of performs some of unification, the destructuring part, from bttom up instead of top down.
; 

(rule (= q (append (nil) a b))   (set (append nil a a) (Proven))  
                                (set(append nil b b) (Proven)))

What egglog rule can take the _question_ (append nil [1] skolem) and (union [1] skolem) 
(rule 
  (append nil a (skolem b))
  (union a (skolem b))
  (append nil a (skolem b)) = true
)
No. I don't like this.
I can write a purely functional intepreter of prolog. I can do this here. The question is can I do it shallowly

(rule 
  (append nil a (skolem b))
  (union a (skolem b))
  (append nil a (skolem b)) = true
)


First class UF. Max's bar napkin seemed to be saying :merge could do it.
I said you can bounce between two UFs and converge if you have good properties.
Do this internally to egglog?






`(append  (nil) (cons 1 nil)  (skolem2 append [] [1]))


If we expose < on eids, we could also make a set datatype that bubble sorts itself.
Or really tree bubble sorts? (it doesn't have to be a list).
Then it's somethign like an (unbalanced) binary tree.
It at least won't 
By the laws of egglog, we can't tell if something will nevr be in it, 
but we can tell if something _is_ in it, and we can recoever set extensionality.

It's pseudo canonicalization

In addition

a + (b + (c + d)) --> (a + b) + (c + d) 
No. For assoc we could just right assoc.
That's canonical.
Commutativity then would bubble sort.
Maybe useful in a hierarcical scheudling system. bubble sorting may be usefu.
This all sounds like bullsht

Is the first class union find stuff bettr really that just using built in Map?
Eh. It canonicalizes.

first class uf is simlar to first class set using keys.
elem( x,s ) is similar to root.
One could do an elem driven definition.
A valid uf rule is (union i j (union k l uf)) = (union k l (union i j)) but I've nt rempted tov use that one.
It produces a new union find (union i j uf) which sucks.
union is analog of (add-elem x s)
(elem x (add-elem x s)) (True)
(elem x s) => (elem x (add-elem y s)) 

A set is a map to true/false.
A uf is a map to uf vals.
a dict is a map to someting.
So it's all kind of the same stuff.

An assoc list is a map. Do we consider assoc lists extensionally? not usually. If so I'd compile it to a better (canonical) structure and compare those.


egglog is knd of a functional programming language. You could designate roots and have a GC run durring rebuilding



Egglog can emulate prolog. There is no question there. Egglog has pure functional programming as a subsystem, and you can write a purely functional prolog interpreter.
A measure I think of how close egglog is to prolog is to attempt to build as shallow and simple intepreter of prolog as possible.
When you write a prolog interpreter in prolog, you can borrow so many capabilities of the host language that it is trivial. You can make each of the capabilities in turn more or less explicit depending on how you want to modify the stock behavior.
The two main things (the essential components of prolog) to try to borrow are unification and nondeterminism. Basically, you can't borrow both in egglog to achieve prolog behavior.

Borrowing egglog nondeterminism, you can use non deterministic rewrite rules in the interpreter picking what search path to go down. However, now if you ever unify something it happens across all branches, which is incorrect. You can fix this by carrying around a first class union find.

If you make the nondeterminism explicit by carrying around a choice point stack in the interpreter, you can use skolemization and egglog union to do some aspects 

Prolog variables `X` are not just one thing. 
Prolog consits of a query pass working backward from goals, searching for proofs. Upon finding the proof, there is an very implicit forward pass consisting of essentially return.
A unification variable in a goal/query is attempting to find a proof to an existential question.
A unification variable in the answer is the assertion of a universally quantified statement.
A unification variable in the head of a program clause is a universal quantified variable for that axiom.
A unification variable appearing only in the body of a program clause is a existentially quantified variablle.






In any operational sense, the relations in the body of datalog rules are smantically very different from the predicates in the head, despite having the same syntax. The body is patterns, and the head is actions.


So the choices are:
- Use a backtrackable egraph controlled by an external process to acheve prolog backtracking. Then unification can be rolled back.
- Use egglog nondeterministic rule application for prolog nondeterminism, then you can't use the raw global union find for prolog unification because it'll interfere across branches
- 



elem absoprtion + list association give us a close to extensional set.

; elem def
(rewrite (elem x (add y s)) (elem x s))
; add absoprtion
(rewrite (add x s) s  
 :when (elem x s))
; union is append
(rewrite (union (add x s1) s))  (add x (union s1 s)))



first class partial functions
Maybe I can write a metainterpreter

(datatype PFuc (Set x y PFun ) (Empty))

(Set x y f)
(Set x y f))

(rewrite (Set x y f) (Set x (merge y z) f)
 :when (= z (apply f x))
)

(rule (((= () (Set x y f)) (= z (apply f x)))
   ((set (apply (Set x y f) x (merge y z))))
))

(rewrite (apply (Set x y f) x) (merge (apply f x) x))

(rewrite (apply (Set x y f) x) (merge y x) 
  :when (= z (apply f x))
)
(rewrite (apply (Set x y f) x) default)




algerbaic theory of defaultdict
and mergedict. These are not new entities you know. The union find dict



Hmm. We can't detect when two intrinsic relations are "equal" either.
That's what we're asking of our first class entities.
Hmm. And I'm keeping the old one...


(= (apply "foo" x) y)
is not complicated. Almost too hokey

(= (apply "edge" (tup2 x y) ()))
(= (apply "path" (tup2 x y) ()))
This style is "borrowing" egglog ematching.

My fixatiom on this frst class set problem is dumb. What do I even want it for?
It's a square peg for a round hole

Theory of big sum

; big commute / assoc
(sum x (sum y e)) (sum y (sum x e))
; big dist
(rewrite (sum x (* (Lit c) e)) (* (Lit c) (sum x e))
(sum x (+ y z)) (+ (sum x y) (sum x e)))

(+ (sum x e1) (sum y e2)))  (sum y (+ (subst x y e1) e2))



factor. This one is tough
(sum x (sum y (* e1 e2))   (* (sum x (interp t1)) (sum y (interp t2)))
:when (= t1 (free x e2)  (= t2 (free y e1)))

Nah this doesn't work
Kind of feels like that nbe example.

; copy everything out.
(rewrite (free x (Var y)) (TVar y))
(rewrite ())


(sum x (sum x e)) is factorable because it is shadowing

(rewrite (sum x (Lit c)) (Lit (* N c)))
(rewrite (sum x (Var x)))
The rapier feels a lot like
{x} |- t

lift {s} (x)

always have minimal thingo in context and explicit lifts to new contexts.
{} |- zero

{x} |- x

union(a,b) |- a + b

context really gets help from metaprogramming
But of course I should go manual first.

freevar(x) = {} _if_ we maintain lift discipline

lift({a,b,c}, e)

sum x (sum y (* (lift x e) (lift y e)))

lift is an anti binding site.
lifts will show up in all rules. v annoying.

binomial coefficients and the knuth book



exact reals...
How do they fit in. Demand...
(demand x eps)


Push anythign interesting into public.
Make separate egglog notes
Suggest the mdbook


# Resolution
;(datatype Bool (True) (False))
;(function PosOr (Bool Bool) Bool)
;(function NegOr (Bool Bool) Bool)
;(rewrite (PosOr True c) True)
;(rewrite (NegOr False c) c)
; assume normal form associated to right like a list.
; False = Nil

; "append"
;(rewrite (Or (Or a b) c) (Or a (Or b c)))
;(rewrite (Neg (Neg c)) c)

;(rule ((= t1 (Or a b)) (= t2 (Or (Neg a) d)))
;      = (Or t1 t2) (Or b d)
;)
;(check (!= False True))

;(rewrite )

;(run 10)

; true is part of bool?
; (assert (PosOr False Nil)) ; assert (NegOr False)
;(datatype Clause (PosOr Prop Clause) (NegOr Prop Clause) (Nil) (True))
;(rewrite (PosOr True c) True)
;(rewrite (PosOr c True) True)
;(rewrite (NegOr True c) c)

;(function append (Clause Clause) Clause)
;(rewrite (append (NegOr a b) c) (NegOr a (append b c))) 
;(rewrite (append (PosOr a b) c) (PosOr a (append b c))) 
;(rewrite (append Nil c) c)
;(rewrite (append True c) True)

;term indexing
;(relation contains (Clause Prop) Bool)
;(rule (= c (NegOr a b)) (contains (NegOr a b) a)
;(rule (contains a b))

; Try using (Set Bool)
; Or just go for AC on clauses

;(check (!= True Nil))
;(relation axiom (Clause))

;(function and (Bool Bool) Bool)
;(function or (Bool Bool) Bool)
;(function impl (Bool Bool) Bool)
;(function not (Bool) Bool)
;(union (not True) False)
;(union (not False) True)
;(rewrite (not (not a)) a)

;(rule ((
;    impl a b
;)))


;(datatype Clause (And Clause Clause) (Lit Bool))
; if we attach a first class uf to clause, maybe we can have full resolution?


## Paper

An alternative to the standard SLD resolution of prolog is SLG resolution, also known as tabling. Tabling is a form of memoization for prolog. In tabling, as the top down search proceeds, when a new goal is found, it is registered as in a table and a continuation is saved to receive possible answers to this query. In this manner, loops in the execution can be detected and terminated.

Tabling increases the completeness and improves the termination properties of the prolog search. Programs that fall within the datalog fragment will terminate under tabled resolution and in this sense tabling is similar to datalog. It is however, considered to be much more complicated to implement efficiently.

In a sense, datalog is half of tabling, only producing the answer side and not the query side.





### Reflection and Truth Values
It can be useful to reflect facts in the egglog system into terms to be reasoned about, particularly equationally
Boolean algebra is a familiar equational structure for reasoning about logical quantities. It is a natural algebraic system to consider in an equational egraph reasoner.

(datatype Bool (True) (False))

Indeed equality itself can be reflected into a predicate

(function eq-math (Math Math) Bool)
(rewrite (eq a a) True)
(rule ((= True (eq a b)) (union a b)))


It is an idiom in datalog to create two predicates, one representing the negation of the other, p and not_p. A tuple being in negative one is the positive assertion that the predicate does not hold, while a tuple being in neither represents an unknown state.

In egglog this doubling of predicates can be represented more naturally by a function to Bool. 
A lattice datalog can represent the lattice of (unknown true false)
This has the extra expressivity of allowing two truth values to be of unknown but equal truth.

Negation and falsehood in the context of datalog is a subtle topic. Just because a fact does not hold now, does not guarantee it will not be discovered to hold later unless the rule set has been saturated. Proving a relation to be definitely False is subjectively not a natural fit to a system with this character.

An alternative notion of truth value that better reflects this feature of datalog is

(datatype True (I))

This datatype has analogs in dependent type theory and in the Marshall B system and is some sense "half" of a boolean. Any eclass of type True that is not in the eclass of (I) is not intepreted as false, but instead as unknown. This state can be useful for representing demand for it's derivation.

Propositional extensionality is an axiom that allows translating logical implication to equational reasoning. The lifting rules 

A rule of the form
(rule ((a)) ((b)))
(rule ((b)) ((a)))

can be turned into a rewrite rule
(rewrite ((a)) ((b)))
(rewrite ((b)) ((a)))


A rule of the form
(rule ((a)) ((b)))
can be reflected into an assertion
(=> (a) (b))
(rewrite (=> (I) b) b)

These are the laws of a heyting algebra.
https://en.wikipedia.org/wiki/Heyting_algebra

(rewrite (=> a a) (I))
(rewrite (conj a (=> a b)) b)
(rewrite (conj b (=> a b)) b)
(rewrite (=> a (conj b c)) (conj (=> a b) (=> a c))
(rewrite (conj (=> a b) (=> a c))  (=> a (conj b c)))



(rewrite (conj (I) (I)) (I))
(rewrite (disj a I) I)
(rewrite (disj I a) I)



Rules can contain universal quantification. 
(resolve fact (=> fact head))


(rewrite (eq-prop a b) ()




SHould first class maps take merge expressons? (Map String Expr :merge)



# Unification modulo egraph
I didn't appreciate that you can't use egglog for both unification and nondeterminism, but you can use it for one or the other.
The unification example is just injecitivity axioms.
a + b = c + d -> a = c /\ b + d is plain not true.
You do have one sided injectivty

You can, it seems, encode unification modul egraphs.
_However_ do not run the equations rules at the same time as the injecitivty rules.
Injecitvity applies to pattrns, but not to the underlying ground terms.

Maybe we could make patterns and terms differetn syntatic objects.
And ground up convert grounded patterns to

patlift (Var )

match (Var a) a




=======
## potential roadblocks

bottom-up vs top-down -- is it feasible? would it lead to infinite expansion?

nested for-alls, implications

negation?

come to next meeting with:

* torture tests?
* working a-mir-formality-in-rust model?

try to build a model in datalog??

https://rust-lang.github.io/chalk/book/
 - Glossary is helpful: https://rust-lang.github.io/chalk/book/glossary.html


### Unification modulo egraph
unification modulo ground equalities
unification modulo egraphs in a prolog metainterpreter


e-matching as discussed in the bjorner de moura paper has a very strong feeling relationship to prolog abstract machines like the WAM


For a _fixed_ egraph, we can encode the e-matching into prolog clauses

For a fixed pattern?

There are different partuial evaluations of this


my egraph:
a + b = b + a
a = 0
b = 1
a + b = 2

```prolog
:- initialization(main,main).
:- use_module(library(reif)).

% alternative encoding
% add(0,1,2)
% add(1,0,2)
% a(0)
% b(1)

egraph(2, 0 + 1).
egraph(2, 1 + 0).
egraph(0, a).
egraph(1, b).

% I could make this generic using Functor stuff.
% functor(P, Op, N), length(Args, N), ENode ..= [Op | Args], egraph(E,ENode), map2(ematch, )  
ematch(P1 + P2, E) :- egraph(E, A + B), ematch(P1, A), ematch(P2,B).
ematch(a, E) :- egraph(E, a).
ematch(b, E) :- egraph(E, b).
ematch(+P, E) :- P = eclass(E).

% is the enumerator of terms in enode the same function as ematch? 
% Yeah, I think it is. That's cool.
%extract(E, A + B) :-
%extract(E, a) :- egraph(E, a).
%extract(E, b) :- 
%expand(E, A + B) :- egraph(E, A + B), expand(A, )

eunif(A,B) :- if_(A = B, true, (ematch(A,E), ematch(B,E))).

main(_) :- ematch(+P1 + +P2, E), ematch(+P2 + +P1, E), print(P1), print(P2), print(E), false.
```

Hmm. So an eclass varables is kind of a different thing from a unif var and a ground. We don't want to return 
enode can give it's own class of inifinte terms that is less powerful from what uvar can express
unification through the egraph is stictly weaker than regular unification. So a result that returns just unif variables subsumes one that returns and egraph result.
They aren't strictly more or less powerful :/ . If a term is in the egraph, then p1 = p2 will always succeed as a structural unification if it succeeds as an ematch.
Hmm. But actually, as I've written ematch, a var matches to `eclass(E)` an unknown eclass, so actually yes, structural unification strictly dominates ematching solutions.

This says every term of the form A + B is in the egraph:
egraph(? , A + B). But what could possible be the enode id here? The term itself?

We have a closed universe egraph. If we had an interleaving eqsat process,          we'd need to save a continuation and trigger at every unification failur. Yikes.
Mark some things as constructors that will NEVER be in the egraph

mydif(cons(A), nil).
mydif(nil, cons(A)).
mydiff(succ(X), zero).

if_(A = B, true, if_(mydif(A,B), false, ematch(). ematch())).
if_(A = B, 
  true, 
  eunif2(A,B))
eunif2([F|Args1],[F|GArgs1]) :- map2(eunif, ArgsA, ArgsB).
eunif2(A,B) :- ematch( , E), ematch( ,E).

If functors are equal, we need to try both eunif and ematch
if they are differen, try just ematch
if unifiable is an optimization?

% case by case. closed universe of possible terms
eunif(A, +B) :- A = B.
eunif(+A, B) :- A = B.
eunif(a,a).
eunif(b,b).
eunif(A + B, C + D) :- eunif(A,C), eunif(B,D).
eunif(A + B, C + D) :- ematch(A + B,E), ematch(C+D,E).
eunif(a,b) :-  ematch(a, E), ematch(b. E).  
    ??? Should I be returning something?  
    No I may have to backtrack

if_()

Hmm. If I explicilty marked egraph terms as seperate things, then the switch over to ematch because obvious.
`+` vs ++

type epat = EVar of string | ENode of string * epat list | EClass 
type term = Term of string * term list | EPat of epat | Var of string | Eclass of id

downcast : term -> epat
downcast Var = EVar
downcast 

let unif : term -> term -> term Var.Map.t
match t1, t2

+A ++ +B is an ematching pattern
A + B is a term

+ 

Maybe there is a reason to make unif return the eclass?
```
ematch(P1 + P2, E) :- egraph(E, A + B), ematch(P1, A), ematch(P2,B).
ematch(a, E) :- egraph(E, a).
ematch(b, E) :- egraph(E, b).
ematch(+P, E) :- P = eclass(E).

eunif3(A + B, C + D, E) :- eunif3(A,C,E1), eunif3(B,D,E2), 
  egraph(E, E1 + E2).
eunif3(a,A + B, E) :- ematch(a , E), ematch(A + B, E).
```

if_(functor(A,)  ))


What if I asserta equalities to the dynamic database
but then table ematch and include congruence searching in it. No...
add(0,1,2) :-
do subsumption encoding? but I need a condition. Maytbe xsb can do that
Eh. Well, the question stands. Instead of CHR, can i us asserta to eqsat / assert equalities and have congruences propagate
Shallowly using unif vars for the egraph is tough

normalize() :-
  egraph(E, A + B), egraph(E2, A + B), E1 /= E2,
  asserta(E, E2)


maybe I could use trie as first class egraph?

```prolog
ematch(p, egraph).

pat1(,egraph) :-

pat1_egraph1()
```

If 

in lambda prolog, we could dynamically extend the egraph using implication. We don't have congruence closure though. This is not eqsat process, it's more like just asserting equalities.
cool persepctive on backtrackable egraph. We have to backtrack because we're reasoning over a new signature

x \ egraph(counter, x) => foo()

You could also run eqsat up to some point, by an external agent (egg), then export this as a prolog database and just do what you can. This is flipped from my other picture of prolog first then eqsat or interleaved somehow.

Iterative deepening. it is an optimization to save previosly unresolavble stuff. 

What about backchaining _just_ using egraph matching.
Then backchaining isn't finding anything that datalog mode wouldn't, because only succeeds for stuff in egraph. I guess loops could send it off the deep end.


It seems to be generally a bad idea to put significant computation into unificatin. Unification in most applications is expected to be fast and deterministic.

Hence the orginal conception of switching to ematching upon deifnite functor collision is reasonable, albeit incomplete for full unification modulo ground equalities

Ok. What do you use it for?
approximating modulo AC is out. :(

Actual function calls? Recplaing is/2. CLP already does in a better way really. CLP for uninterpreted functions

Using unif mod egraphs for resolution proofs modulo equality? What is paramodulation anyway?


### Partial horn clauses
Essentiall algerbaic theories
Generalized algerbaic theories


Partial functions + equality + horn. Sounds familiar.

They have a resolution perspective. You can solve datalog via resolution, I wouldn't reccommend it

```
------
  |- base fact

Rules are sequents

(rule (a b c) (d e f))  --> 


---------------
a b c -- rulevars -> d e f

(define f foo)    foo \downarrow (is defined)

```

They might allow partial instantiation of rules? (a3)


Interesting. An unknown graph?
dom(e) cod(e) and we can describe the graph via equations.

## Grobner

A = 0 :- Q = 0, P*Q + A = 0
Finding P is the bitch though.
S polynomial
Q * B - P * A = 0  :- Q * x^m + B = 0, P * x^n + A = 0
non zero form
Q * P * x ^ gcm(n,m) =  :-  Q * x ^ n = B, P * x^m = A.

Reduction:
(P - Q) / (A - B) = 0 :- A = B, P = Q.


a union find is describing a grounded terminating rewrite system. Each edge in the union find is a rule. Is this an important observation? Meh.

Could I embed knuth bendix prcoess itself into egraphs?
:- rule(A,B), rule(B,C).

Or resolution prover?


https://github.com/dwarfmaster/commutative-diagrams should talk to this person

```eggsmol
; connected compoenents are equivalence classes of vertices
(datatype component )

(function belongs (i64) component)
(relation edge (i64 i64))

(assert (edge 1 2))
(assert (edge 2 3))
(assert (edge 3 4))

(assert (edge 7 8))
(rule ((edge i j )) ((edge j i)))

; initialize starting point
(define start (belongs 1))
; transitivity rule of components
(rule ((edge i j) (= comp (belongs i))) ((= (belongs j) comp)))
;(rule ((edge j i) (= comp (belongs i))) ((= (belongs j) comp)))

(run 10)
(check ( = (belongs 1) (belongs 4)))
; does not exist. Returns error as expected.
(check (= (belongs 7) (belongs 8)))

```

## Gilbert Imp
```eggsmol
(datatype Expr
  (Var String)
  (Lit i64)
)

(datatype Stmt
  (Seq Stmt Stmt)
  (Set String Expr)
  ; (Skip)
)

; Zipper of Stmt
(datatype Ctx
  (LSeq Stmt Ctx)
  (RSeq Ctx Stmt)
  (Top)
)

(relation constval (Ctx String i64))

(dl
constval(x, v, n) :- constval(LSeq(ctx), v, n), !writes(Stmt, v), constval(ctx, v, n).
)

(realtion reads Stmt String)
(relation writes Stmt String)

(dl 
S =  Seq(s2,s1) :- S = Seq(s1,s2), notexists v: { reads(s2, v), writes(s1,v) }.
)


```


contextual egraphs - rewrite under the _assumption_ of dif.
This is the analog of frozen constraints. Holy shit.
conexts for lastice filter triggers

E =  :- E = store(select()) , neq(A,B)
vs
neq(A,B) |- E =  :- E = store(select)
A != B |- E =  :- 
eq(A,B)
Could even A != B very special.


The datalog-prolog map.
Should frozen constraints go in contexts?
Or can they be globalized?

cardinality estimation - new souffle paper
vectorizatiom
backoff scheduler

clear-rules


request(a, eps) val(a, int), |int| < eps



add(a,b,c)
emina


// backwards precision requrests
prec(a, eps/2), prec(b, eps/2) :- add(a,b,c), prec(c, eps).
int(c, ia + ib):- add(a,b,c), int(a,ia), int(b,ib).

// precision search
prec(x, deltax/2):- f(x,y), prec(y,epsy), val(y, iy), |iy| >= epsy, prec(x,deltax).



primitive relations
predicates
guards
 = 

implicits?


bitvectirs


extraction program
datalog
agreggates
negation


extraction program

semantics vs operational paper

merging via a table indirection
even regular lattice datalog can be implemented in this way

generic join vm

query side


predicate pushdown

herbie

(rules :my-rules
(((edge x y)) ((path x y)))
(((edge x y) (path y z)) ((path x z)))
)

(run :my-rules 3)


Halloween problem


smarter type sys6ten,
Formulog had an example
type inference
unification

lambda
implement HM

sorted trie

algerbaric program analysis
equational solving


observation trie
if any function maps into two things that are not equal, a and b are not equal
imperfect indexing is allowable.
Things that _may_ be equal 
Things that _can't_ be equal
observations and lattices
The mutating value model, 
set of exact reals model
even vs odd observation

Mark certain things as trie observations
Any table that maps into primitives is a trie domain?
it's this bgi search procedure. 
It kind of is like diqeq on demand
could also enumerate over non equal things
non overlapping lattice filters
filters are observations

How to make first class sets for egglog.
Brute force.


First class sets of sorts can only shrink


comosing dataflow and tranfromation
appendix of pearls

rewrite of matrix rules

```
(datatype Math
  (Add Math Math)
  (Lit i64)
  (Var String)
  (Mul Math Math)
)

(datatype Type
  (Mat Math Math)
)

(datatype MExpr
  (Id Math)
  (MMul MExpr MExpr)
  (MVar String)
  (Kron MExpr MExpr)
  (DSum ME)
  (Zero Math Math)


)
(function )
```

chase core
 (a = b) <= R


Do lattices via
(assert (<= (lo x) 6))


flatproofs
proof minimazation

## Souffle egglog
maxint
```souffle
.decl add0(x:number, y : number, z : number)
.decl add(x:number, y : number, z : number)
.decl maxid0(x : number)
.decl id0(x : number)

add0(1,2,12).
add0(12,3,123).
add0(123,4,1234).

id0(x) :- add0(x,_,_).
id0(y) :- add0(_,y,_).
id0(z) :- add0(_,_,z).

maxid0(x) :- x = 1 + max t : id0(t).

add(y,z,autoinc() + mid) :- add0(_x,y,xy), add0(xy,z,_xyz), maxid0(mid).
add(x,y,autoinc() + mid) :- add0(x,yz,_xyz), add0(y,_z,yz), maxid0(mid).
add(x,y,z) :- add0(x,y,z).


add(y,x,xy) :- add(x,y,xy).
add(x,yz, xyz) :- add(x,y,xy), add(xy,z,xyz), add(y,z,yz).
add(xy,z, xyz) :- add(x,yz,xyz), add(y,z,yz), add(x,y,xy).

//add(@findroot(x), @findroot(y), @findroot(z)) :- add(x,y,z). // canon
// add(@findoot(x),@findroot(y),@unionroot(z,z1)) :- add(x,y,z), add(x,y,z1), z != z1. //congruence

add(x1,y1,z1) :- add(x,y,z), eq(x,x1), eq(y,y1), eq(z,z1).
eq(z,z1) :- add(x,y,z), add(x,y,z1), z < z1.

.decl eq(x : number, y : number)
eq(x,y) <= eq(x,z) :- y <= z.
add(x,y,z) <= add(x1,y1,z1) :- eq(x,x1), eq(y,y1), eq(z,z1).
//add(x,y,z) <= add(@findroot(x),@find(y),@find(z)).
.output add(IO=stdout)
.output maxid0(IO=stdout)
.output eq(IO=stdout)
```




```


// extraction
.decl add0(x : number, y : number, z : number, d : unsigned)
.decl add1(x : number, y : number, z : number)

 = min d : add( x, y , z, d)

add1()


```





## disequlity (ne graphs)
https://en.m.wikipedia.org/wiki/Apartness_relation


## Indicator functions
Internalizing case analysis into uninterpeted function

[[nonzero(x)]] = if x = 0 then 1 else x (or if x = 0 then undef else x)
[[gtz(x)]] = if x >= 0 then x else 0 (* can _assume_ x is nonzero and continue *)
altenrative?
pos(x) = {1 if x >= 0 else 0}

x = pos(x) * x

sort of the same thing.
case analysis:
x = gtz(x) + gtz(-x)

is this that different from
or(pos(x), not(pos(x))) ?
or  x= pos(x) * x indictator as internalizing
implies(pos(x), something)

implies(ctx, something) is harrop feeling. carrying your assumption context



pos(nonzero(x)) = nonzero(pos(x))
They ae kind of tags.
nonzero(x) = x :- nonzero_pred(x)

There is no reason to have nonzero_pred, which will point to pointless eclass. nonzero(x) is representing a similar thing.
Different notion of truth. nonzero(x) = x,  instead of nonzero(x) = true vs nonzero(x) merely being in table.

nonzero(x) != x becomes just as hard as usual to express.

nonzero(x)

Hmm. Is this encoding everything back into rewrite rules?

## Linear Database

In addition to the egraph, keep a linear matrix inequality
Ax <= b
the matrix being A in Ax <= b, where x is a vector of variables associated with eclass ids.
To rebuild the inequality matrix, one might remove all columns corresponding to non-canonical eids and accumulate their entries into the root of their eclass.
"monotonic smt"

I guess > is a very particular version of != , so maybe that could be useful

This is the caononical reference to my knowledge of linear inequalities in smt https://yices.csl.sri.com/papers/cav06.pdf

I don't see how you could pattern match (bind new variables) on >= any more, but you can use it as a guard. You could ask for a maximization?

Liunear programming presolve. And reducing redundancy in the matrix may be somewhat expensive. At least in my naive first guess, asking if a row is implied by the rest of the matrix requires 1 linear programming solve.

Finite domain constraints? These are basically expressible in the lattice system with propagators as rules.

I guess the easy thing to do integrate theories like linear inequalities is to literally assert them into z3 as an eggsmol action using a z3 solver context as a db. Reuse the theory systems of existing smt. Seems like cheating though.

## Semantics
What is the semantic model of datalog with lattices? Partial functions from tuples to lattices?
Is the analagous model a pair of a partition P of the atoms X ( a collection of nonintersecting sets of X) and partial functions f for each table going from tuples of the elements of the partition P (the elements of sets of equivalent elements of X) to elements of P? The finest such partition and the most partial f that is a fixed point of the expansion process is the one produced by egglog
The eids represent the element of the partition to which they belong and don’t represent themselves.
Which is why whichever particular eid comes out is not important.
This is all ignoring the ability to call make-set, but what is the semantic model of ordinary datalog under the addition of a counter or functions symbols?
P is a subset of the power power set of X
And the f are functions that you give 3 sets for example and they might return a set
The 3 sets you give it come from P and the returned set is also in P
It is very difficult to express these definitions clearly
As an example P = {{a}, {b,c}}
f : PxP -> P = [ {a},{a}-> {b,c}; {a},{b,c}-> {a}]
But the concrete table of f may look like [(a,a,b);(a,b,a)]
Or it might be [(a,a,c);(a,c,a)]

## Raw Egglog (Salmonella)

```python

count = 0
parent = []
def fresh():
  global count
  parent.append(count)
  count += 1
  return count

#def strata():
num = set()
def fnum(i):
  z = fresh()
  num.add((i,z))
  return z
add = set()
def fadd(x,y):
  # do simpler noisy thing. Smarter to lookup first before calling fresh
  z = fresh()
  add.add( (x,y,z) )
  return z
acc = fnum(0)
for i in range(3):
  acc = fadd(acc, fnum(i))

print(add)
print(num)
from collections import defaultdict
def norm():
  [(i,x)  for (i,x) in num for (j,y) in num if i == j]
  dups = [(x,y) for (i,x) in num for (j,y) in num if i == j]
  dnum = defaultdict(list)
  for (i,x) in num:
    dnum[i] += x
  #canon = {}
  for (i, xs) in dnum:
    c = min(xs)
    for x in xs:
      parent[x] = c
    



```

```python
#add_yz = {z : [(x,y)] for (x,y),z in add.iter()}
# build indexing structures
# We might only need one?
add_3 = default_dict(list)
add_2 = default_dict(list)
for (x,y),z in add:
  add_3[z] += (x,y)
  add_2[y] += (x,z)

# TODO use smaller one
for xy, y_z in add_3:
  x_xyz = add_2[xy]
  for x, xyz in x_xyz:
    for y, z in y_z:
      add(add(x,y),z).eq(xyz) 

# try
#defaultdict(defaultdict(set()))
```

```rust
// // cargo-deps: ena

fn main(){
  //let mut edge = vec![(1,2), (2,3), (3,4)];
  //let mut path = vec![];
   //let uf = union
   let mut num = HashMap::new();
   let mut add = HashMap::new():

  // 3 iterations
  for i in 0..3{


  //add(x,add(y,z))
  // flatten
  // add(x,yz,xyz), add(y,z,yz)
  // add(yz) -> 

  // rebuild
  let old_add = std::mem::take(&mut add);
   for (mut (x,y), mut z) in add {
     x = uf.find_mut_value()
     y = uf.find_mut_value()
     add.entry((x,y))
        .and_modify(|v2| *v2 = uf.union(z, v2))
        .or_insert_with(|| uf.find(z))
   }
  }
}
```


Write the semi naive datalog using either eq or parents(x,y).
Delete at the right spots.

Hmm. ancestor parent is usually faster

:- edge(x,y).
parent(x,z) :- parent(x,y), parent(y,z).

parent(min(),max(z1,z)):- add(x,y,z), add(x,y,z1), z != z1

num(i,x) <= num(i, y) :- x <= y.
parent() :- num(i,x), num(i,y), x != y

dnum(i,x) <= num(i, y) :- x <= y.
num(i,x) <= dnum(i, y) :- x <= y.
parent() :- dnum(i,x), num(i,y), x != y

## Symbolic Execution


## Disassembly, Compiliation I dunno 

No lattices.
Adts.

what is a constructor

Is this prolog?

Fresh variables that don't come from terms. (Do not exist in the functionally dependent position of any).

append([],A,A) :- A = fresh().
append([X|],A,A) :- fresh(), fresh().


Should foo match a unification variable in the database?

IF I make a python pretty printing frontend, that could be useful
We don't _have_ to use C++/Rust bindings

```python
from dataclasses import dataclass
from typing import Any, Union, List
@dataclass
class Var:
  name: str

@dataclass
class Lit:
  val: Any

@dataclass
class Pred:
  name: str
  args: List[Union[Lit,Var]]

```

# eggsmol

```eggsmol
(relation path (i64 i64))
(relation edge (i64 i64))

(assert (edge 3 5))
(assert (edge 7 8))
(rule ((edge x y))  
      ((path x y)))
```

```eggsmol
; proofs of conectivity are paths
(datatype Proof
  (Trans i64 Proof)
  (Edge i64 i64))
(relation path (i64 i64 Proof))
(relation edge (i64 i64))

(assert (edge 2 3))
(assert (edge 3 1))
;(assert (edge 3 4))
;(assert (edge 1 4))
(rule ((edge x y))  
      ((path x y (Edge x y))))

(rule ((edge x y) (path y z p))  
      ((path x z (Trans x p))))

; We consider equal all paths tha connect same points.
; Smallest Extraction will extract shortest path.
(rule ((path x y p1) (path x y p2))  
      ((= p1 p2)))

(run 3)
(check (path 1 2 (Edge 1 2)))
; Would prefer being able to check
;(check (path 1 2 _))
; or extract
(extract (path 1 4 ?p))

; Get size of tables? Dump tables?
```


```eggsmol
(datatype Proof
  (Comp Proof Proof)
  (Sym Proof)
  (Id)
  (Edge i64 i64))
(relation path (i64 i64 Proof))
(relation edge (i64 i64))

; 2 loops = cylinder.
; loop 1
(assert (edge 11 12))
(assert (edge 12 13))
(assert (edge 13 11))

; loop 2
(assert (edge 21 22))
(assert (edge 22 23))
(assert (edge 23 21))

; vertical edges
(assert (edge 13 23))
(assert (edge 12 22))
(assert (edge 11 21))


(rule ((vertex x))  
      ((path x x (Id))))

(rule ((edge x y))  
      ((path x y (Edge x y))))

(rule ((path x y p1) (path y z p2))  
      ((path x z (Comp p1 p2))))

(rule ((path x y p))  
      ((path y x (Sym p))))

; basic square loops on side of cylinder
(rewrite (Trans 11 (Trans 12 (Trans 22 (Trans 21 p)))) 
         p)
(rewrite (Trans 12 (Trans 13 (Trans 23 (Trans 22 p)))) 
         p)
(rewrite (Trans 13 (Trans 11 (Trans 21 (Trans 23 p)))) 
         p)

; reverse a path. twice is same as original
(rewrite (Sym (Sym p))   
         p)

(rewrite (Comp Id p))   
         p)
(rewrite (Comp p Id))   
         p)
(rewrite (Comp f (Comp g h))
         (Comp (Comp f g) h))



(run 3)
;(check (path 1 2 _))
;(extract (path 1 4 ?p))
(extract (Edge 1 2))
; Get size of tables? Dump tables?
```

```eggsmol
(datatype Expr
  (Mul Expr Expr)
  (Var i64)
  (Lit i64)
)


; regular unification
(rule ((= (Mul a b) (Mul c d)))
   ((= a c) (= b d)))

;(relation false (i64))
; If any Literal make equal to something it can't be, false is derived
;(rule ((= (Lit i) (Lit j)) (!= i j))
;      (false 0))
;(rule ((= (Lit i) (Mul a b)))
;      (false 0))

(assert (= (Mul (Var 1) (Var 1)) 
           (Mul (Lit 1) (Lit 2))))



(run 3)
(check (= (Var 1) (Lit 1)))
(check (= (Lit 2) (Lit 1)))
;(check false 0)
```

```
; injective
;(rule  (eq (Mul (Var x) b) (Mul (Var ) b))     )

; start
; but how do you know when to commit to a particular commutativity?
;(eq e1 e1)
```


```eggsmol

(datatype Expr
  (Add Expr Expr)
  (Neg Expr)
  (Num i64)
  (Var String)
)

(rewrite (Add x y) (Add y x))
(rewrite (Add (Add x y) z) (Add x (Add y z)))
(rewrite (Add (Num x) (Num y)) (Num (+ x y)))
(rule ((= (Add x y) z))
      ((= (Add z (Neg y)) x)))
(rewrite (Neg (Neg x)) x)
(rewrite (Neg (Num n)) (Num (- 0 n)))

(assert (= (Add (Var "x") (Num 2)) (Num 7)))

(assert (= (Add (Var "z") (Var "y")) (Num 7)))
(assert (= (Add (Var "z") (Var "z")) (Var "y")))

(run 3)
(extract (Var "x"))
(extract (Var "y"))
```
(Sub)



There may be utility to special casing no argument relations as bools. But (False 0) is good enough.

preprocessing

egglog decompiler -> PEG or RSVD

YOGO - koppel. You only grep once https://www.jameskoppel.com/files/papers/yogo-preprint.pdf
https://arxiv.org/pdf/2204.02765.pdf


# e-unification
Yihong has a point. This makes sense. I should look into it

No. It doesn't seem to work. You need backtracking to do e-unification. You don't know when you can commit to
a unification.

commutiative unification
```
eun(A,A). % :- !.
% already taken care of. 
% eun(A + B, C  + D  ) :- eun(A,C), eun(C,D).
eun(A + B, C  + D  ) :- eun(A,D), eun(B,C).
```

Constrained horn clauses -> instructions as rules?
vs somehow encoding instructions as facts.
Instructions are facts sure. The state isn't though.


```
step(deadbef + 1, ) :- step(0xdeadbeef)


pc(State') = 43, State' = step(State) :- pc(State) = 42


// r0 is a symbolic constant, not implicitly a value. It should never be unified with 53 for example
insn(1) = mov(r0, r1)
insn(2) = add(r0, r2)
insn(3) = ble( r0, 0xdeadbeef)


(datatype loc
  (Reg String)
)
(datatype Insn
  (Mov String String)
  (Add String String)
)

But add is also in a certain respect mathetical addition. Can I have 
rewrite rules over assembly programs?
Denali

We can decouple the interpreter from the program. That's kind of nice.
 :- step(State), insn(pc(State)) = mov(R0,R1)

// symbolic execution + simplifcation?
// at a branching point, we need to encode the branch taken.
// patch condition
// This is a relative of formulog?

// concrete next relation. But pc isn't unqiuq.. hmm.
pc(step(42)) = 43

next(42,43).

// constructor style record
state(42, meminit, r0_init)

// projector style record
pc(state_init) = 42


path_cond(State') = and( r0(State) > 7 , patch_cond(State)) :-

// frame problem?


mov(r0,r1, add(r1,r2, init_state))
vs
step(mov(r0,r1), step())

vs run(seq(mov(r0,r1), add(r1,r0)), s)

data dependencies

operations commute.
step(mov(a,b), step(add(c,d))) -> step(add(), mov()), noteq.
well. probably not. because of carry flags and such.

instruction selection
add(a,b) -> addinsn(a,b)
mul
 as a final process after building equivalence.

(datatype Reg
  (R0)
  (R1)
  ..)
they are concrete... ?

frame problem
r0 = r0

seq(mov(x, a + b), mov(y, x + c)) = seq()
mov(sim([x = , y = ))

seq() & par()

anything that is live at end of block or observale needs to happen.
functionalize, then exctract.
```


peephole optimziation.
Rearrange. Try out new variables.
p = seq(uses r0 instead) :- p = seq(  uses p internally ), dead(r0, p) 
Do constraint based extraction later. Maximize total dependency time.

live and dead are required to do certain rewrites.
That's the point of these analyses kind of.


## Differential / Incremental egglog

Incremental egglog. We could perhaps use one of the non union find based encodings?

 note that I think incrementality a la differential dataflow seems like a way to extend the relational egraph ideas to supporting backtrackable / multiversioned egraphs. Connected components is the example I've seen discussed in slides of differential dataflow. Union find is a connected components algorithm and vice versa. Moving the watermark is a way to commit and garbage collect the different egraph versions. There maybe 2 or 3 different notions of "time" that might make sense to us. Time 1: congruence closure repair iteration time 2. rewriting time. 3. external user injection time (say driven by a SAT solver or something).

I have thought that one way to extend to certain higher order clauses would require a backtrackable egraph
consider the higher order axiom (forall x, foo(x) -> bar(x)) -> baz(z). This falls into the harrop clause fragment that is supportable by lambda prolog. Harrop clauses are a fairly natural extension of horn clauses that still support a natural operational prolog-like execution. I am unclear to what degree they are supportable in bottom up.
One way to do this is to add the fact foo(fresh) to the database, then run datalog for a while and see if the fact bar(fresh) is derived.o
If so, cleanup the database before foo(fresh) and add baz(z)
If not (maybe after some timeout) cleanup before foo(fresh)  and don't add baz(z)
These sorts of clauses do actually show up in theorem proving applications of egglog. The specific example I have in mind is that universally quantified things are universal properties of constructions in category theory. (forall f h,  g . f = g . h -> f = h  ) -> monic(g)  is one example (uh maybe with some well typed ness conditions too).
https://www.philipzucker.com/egglog2-monic/
This is admittedly somewhat esoteric.
Rust's Chalk trait solver also supports something like harrop clauses because it has to. https://rust-lang.github.io/chalk/book/clauses.html#type-checking-generic-functions-beyond-horn-clauses 


Another place where backtracking might be useful is tentative alpha equivalence discovery (this is again  kind of half baked thinking) (edited) 
Suppose I had a two term \a. body(a)  \b .body2(b) encoded in the most naive way using fresh variables for every binder
If I suspect that body = body2  I could tentatively set a = b , run congruence closure, and then see if body(a) = body2(b) (edited) 
If so, commit. If not, roll back a = b
body were intended to be metavariables, not concrete terms btw.

lam(eida, eid1) lam(eidb, eid2) , tentatively set eida = eidb , run cong closure, see if eid2 = eid1 . (edited) 
And I rather prefer sum(a,body) and integrate(x,body) as examples since there alpha is all you care about, not normalization or substitution.

They are also related ideas since `\a. bodya -> \b. bodyb -> (a = b -> bodya = bodyb) -> a = b` is kind of expressing the same thing.

Perhaps a scoped union find could do the same here.

But scoped union find is equivalent to 

What about magic setting this? I can't? How do I express tentative a = b knowledge. context I guess.
Goals and Sigma are as much a part of lambda prolog as anything.
Program analysis of lambda prolog. partial evaluation of lambda prolog interp in datalog.
CFA? Something like higher order functions is happening. We could truncate context at k.
In ordinary datalog maybe. But union find equality is not easily contextualized? Or is it? Scoped union find or internalize union find into a parents table. Ephemeral UF of yihong.


In mundane prolog, the program is a fixed entity.

(a = b -> bodya = bodyb) as a closure or defunctionalized?

modus ponens ctx -> foo(ctx, a) -> 

herbie
chr

seminaive and monotoncity?


egglog without existential - consider semantics. Must be realted to partial equivalrence relation over atoms

Related semantics of eggog to the expanded version with quadratic eq table?


partial functin to unit is _=_

examples

extraction you have give what are constructores

monotonicity is what you need for soundess of derivations
hmm. Is this true?
Well in a sense.

egglog functions for lattice tables



## Union Find Groups
https://youtu.be/KxeHGcbh-4c?t=1424 group action on union find edges... Hmm.
Supports permutations not on the nose. (commuting)
Is associativity a group? Not really I don't think. It's something else.
braiding?
A different extension of UF from scoped.
http://poj.org/problem?id=2492 a bug;s life
Not very politically correct now is it

1 != 2
2 != 3
1 != 3

1 (+1) = 2
2 

g(1) != g(2)
g(2) != g(3)

permutation group?
swap(1,2) = swap(2,3)

start with full graph. Delete edges. Are there two connected components?

male(1) = female(2)
female(1) = male(2)

but do not state which is true.
Are there two connected components or one? (true and false statements)


gender(a) != gender(b)
In a closed universe of choices, a != b is the same as   and ((gender(x) = opt1) != (gender(y) = opt))
which is the same as  /\ or(gender(x) = otheropt)
If we make gender(x) = otheropt as a proedicate   is(x,opt) or isopt(x). The relational form of the function gender.

isopt(x) = isopt(y,)

and (isnot(x,opt) = is(y,opt))

male is isnot

notmale(1) = male(2) but we don't know if true
male(1) = notmale(2)

not is a group though

not(female(x)) = female(y)

1,swapgender is group

indeed if swap(x) = y, then x can't possibly be y if there are no fixed points of this transformation.


gender(x) = male
internalizing the relational lifting:
gender(x,male) = true :-: gender(x) = male.
gender(x) != male ----> gender(x,male) = false 

gender(x,female) = true :- gender(x,male) = false.


// LEM
eq(x,true) :- eq(x, false).

x = a :- eq(x,a) = true.


Generalizing 
color(x,green) = true :- color(x,red) = false, color(x, blue) = false.
color(x,blue) = true :- color(x,green) = false, color(x, red) = false.

This is like my datalog coloring problem

 :- notcolor(x,red), notcolor(x,blue) 

notcolor[x,c] is like color(x,c,truthvalue) which is modellable in datalog. Whetger i choose to fuse it with the predicate name is up to me. This is very similar to magic set binding pasttern fusing.

The bugs are in two clans

a fights b

```souffle
// Shark vs Jet predicate
.type clan = Jet { x : bug} | Shark { x : bug}
.type bug <: unsigned
.decl eq(x : clan, y : clan) eqrel

.decl fights(x : bug, y : bug)
fights(1,2).
fights(2,3).
fights(1,3).

eq($Jet(x), $Shark(y)), eq($Shark(x), $Jet(y)) :- fights(x,y).

// There is a traitor if there is a bug that acts as a shark in one situation and jet in another.
.decl traitor()
traitor() :- eq($Jet(x), $Shark(x)).

.output traitor(IO=stdout)

```
This encoding isn't as pleasing. Male and female is quite easy to explain unfortunately.

and other permutations.

For finite sets, we can label with permutations?
no.
color(x) = cycle(color(y)) is a different atatement than color(x) != color(y) (a stronger statement)

groupaction(a) = groupaction(b)

not is a group action.


notgender(x,male)


single bit field in union find

The permutation group of size 2 is exactly the action of {id, not} on booleans
{true -> false, false -> true}.

Every function can be lifted to a relation via reflection
f_rel[X,A] = true :- f[X] = A.
f[X] = A :- f_rel[X,A] = true.

Disequality statements can be macro expanded to statements on the relations
x != y  ----> x_rel != y_rel ---> x_rel = not(y_rel)



Alternatively, these true/false/eid fields can be in every function symbol



permutation groups can act on powerset lattices.
Act on filters?
They don't move between layers of the lattice though.
Up and down powerset lattice. upper and lower bounds. ??? Lower bound is single element?
Intervals of sorts. must be in the set, can't be in this set? Complements of each other sort of.

polytopes? Simplices?


concrete example

```
// 3 queens
//queen : int -> int
// function from column to row of queen
queen(1) != queen(2)
queen(2) != queen(3)
queen(3) != queen(1)
```

```
// queen_rel : int -> int -> bool
queen_rel(1,y1) = not(queen_rel(2,y2))
queen_rel(2,y2) = not(queen_rel(3,y3))
queen_rel(3,y3) = not(queen_rel(1,y1))

y1 = queen(1)
y2 = queen(2)
y3 = queen(3)

queen_rel(X,Y) = true :- queen(X) = Y.
queen(X) = Y :- queen_rel(X,Y) = true.

```

```
add(x,y) != num(0)
--->
add_rel(x,y,add(x,y)) = NOT(num_rel(0,num(0)))
```


Y = div(Z,X) :- mul(X,Y) = Z, X != num(0).

num(0) != num(1)
num(1) != num(2)

Does this imply num(0) = num(2) by the encoding?

num_rel(1, num(0)) = false.

```
// queen_rel : int -> int -> bool
queen_rel(1,y1) = not(queen_rel(2,y2))
queen_rel(2,y2) = not(queen_rel(3,y3))
queen_rel(3,y3) = not(queen_rel(1,y1))

y1 = queen(1)
y2 = queen(2)
y3 = queen(3)
queen_rel(X,Y) = true :- queen(X) = Y.
queen(X) = Y :- queen_rel(X,Y) = true.
```


and vice versa
queen_rel(1, queen(2)) = false.
queen_rel(2, queen(3)) = false.
queen_rel(1, queen(3)) = false.



## Defaults

do we want to have complete lattices.
What is the default value

Default value could be metavariable

I've been tinkering with a prolog/CHR encoding of egglog and in that case defaults being unification variables is by far the easiest thing to do and not costly since the host language has them. But it does seem like a pain to do it in the rust implementation

If unification variables can point to constants then we don't need the `Num` constructor.



## Egraphs and Terms at the same times
Max: Log table and materialized caonicalized version. A different flavor of the two table idea. I'm not particular convinced it's the same thing. The egraph log doesn't really let you talk about terms?

You need both terms and egraphs. Without the egraph union find action, we just have a hash cons. During extraction, we'll want to be using the term version.
If you used a min lattice for example rather than "spooky" union find, that is a hash cons, where we just ignore the version that has a high id for some reason (because of failure to check properly probably.)

I'm kind of thinking that when we define "datatypes", we need to generate two different things. Egraph like tables and hash-cons like tables add_egraph : eid, eid -> eid  vs add_hash : int, int -> minlattice Hash-cons tables would let us talk about terms, which could be attached to eclasses via lattice mappings. Another way of looking at hash cons tables is that their output ids use min-lattice rather than spooky union find "lattice".  Another thing that I think is useful is to "downcast" eclass ids to regular ints, like how the max-lattice could be downcast to an int. I suspect but do not see clearly that with that capability, it is possible to record the equivalence proofs using a regular table instead of a fancy union find (upon every discovery of a new equivalence, record that tuple. This is basically what gets recorded in proof producing union find anyway. Reconstructing the actual proof path seems like it could be expressed as a datalog query itself since UF is used for connected components, proof of connected components is a path, and _the_ classic datalog query is for paths) , avoiding my concern about yihong's "no global union find" version.

It might be desirable for the hash cons table to be garbage collected in some sense. It might also be better to just use a regular hash cons 

The hash-cons / egraph table distinction fell out naturally in the souffle encoding where add(x,y,z)  was the egraph table, whereas $Add(x,y)=z . Hmm. This is not right. We put eclass ids into $Add().

There does have to be an injection of terms into eclassid
inj(tid , eid)
There is a natural table injecting term_ids into eclass_ids, and in principle nice versa, although the opposite direction easily becomes an infinite table

Another way of talking about this is that in ordinary datalog you can make an eq relation
eq(x,y) :- eq(y,x).
eq(x,z) :- eq(x,y), eq(y,z).
Asserting any equality to this relation then gets completed with transitivity and symmetry. Instead you could model this in "edge path" style by asserting discovered equations to eq_edge
eq(x,y) :- eq_edge(x,y).
In souffle and in egglog,eq is done with special data structures, but it is still possible to keep eq_edge for the purposes of recording data.




## CHC
If constraints are egraph constaints.
You need it to satruate though. Wouldn't this alrady be the obvious thing for an smt solver to do?

reach() :- reach()

equational theory over state.
Why would you have this?
Boolean operations I guess.

Why would loops ever terminate?

CHC are second order solvers. They return propositions/predicates

phi = union(phi, f)

First class sets / predicates:
union = or
inter = and
subset = implies

subset(a,b) <=>  exists c, b = union(a,c). exists c, inter(b,c) = a.
Skolemized version: diff is maximal dude.

//
union(A, diff(B,A)) = B  :- subset(A,B).
inter(A, diff(A,B)) = A  :- subset(A,B).
subset(A,B) :- union(A,C) = B.
subset(A,B) :- inter(B,C) = A.

// why even both putting the variable in there.
subset(phi(x,y,z), )
subset(phi, x = x + 1) :- x = x+1, subset(phi), . 

phi :- phi, cond. ---> subset( and(phi,cond), phi).
phi  >= phi /\ cond

subset( and(phi,cond), phi).
extract subset(phi, X). smallest X that does not mention phi
How will you ever actually be able to solve for phi.
How will you use cond in agood way.

meaning(condexpr, L(x, y, z)).

A <- union(A, empty).
subset(A,C) :- subset(A,B), subset(B,C).


subset(c1,c2) :- meaning(c2, L(x,y,z)), meaning(c1, L(x, y, z)).
Or maybe rather out approximation. No if merely outer approxmation, we can't guarantee subset.

boundtope(cexpr, L1 + L2) :- x + y

generalization rules
subset(polytope, weakerpolytope).
subset(ptope, join(ptope1,ptop2)) :- ptope1, ptope2

A bounded loop it can just inline I guess.


Is this the Kozen algerba? The items are sets now. "term algebras"

We can just lose subset and consider union(a,?c) = b   to be the definition of subset? We can resolve subset away.

We also probably want to relax CHC. That's a hard step.

I internalized too much I feel like. I can't use meta :- ?
subset(phi, B) :- subset(phi, A), trans(A,B).
This does feel like indirect equatily or someting
subset(B,phi(pc2)) :- subset(A,phi(pc1)), trans(A,B).


THis is the difference between are partial order and and algerbaic characterization of a lattice.
It is reminsencet of categorical, adjunctions, indirect equality, relation algerba, algerba of programming, backhouse

Bubble sort, merge sort for union. A way to normalize AC. But why not destructive rewriting then?
union(union(b,union(a,E):- union(a,union(b,E)), a < b. 

higher arity normalization.
union(a,b,c) :- union(a,union(b,c)).

What is the best memoized sort?

## refinement typing
I have another possible application related to the hindley milner one yihong did. I've been encoding bidirectional typing into souffle and I suspect something interesting could be done using egglog in the ever mysterious chk-syn rule. Page 3 https://arxiv.org/pdf/1908.05839.pdf This is also the rule where refinement typing puts the smt subtyping query, so there is some relationship there. https://arxiv.org/pdf/2010.07763.pdf pg 15
Gam |- e => A    A = B
-----------------------
    Gam |- e <= B

Maybe refinement typing could be done directly. Not sure. The resulting verification conditions are horn clauses i think? Not sure if that is good enough.


infertype as a partial function
I have been considering using option to represent the binding patterns ofmagic set.
infertype
checktype

Hmm. Doesn't really match does it. No, maybe it does


## Interval arithmetic
Does anyone have an example where rewriting makes an interval more precise?
white_check_mark
eyes
raised_hands



The really simple one was cos^2(x) + sin^2(x) -> 1 takes [0,2] to [1,1]
yeah, that's good. just looking for some easy tests
For that matter x * x -> x^2  also works. if x was in [-1,1] the lhs is [-1,1] whereas the right is [0,1] if you consider squaring as a primitive interval 
You want to rewrite to fused ops you have primitives for (edited) 
ah that's a good one
But it isn't clear how to get your way there, hence egraphs
you dont even have to fuse, you can just have a different rule for lo(x*x)
And the same pieces might be parts of two different fused expressions (I think) (edited) 
Hmm. I don't think I understand the lo(x*x) thing
Oh...
Interesting
you don't need a square ast node at all
I see.
That's cool
you can just have a rule for lo(x * y) and lo(x * x)
Very cool.

S U B S U M P T I O N
Also maybe  div(y,x), posnegzero(x)  could have a good rule

You could also maybe encode hi(x) = sqrt(n) :- hi(x*x) = n (edited) 
Back driving expressions

And so on hi(x) = a - b :- hi(x + y) = a, hi(x) = b

https://juliaintervals.github.io/pages/tutorials/tutorialConstraintProgramming/
https://juliaintervals.github.io/pages/tutorials/tutorialConstraintProgramming/
Hmm. I wonder if we could make a lattice out of taylor models. That'd be fancy
I'd guess the join of two upper bounding polynomials would be the polynomial that stays above both at all points (of the domain of interest) and minimizes some objective. some variant of a sum of squares optimization (edited) 


An example where there isn't a best thing to do in regards to rewriting?
For assoc and comm you'd want them all. You should just group together like terms.

(x >> 2)

(a * 2) / 2




What about floating point reasoning?


Ok I might have an example where it starts to get hairy to arrange a destructive rewrite simplifier to do the best thing every time
white_check_mark
eyes
raised_hands



consider (a + b)(c + d). Should it be expanded?
(a + b)(a + d) should if we can recognize  a*a as a special sharing case. There is not sharing in the factored form (edited) 
(a + b)(b + a) shouldn't. We can commute, and then recognize a sharing at a larger level , which gives better bounds
Ok so maybe the rule should be canonicalize every factor, pair up, and then expand the pieces that don't share up. But that rule is messy to express and questionable. You might just need to keep patching it
I think running these with all variables as [-1,1] is sufficient to demonstrate the difference
Also partial expansions. (d + (b + e))(d + e). Finding the sharing here with destructive rewriting is hard


Herbie Use rationals

.decl exact(e : Expr, v : rational)
.decl approx(e : Expr, samplenum : unsigned, value : float)
approx(e1, i, v1) <= approx(e2,i, v2) :- eq(e1,e2), exact(e1, v), abs(v - v2) <= abs(v - v1).

.type rational = [n : number, d : ]
Yeah. Not particularly gonna be better than floats.



## Destructive Rewriting 
CHR
Linear Logic programming


"pruning", destroying entire eclasses? Or never put stuff into "dead" ecalsses. You don't want to both making num(x,a) equal to anything else. It's a really good term.

## Macro System
scyrer has some work to allow embedding. That's infriguing.

https://stackoverflow.com/questions/14459647/is-it-possible-to-generate-and-execute-rust-code-at-runtime

Relatedly : user defined functors.

Prolog style macro system. We could use egglog itself to compile egglog programs? Kind of makes sense.


Use guile? Seems kind of an insane dependency.
Maybe having the master program be racket or whatever and just expose a C api everyone can use.
Then you could use normal racket macros.

Prior datalog API:
- Souffles C api. Pretty basic. There are relations.

It's really hard to have good coupling to rust features but also be portable.


Martin mentionedFortress rewrite rules and Rel uses higher order compile time stuff inspired by hilog?
Flix has its own language.
Embedded datalogs of any kind can construct programs
Souffle has CPP

Many transformations are embedding this or that concept to stock datalog features. If you want that to be a macro system so be it.

That the souffle _compiler_ is written in C++ seems kind of insane. But they would have a 2 language problem.
A bytecode intepreted datalog.

## Proof provenance = extraction?
initiaitng the egraph
var("x",1).
var("y",2).
add(1,2,3) :- var("x",1), var("y",2).
add(3,1,4) :- var("x",1), add(1,2,3).

Consider the following methodology for initiating the egraph. In some sense we're only allowed the make add(1,2,3) because 1 and 2 are already in this egraph.
var("x",1).
var("y",2).
add(1,2,3) :- var("x",1), var("y",2).
add(3,1,4) :- var("x",1), add(1,2,3).

The souffle proof of add(3,1,4) would exactly mirror the "term" that we put in eclass 4
I suppose what I'm doing is associating a grounded rule with every node in the original term.
rather than just a grounded fact.

proof of smallest cost analysis = term. If you ignore the parts of th proof of how the terms got there

magic set for top down extraction.

rel height(x,h : lat) | x -> h.
needheight(x), needheight(y) :- needheight(z), add(x,y,z).
height(z, min(hx,hy) + 1) :- needheight(z), add(x,y,z), height(x,hx), height(x,hy).


// needheight ~ reduciable
needheight(fx) :- app(f,x,fx), lam(v,b,f).
action@insert(t) :- redexp(fx), extract(fx, t).


Grounded rules are proof steps.
That's why the provenance thing worked. A rule name + missing variables plus what was in the head.
You could also make a new rule to record the rule. This is perhaps somewhat wasteful however.
rule1(a,b,c) :- body1().
head1(a) :- body1().

Or! Any usage of head transform into one of the usagees of rule
foo(x) --->  { rulefooheahd() ; rulefoohead() ; rulefoohead() } 
Then you don't need structures. But then you need...

These rules are enough to construct the grounding of the program?
Well, the tables were also in the absence of negation.

## Proof
(i,j) tuples for each equality

explain(i,j).
```
$Eq(i,j)
.decl explain(i,j)
.decl eq(i,j) eqrel
```
eq is closed under trasnitivty
explain isn't
```
eq(i,j) :- explain(i,j, r).
explain(i,j, $AccoL()) :- 
explain(i,j, $AssocR()) :-
explain(i,j, $Comm()) :-

explain(i,j,$Cong()) :- // congreunce 

```
eq is bottom up, but then upon solution, we can extract explain top down.


In egglog0 I could record proof trees as an etxra parameter. this is just like my prolog theorem prover.
Can enforce equality of proofs for compression.

## ASP for ILP extraction?
I've become more intrigued by the plausibility of using ASP solvers for extraction. Deeply integrating ASP techniques or semantics takes us wildly out of scope, although might be possible. But instead, if extraction is stratified after eqsat, one could print out the normalized egraph database directly into an input file for clingo.
```
num(4.8, 0).
num(754.3, 1).
add(1,2,4, analysis_res_1, analysis_res2, ...).
% and so on
```
And then write the clingo constraint program that operates over these base facts. Alternatively instead of printing this file could use rust bindings: https://github.com/potassco/clingo-rs . See for a flavor of the splitting between the program clauses and the incoming data this graph coloring example https://stackoverflow.com/questions/41191313/asp-clingo-splitting-graph-to-n-cliques .
ASP is a hyper expressive language for optimization problems involving constraints for things like graph coloring, cliques, subset cover or hamiltonian cycles and other things and it feels like it would be a fast way to write strange custom extractions. There seems like relatively low impedance mismatch between the egglog and clingo compared to other optimization methodologies like CSP or IP because they are both rooted in logic programming and relations. Having said all that, I don't know to what size clingo scales, I don't have an example where such sophisticated extraction is warranted, and I'm not 100% sure I know what an extraction encoding would look like.


Kind of related thing one could do is take the grounded eqsat database and encode it into a sat solver. We're not trying to compete in the same domain as sat solvers though. And what do I really mean by this? What kind of boolean logical structure am I considering?
  horn clauses 
+ quantified boolean formula without equality? forall x, f() \/ f() = f() \/ \/ \/ 
It has a flavor of ackermannization. Could only ever return unsat?

Maybe this is just a bad SMT solver.
It's like reversed though. SMT solvers are SAT with theories laid on top. This is EqSat with SAT laid on top.

Remy points out that MIP solvers are awesome. No objections here.

How does ILP work? You get an integer variable for every enode? You make linear constraints that... something?

## the chase
Would it be fair to say that ordinary datalog itself is the chase over full dependencies?
https://dl.acm.org/doi/pdf/10.1145/1514894.1514897 Datalog+- a datalog framework supporting TGD and EGD. A theory, not implementation paper?
A slightly more recent talk http://people.scs.carleton.ca/~bertossi/talks/introAlgsDat+-(16)Pruned.pdf
A thesis on the chase of datalog programs I haven't found the full version of https://www.proquest.com/openview/665c3cbe7753bef1a57a2ccc7bbdb775/1?pq-origsite=gscholar&cbl=18750&diss=y
The chase of datalog programs - ProQuest
Explore millions of resources from scholarly journals, books, newspapers, videos and more, on the ProQuest Platform.
What do you mean by full dependency? Datalog is a chase that only supports tgds
I was reading the Alice book and it was terminology I haven't seen anywhere else yet. Full dependency was rule without existential in head.
Chapter 10 http://webdam.inria.fr/Alice/
Also very interesting that they mention the EPR class of formula
https://twitter.com/SandMouth/status/1464685169214951426?s=20&t=faU6J4XGjpXRLQNoQeJx1Q@SandMouth
Is EPR kind of sort of datalog? The lack of function symbols is pretty similar
Yihong replied he had asked the same question
My impression of what is considered "datalog classic" is that it didn't include TGDs, but any actual datalog with a counter, or integers, or adts probably does.
Is the chase an operation over the actual tables, the schema, queries, or all of them depending on the context?
The chase for Egds involves picking one variable and substituting it into all occurences. This is the naive implementation of unification?
And by variable maybe i mean "labelled null"?
Amusingly, the only way the chase is making sense to me is basically saying "the chase is egglog" rather than "egglog is the chase"
Given my relatively poor database background


So for ephemeral union find, how do we track proof. When we do chase step, we must record it somewhere for provenance

graal https://graphik-team.github.io/graal/papers/graal-ruleml2015.pdf The graph of rules. You can check if rules can unify?


## Prolog v Datalog v Egglog
What makes 

prolog is structural unification g(_) = f(_) can never succeed
Modeling egglog using CLP, adding constraints of equality to and egraph can never fail.

Max has been limitting in the head.

## Egglog vs SMT
Is egglog jyst a bad smt solver wihout dijsunction?

## Egglog vs Flix vs IncA

union find is lattice
join() = parent if in same 

lattice that's changing


lattice in input position? Because eclass id are in input position

dynamic lattices - dpeendent lattice

forall,  -> L a dependent function
A dependent relation?

A lattice that depends on a table.

Hmmm. 

the lattice type also move monotonically

other latic

on the query side flix goes both ways


chase = 

join is spooky
meet is findparent

body vs head
fd output vs input

Why is sort allowed in both, but lattice allowed in 

partial lattice


subsumption semantics

"Everything is a pointer to a pointer to an element of the powerset lattice!!"

"dynamic typeclass"
You could do this in ocaml. This was my point about Set.t with a global thing.

typeclass Lat L {
  join(x,y,z) :- parent(x,y).
}

flix + trees

Is partitioning 


We could probably build a union find using lattices. Of course. Yes.
Remy points out that this does not normalize enodes however.
So this "lattice in negative position" thing is meaningful.

parent()

```
parent(number, maxlattice).
parent(i,k), parent(k,i) :- parent(i,j), parent(j,k).
parent(i,j), parent(j,i) :- findsomethingstbeequal(i,j).
```

I actually thingk the lattice concept is a red herring.


Dependent prolog datapoint - Twelf.
Dependent vs not and lambda vs not seem like distinct axes. Given that lambda prolog has lambda but is not dpeendeltly typed.
A datalog twelf?

type("parent", symbol, symbol).
constructor were named rules


Calling something a lattice macro expands a join relationin the right spots.
This join relation could be intertwined. And really has to be because of demand drivenness



## Gogi

we can have exists, but ONLY in functinally dpenednet position (at least one)
A subclass of TGDs




## Related systems
### Egg
Egglog has as a subsystem egraph rewriting. This is the main motivation.
### SMT
SMT solvers have egraphs in them + logical boolean structure and theories. Egglog supports only horn clauses and has a constructive flavor. With extract-externalsolve-insert, it could support theories. It supports a different class of queries than smt: simplification and pattern search (CQ), simpler operational semantics (leading to performance gains and understandablility smt quantifiers are notoriously difficult to tune and debug), simpler proofs.
### Datalog
Well, duh.  Manual eq(x,y) relations can kind of encode what egglog does.Souffle has eqrel. uZ3 is a reltaed system. I actually don't think it uses much of Z3's smt facilities.
### Chase Systems
Egglog's procedure is some variant of the chase.
Datalog+-
See "Benchmarking the Chase". There seem to be some subtle restrictions of egglog compared to full chase that make it simpler/faster/tuned to egraph use cases?
### Prolog
prolog has a union find. That makes something feel similar. This point is still confusing. CLP & CHR are related prolog topics. CHR is capable of encoding basic egglog without too much effort at performance cost. Prolog union find is search branch local. Egglog's is global. Prolog unifies structurally, Egglog makes this optional. Prolog's dfs search is incomplete. Tabled prolog vs egglog? We don't support "raw" unification variables, but perhaps we could (using fresh).
### Formulog
formulog = Datalog + smt
smt = egraph + sat
egglog = egraph + datalog = formulog - sat
### Flix IncA
Egraph analysis is latticy. congruence closure feels somewhat latticy in a hard to pin down way. Automatic joining of "duplicate" entries.
### Proto-Egglogs
Egg-lite, egglog0, souffle-egglog

Maybe ATP




See datalog notes
datafun, flix, rel
DDlog 
propagators
lvars?



## Lattices as egraphs
Datalog for Things without canonical forms. Then egglog is key.
What don’t have obvious canonizing rewrite systems? Groups. Lattices. Given as generators module equations. Why would I do this?
Oh that’s cute. If we want to internalize lattices egglog might be good? but the lattices we talk about aren’t equalitional presentations.


This might be interesting. Hash-consed points-to sets https://yuleisui.github.io/publications/sas21.pdf , I think they are saying that storing all the indexed points to sets as relations is highly redundant, when really you want to store a foreign key to a points-to-set table, memoizing the sets. This foreign key is kind of a reified set identifier. I think one could consider an uninterpreted function based representation of sets (union s1 s1), (sing x), etc  https://z3prover.github.io/api/html/ml/Z3.Set.html https://stackoverflow.com/questions/17706219/defining-a-theory-of-sets-with-z3-smt-lib2  and giving egraph rewriting axioms for union associativity, commutativity  etc. These union egglog enode tables are very similar (identical?) to their operation memoization tables. It's kind of an interesting angle to reifying sets as objects in datalog. Although I have some other ideas of how to do this that don't really require egraphs (I'm currently very tickled by the idea of hash consing patricia tries).

Stack OverflowStack Overflow
Defining a Theory of Sets with Z3/SMT-LIB2
I'm trying to define a theory of sets (union, intersection etc.) for Z3 using the SMTLIB interface. Unfortunately, my current definition hangs z3 for a trivial query, so I guess I'm missing some ...


Martin Bravenboer  33 minutes ago
We tried that too in Doop but it didn't perform well at the time. It's super performance sensitive. I think it'd be better to implement compression in the underlying database system, which would also be more declarative.

Martin Bravenboer  32 minutes ago
It's similar to the idea behind the bddbddb points-to analysis work, which used BDDs for compressing the points-to sets.

Martin Bravenboer  31 minutes ago
I don't recall what method we used, sorry  (>10 years ago ...). It was not sophisticated so maybe it can be done better yeah.

(speculative shadowy idea) Maybe one could write BDDs also using egraph rewriting powers. It'd be interesting to have a system that has both relational and bdds available (if bddbddb didn't already have this. I'm not familiar with it's details)

Martin Bravenboer  28 minutes ago
It's very sensitive to variable ordering, so for it didn't work great for representing all relations (as in bddbddb). But some controlled usage may be fine yeah

There is something pleasing about the user level simplicity of defining their own set representation equationally even if it may not be as performant as a custom extension of some kind. One could say something similar of datalog based analyses in general.
In a related meta direction, one could consider defining a lattice equationally rather than as functions (join is an uninterpreted function that is associative, commutative, absorptive, and obeys individual lattice specific equations). I don't have an example in pocket of where this would be useful (e
But in principle, lattices, like many algebraic structure, are sometimes defined by generators quotiented by equivalence classes. In particular non finite lattices
I wonder if it would be useful semantically to attempt to consider lattices as a subcase of egraph mechanisms rather than egraph union finds as a subcase of lattices. I don't know exactly what I mean, but it smells plausible. (edited) 
I suppose you'd have to know that to fix a functional dependency, you need to apply a join uf to the two eclasses. This idea is of some relation to materializing the join function as a table.



## Harrop Clauses
See also higher order rules
Gensym for quantified stuff. But you can't keep gensyming wantonly. So combine with not guard so you only do gensym once.

## Top down evaluation
Why does CLP seem so similar and yet so far? What is up with dif/2
We can express linear equalities, boolean equalities in SLD
We could ackermaize into booleans.
egraph equality can't fail. unification equality can.

Prolog needs a backtrackable union find.




## Constraint handling rules CHR
A question I never had an answer for https://twitter.com/notjfmc/status/1422215450675535877?s=20&t=RyHMtBS3ySaALLC9MuGmUA . CHR afaik are a way of integrating eager rewriting into prolog https://en.wikipedia.org/wiki/Constraint_Handling_Rules (edited) 

http://www.informatik.uni-ulm.de/pm/fileadmin/pm/home/fruehwirth/constraint-handling-rules-book.html
[chr what else](https://arxiv.org/pdf/1701.02668.pdf)

compiler to sql statements. Makes sense.
Multiset rewriting?
- [A More Naive EGraph](#a-more-naive-egraph)


## CAS

Hmm. You know, I feel like egglog is very close to being able to express this concept via a rule already. If you tag terms with context
 foo(ctx2, ?x,?y) = bar(ctx2,?z)  :- foo(ctx1, ?x,?y) = bar(ctx1,?z), ctxs(ctx2), ctx1 <= ctx2  
It is wasteful to some degree. But not obviously more wasteful than just keeping a labelled graph as a disjoint set datastructure
If we can store lattices in the range of foo, it might be even less wateful

carette discussion https://julialang.zulipchat.com/#narrow/stream/236639-symbolic-programming/topic/x-x.20is.20not.20necessarily.20equal.20to.200/near/232167346
https://arxiv.org/abs/1904.02729 - specifying symbolic computation, carette and farmer


Hmmm. Is extraction some kind of quote operation? If I extract and reinsert, it does nothing. Maybe it needs to be guarded somehow. With like a metalevel annotation? foo -> :foo -> ::foo -> :::foo
a = extract(foo)

##  Quoting out of egraph, reflection

extract(foo(a,b)) = cons(:foo, :a, :b) which is a valid term to put back in.
extract = quote
This is how to extract and reduce lambda calc?

see also higher order rules

## Bisimulation finest partition
https://cstheory.stackexchange.com/questions/37177/partition-refinement-in-transition-state-systems-bisimulation-contraction partition refinment bisimulation is an iterative fixpoint algorithm. Sure we could encode transition system as relation. We need reified notion of partition (like eclass id did). I could model using bitsets in souffle. pairition(bs) <= parition(bs) :- SUBSET(bs2,bs1). Goes twoards finest partition. 

## Typeclasses and Rust Chalk

Something to think about: Applications of egglog to typeclass resolution modulo equality. https://arxiv.org/abs/2001.04301 I don't really have a feel for the relation between tabled top down and magic set transformed bottom up although there clearly is one. I guess I'm also not clear on how magic set works in egglog for that matter. I don't know how to execute egglog top down in the first place.
An example would be finding a typeclass for Vec n a where you take the assoc/comm mult and add  axioms on the size index. Presumably the equational axioms must also be associated with instance dictionaries. Hmm. Maybe this is not as straightforward as I thought. You also need instances for congruence?
There isn't a problem with ordinary bottom up egglog, it just seems very wasteful on a query driven application like this

Chalk is also a very good point. [The cahlk blog posts](https://github.com/rust-lang/chalk) exliciitly talk about specialized equality. That is intriguing. I should contact Niko Matsakis.
https://smallcultfollowing.com/babysteps/blog/2017/01/26/lowering-rust-traits-to-logic/ Prolog + euqliaty reasoning he syas he's looking for

Chalk even talks about making a union find.


asscoaited types
IntoIterator
Item

```
intoiter(vec(T)) :- intoiter(T).
iter_item(vec(T)) = T :- intoiter(vec(T)).


eq(T,U)

query:
into_iter(vec(T))


```
Good examples of multi arg typeclasses?


Provenance of chalk or polonius are importatn for good error messages.

Guess missing clauses?

We need harrop for generic problems?


## provenance
How do we not fuck provenance.


## Semiring smenatics
prvoenance
smemiring smenaitcs
[provenance semirings](https://dl.acm.org/doi/10.1145/1265530.1265535)
[lecture on this](https://courses.cs.washington.edu/courses/cse544/12sp/lectures/lecture18-provenance.pdf)
oh. the max plus semiring. I see.
[souffle provenance](https://arxiv.org/abs/1907.05045)
[provennce guided synthesis](https://www.cis.upenn.edu/~mhnaik/papers/popl20.pdf) - is this related to ruler?

Hmmm. Could you write linear tensor recurrences this way? atoms are still indices carries amplitudes though. How do you avoid recomputation? Collecting up inifintie loops via memoization.
Kind of a feynman diagram thing.
Base propagator list 0f u(0,0, ampl). u(0,1,amp).
Magic set. If we want to query just a single vector?
linear algerba and graph algorithms are known to be connected in this way.
Maybe you need the product semiring to also track index provenance.
The lattice character of max seems important
dynamic programming

shortest path
foo( , iter+1) :-  foo() ,iter < MAX
foo(cost) <= foo(cost1) :- cost <= cost1.

Maybe monotonic increase of probability?.. Eh. Still seems hard to mannage
[https://arxiv.org/pdf/2105.14435.pdf](convergence of datalo over pre semirings - remy papers)
https://arxiv.org/pdf/2103.06376.pdf semiring dictionraries


()
()
()

r
delta_r

r :- delta_r
r :- yada yada r
No that's not good enough. It doesn't know r is already saturated over the rules. Is ther any way to trick it? Directly accessing delta relation is a good point.


[efficient encodings of first irder horn to equation logic](https://smallbone.se/papers/horn.pdf)

[equational term graph rewriting](https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.53.6428&rep=rep1&type=pdf)

I've still never tried just throwin into vampire. It has a horn clause thing right?

https://github.com/nadia-polikarpova/cyclegg

yihong https://drive.google.com/file/d/18m0_fCT21-RLxB8EedmC1MuzhAM4In6X/view
Profile driven optimization. Better scheduling?

Lvars - Guard conditions are filters

What if we rearranged the storage of analysis in egg.

[twitter egraphs for query planning?](https://twitter.com/justinjaffray/status/1501294656239329281?s=20&t=qlKx5dL5bXCILsNAtcDYfw) "like cascades but better"

parent( x : Id, p : Id)


parent(x,p) <= parent(FIND(x),FIND(p)).
parent(x,p) :- add(x,_,p).
parent(y,p) :- add(_,y,p).
 :- parent(x,$Add(x,y)), parent(y,$Add())

## Lambda 

The hash cons modulo equia version uses maps at lampba sites. But then we need to manipulate the maps at the same time we manipulate expressions.
co debruijn? See jasper

https://pavpanchekha.com/blog/egg-bindings.html brilliant. let is synatcticfied substitution. But do these actually have semantics?
This is related to unmooring of succ in de bruijn. Kiselyov finally tagless combinator conversion did something similar.

What about SPJ's points?

### Extract and do stuff
Extract lambdas, reduce, reinsert. It does seem simple. Doesn't produce as much junk.
Seek
app(lam(?x, ?b), ?y) => eval()

app(lam(?x1,?b1), q) = app(lam(?x2, ?b2), q) :- lam(?x1, ?b1) = lam(?x2, ?b2).
No, only is q fresh. forall q. This might as well be "extract and check alpha". I'm not even sure it's right.



lam(?x1, ?b1) = lam(?x2, ?b2) :- lam(?x1,  app(lam(?x2, ?b2), ?x1)), = lam(?x1, ?b1) 



HVM does jive
- graph representation is reminiscent of egraph already (biartite to eclass nodes)
- read out sounds like extraction
- victor's point about only dealing with things that can result from avalaution of lambda terms sounds like only doing egraphs that come from terms.
- 

Two seperate problems:
Alpha recovery vs substitution/normalization
For sums/intergals alpha is what you need.
sum(xfresh, ) isn't _that_ bad. You need to manually recover alpha though. Sometimes this is important. But I've been willing to make bigger composromises

Some nodes can be turned upside down by (multiported going up) by precomposing with a projection. plus(a,b)probably can't since it doesn't have a unique decomposition once we start rewriting.

Lambdas need? incremental copying?
Different "modes". LambdaVar(l), LambdaBod(l) Lambda(body) you need to tie the not with a fresh var.
Lambda(body) where body was contructed using freshv. Then set freshv = LambdaVar(Lambda(body)). Knot successfuly tied. We have an alpha equiavlant rep.
But how does it know which var is it's... Hmm. This is suspicious. Uhhh. No I guess this is ok.
But it isn't alpha equivalent. to a second construction of the same kind. So be it I guess.

parent pointers is kind of an interesting point generally. We can use parent pointers to drive up one level from a concrete term to a non concrete term (variable in one of it's other leaves) efficiently.

I feel like the dup operation makes it so that we have no sharing anymore.


Interesting for substitution. The parents pointers mean we can easily access at least the immediate context in which x occurs.


just requiring uniqueness of var spots doesn't help? I don't know that you can even maintain this under egraph rewriting. Probably not.

sum( share(x0, x1) , body)

Linear pattern rewriting. with explicit clones.

enode containaing share(x,x) can reduce to enode containing x

break eclass into binary eclass? is binary eclass Differetn from share?
n-arity share nodes? surrree. Not really a problem.

What about eclasses represented using pointer style union find. Then enode is redajustable. Can stil have many incoming nodes.

Low level C runtime style egraph. pointer/graph rewriting engine. How do you search it though? Garbage collection style techniques.
Tags. rust enums are tags though. 
Avoid hashing


explicit sharing

### Yinhong let binings
ambda calculus in gogi:

```
sort term.
rel false() -> term.
rel true() -> term.
rel num(i32) -> term.
rel var(string) -> term.
rel add(term, term) -> term.
rel eq(term, term) -> term.
rel lam(string, term) -> term.
rel let(string, term, term) -> term.
rel fix(term, term) -> term.
rel cond(term, term, term) -> term.

rel free(term, string).
rel const_num(term, i32).
rel const_bool(term, bool).
rel is_const(term).

% constant folding
const_num(c, i) :- num(i, c).
const_num[c] := const_num[a] + const_num[b] 
             if c = add[a, b].
const_bool[true[], true].
const_bool[false[], false].
const_bool[c] := true[]
              if c = eq[a, a].
const_bool[c] := false[]
              if c = eq[a, b],
                 const_num[a] != const_num[b].
is_const(c) :- const_num[c].
is_const(c) :- const_bool[c].

% free variable analysis
free(c, v):- var(v, c).
free[c] := free[a] if c = add[a, b].
% unfolds to free(c, v) :- free(a, v), if c = add[a, b].
free[c] := free[b] if c = add[a, b].
free[c] := free[a] if c = eq[a, b].
free[c] := free[b] if c = eq[a, b].
free(c, v) :- free(body, v) 
           if c = lam[x, body],
              v != x.
% fv(let(x, a, b)) = free(a) + (free(b) \ x)
free(c, v) := free(b, v) 
           if c = let[x, a, b],
              v != x.
free[c] := free[a]
           if c = let[x, a, b].
free(c, v) :- free(body, v) 
           if c = fix[x, body],
              v != x.
free[c] := free[pred] if c = cond[pred, a, b]
free[c] := free[a] if c = cond[pred, a, b]
free[c] := free[b] if c = cond[pred, a, b]

% if-true
then := cond[true[], then, else].
% if-false
else := cond[false[], then, else].
% if-elim
else := cond[eq[var[x], e], then, else]
     if let[x, e, then] = let[x, e, else]
let[x, e, then] :- cond[eq[var[x], e], then, else]
let[x, e, else] :- cond[eq[var[x], e], then, else]
% add-comm
add[b, a] := add[a, b]
% add-assoc
add[a, add[b, c]] := add[add[a, b], c]
% eq-comm
eq[b, a] := eq[a, b]
% fix
let[v, fix[v, e], e] := fix[v, e]
% beta
let[v, e, body] := app[lam[v, body], e]
% let-app
app[let[v, e, a], let[v, e, b]] := let[v, e, app[a, b]]
% let-add
add[let[v, e, a], let[v, e, b]] := let[v, e, add[a, b]]
% let-eq
eq[let[v, e, a], let[v, e, b]] := let[v, e, eq[a, b]]
% let-const
c:= let[v, e, c] if is_const(c)
% let-if
cond[let[v, e, pred], let[v, e, then], let[v, e, else]] 
    := let[v, e, cond[pred, then, else]]
% let-var-same
e := let[v1, e, var[v1]]
% let-var-diff
var[v2] := let[v1, e, var[v2]] if v1 != v2
% let-lam-same
lam[v1, body] := let[v1, e, lam[v1, body]]
% let-lam-diff
lam[v2, let[v1, e, body]] := let[v1, e, lam[v2, body]] 
                          if v1 != v2, free(e, v2)
% capture-avoiding subst
lam[fresh, 
  let[v1, e, 
    let[v2, var[fresh], 
        body]]] 
  := 
let[v1, e, lam[v2, body]] 
  if v1 != v2, !free(e, v2), fresh = gensym().
```


basically a straightforward port of lambda.rs. The most interesting thing is probably the definition of free and is_const, both of which are encoded as plain relations and the analyses logic are easily expressible inside Gogi (i.e., no rust code)

Very interesting. Is stratification not a problem on that !free()?

I love the usage of let

Is stratification not a problem on that !free()?
That's a good point. It seems this program is syntactically non-monotonic. I have to think about this more

I’d a little bit suspect something could become free or unfree under rewriting. I’m not sure I understand what free means on an eclass. Free in every term of the eclass? Free in at least one term?
Both notions can probably be useful
Free in at least one term is monotonic under rewriting
Free in every term isn’t

according to the equational theory, every term in the same e-class should have the same FVs?

I’m not sure. Binding and egraphs don’t play nice
I kind of am suggesting that FV seems like it become multiple distinct definitions when extended to egraphs
Notfree in at least one term is also monotonic
The funniness of negation in datalog/contructive logic. !free and notfree are probably distinct notions
!free is “I don’t have proof it is free” and notfree is “i have proof it is the case it is not free”

If two terms have different set of FVs, then they shouldn't be merged into the same e-class, right?
like var(a) and var(b) should never be equiv to each other (although \a.a and \b.b could)

Hmm. I’m not sure. Guard every rewrite rule on the free variable set?
My sense is that it is easy to have the egraph equate things under your feet

if a rewrite rule does not introduce / eliminate fvs, then the invariant should be maintained

Binding is too syntactic and the egraph is too semantic
Maybe.
If this is true it seems pretty dang subtle to me. What if you put a loop in your egraph? Seems like there could be a way to smuggle a variable somewhere it shouldn’t be

\a. a-a = \b. b - b = \c. 0   b-b = 0 = a-a   what is free and bound in these eclasses (edited) 

Ah I see! That's probably because ?x - ?x => 0 is not FV preserving
We could perhaps tag(a,0)  as distinct from 0

One thing we can do is to associate e-classes with FVs
This may be doable in egglog, and is definitely tricky in egg

The full version of tagging is tagging every subterm with it's context, which seem possible. But then many equal things are not seen as equal and there is a lo of repeated rewriting

https://uw-cse.slack.com/archives/C01JJQNFA3G/p1647627785866149?thread_ts=1647532167.160219&cid=C01JJQNFA3G


Hmm. You know, I feel like egglog is very close to being able to express this concept via a rule already. If you tag terms with context
 foo(ctx2, ?x,?y) = bar(ctx2,?z)  :- foo(ctx1, ?x,?y) = bar(ctx1,?z), ctxs(ctx2), ctx1 <= ctx2  
From a thread in egraph-db | Mar 18th | View reply
But it's interesting that you're suggesting maybe a less heavyhanded way of doing it. You only perhaps need to tag terms that don't already obviously contain variables (edited) 
It does seem subtle though. As does anything that has to do with binding and capture
Well, I think the equational rule of lambda calculus should be fine, so maybe only constants / non-lambda terms are troubling
Here is a trick: change the definition of num from rel num(i32) -> term. to rel num(i32, term)., so two nums with same int won't be unified

Yes.. maybe. tag(a,0)  is a weird kind of anti binder. Maybe it should be considered part of the lambda calculus syntax like let is and the rule is you only make rules that preserve free sets like you said
tag : string -> term -> term
forget? unbind ? Better names
It's like an operation dropping an element of the context like how let adds an element to the context
let = insert  tag = delete because the context is a map structure from vars to terms (edited) 
tag is the opposite of let


let v e (tag v b) -> b
(tag v (let v e b)) -> (let v (tag v e) b)  also. (edited) 
 v1 != v2, tag  ?  <-> ?


I suspect tagging may cause a lot of overhead for terms with large set of fvs
Yes. It's bad. I'm not even sure it's safe
my trick (disallowing constants to be unified) may just work, but I need more time to think about that
would be a fun weekend project
It's sort of intertwining using the SMT theory of arrays for the context with a theory of terms. var(x) means lookup key x in context. (edited) 
I hope we have a hoare logic / separation logic / whatever logic for reasoning e-graphs :joy:

! is always going to be fishy in egglog because we assume no stratification by default because we don't expect saturation
It's use requires very careful hard to check thought
For which I have no formal system that seems appropriate
My rule of thumb is to always have a compositional semantic model in mind. That seems to help (edited) 
The semantic model of something with binding terms is quite puzzling
But usually involves some notion of context.
Your use of !free is to block overzealous gensym right? Maybe there is a way to skolemize it instead
Or maybe just remove that rule entirely
Weaker system, but still perhaps able to do something useful

I adapt from here: https://github.com/egraphs-good/egg/blob/main/tests/lambda.rs#L153
lambda.rs
        rw!("let-lam-diff";
<https://github.com/egraphs-good/egg|egraphs-good/egg>egraphs-good/egg | Added by GitHub

this rule is important though since it implements capture avoiding subst

```
% capture-avoiding subst
lam[fresh(v1,v2,e,body), 
  let[v1, e, 
    let[v2, var[fresh(v1,v2,e,body)], 
        body]]] 
  := 
let[v1, e, lam[v2, body]] 
  if v1 != v2.
```
This is the skolemize idea. I suspect it is incorrect (edited) 
In the term world, fresh could in principle be a deterministic function of the pieces you have around? (edited) 
You don't need a globally fresh variable, just one that doesn't appear in e, body, v1 or v2



## Scoped union find
antichain in the equivalence class lattice? no.

reference style UF. UF without path compression. The relationship if id 1 in scope a and id 1 in scope b becomes funky.

Unionfind merge = finesest unionfind that is coarser than the input union finds
Scoped union find is keeping merge implicit. This is .

path compression is absolutely essential to asymptotic complexity, but completely unessential to the specification of what the union find is and should return. It's purely a performance optimization.

Do you want to make merging UF fast or not

```python
class UF():
  def join(self,rhs):
    u = UF( max(len(self), len(rhs.size) )
    for i in self:
      u.union(self.find(i), i)
    for j in rhs:
      u.union(rhs.find(j), j)
    return u
  def meet(self,rhs):
    l = min(len(self), len(rhs.size))
    u = UF(l)
    for i in range(l):
      if self.find(rhs.find(self.find(i))) == self.find(i): #and other direction? I'm just guessing here.
        u.union(u, )
```

```python

class Scope():
  def __init__(self, parent):
    self.parent = parent
    self.parents = {}
  def local_find(self,i):
    while i in self.parents:
      i = self.parents(i)
    return i
  def find(self, i):
    i = self.local_find(i)
    return self.parent.find(i)
  def union(self, i, j):
    #i1 = self.find(i)
    #j1 = self.find(j)
    i = self.local_find(i)
    j = self.local_find(j)
    if i != j:
      self.parents[i] = j

class Scoped_UF():
  def __init__(self):
    self.scopes = [Scope(None)]
  def make_scope(self, s):
    self.scopes.append(Scope( s ))
    return self.scopes.


```


Max has put forward that we need different union finds floating around indexed in some way

Ok he says that what about just a graph with lbaelled edges. connectivity in this graph is union find. Good point. The graph is then literally 
Can I use souffle choice-domain to do somethign good. It gives me an incremental spanning tree.

A more complex union find structure seems like it could be useful. We might way a full non destructive union find. Another option is a "scoped union find". Scopes form a forest. Deeper scopes get the subsequent unions of their ancestor scopes, but not vice versa. Scopes form a partially ordered set.

Options of multiple related union finds:
1. The fillaitre conchon persistent union find has an angle where you really only have one union find active at a time.
2. Using functional maps to implement union find rather than imperative arrays or refs. You don't get path compression? How important is that really? ln(n) vs inverse_ack(n) both feel close to constant.
3. just copy entire union find every time you need a new one. Updates to higher union finds don't immediately propagate to lower ones for good or bad

When you call `find` on a lower scope, you need to traverse up through the higher scopes to collect up any unions they may have accumulated since the scope was created. Is there a way to not require this?

In a sense, scope boundaries are delimitters that stop certain kinds of union find information from being propagated. Path compression is still fine (?), but calling union on a deeper scope cannot be allowed to affect disjoint sets at higher scope. The indirection of scopes never goes away unless you can explicitly collapse them for some reason (if you keep reference to all your children scopes). Collapsing merges yourself into your parent scope, and then redirects your children to your parent.

Other names:
- Marked union find
- union find trie - we could have scopes tagged with interesting info. Or not generated basted on "gensym" counter more or less, but instead looked up by key as in a trie

The pointer perspective on union find seem like it could be interesting. I wonder if literally stack techniques from delim continuations are useful? Copying stacks, markings stacks. Just carrying a scope identifier in the references? That makes sense. You could just not union beyond your current scope. Maybe depth/name?

No you do path compress. The difference is on union. You find up to the scope barrier.
No union is the same. union doesn't require a find.

You only need to refer to the equivalence classes of the scope above you. So deeper scopes could be quite small. Hmm. Hard to see how to do this.


It almost feels like it might be a "macro scale" union find, but I don't really see how to implement union on two scopes. It would be unionfind merge + ?

Maybe it's sort of keeping a stack of union finds that are implicitly being union find merged. But we hold off to share access to the upper ones.

union = keep top of scope. Perform full find. Set top of scope to this? Or just perform union at top of scope?

Copy on write optimization (COW). `Vec<Option<Box<Page>>>` Separate domain into pages. If None, assume no change compared to scope above. If deep scopes are small changes this could lead to memory savings. At the expense of even more indirection though.


```rust
type SUF =
{
  size : usize,
  ufs : Vec<ScopedUF> 
}


struct Scope(usize); // scopes are just labeled by integers into the ufs vector
struct ScopedUF {
  parent : Option<Scope>, // may be root
  uf : unionfind //Vec<usize> // maybe make Either<Vec<usize>, SimpleMap<usize,usize>>. For scopes where not much action happens, we want a sparse fast map.
}

impl ScopedUF {
  fn default(size) {
    ScopedUF {parent : None, uf : default() } //0..size.collect() }
  }
}

impl SUF {
  fn fresh_scope(self : &mut Self) {
    self.ufs.push(default(self.size))
  }
  fn build_child_scope(self, : &mut Self, s : Scope) {
    let d = default();
    d.parent = Some(s);
    self.ufs.push(d);
  }
  fn upstream(self : &mut Self, s : Scope) {
    // This is just destructive unionfind merge? So we could merge any scope s into any other s' really.
    // iterate through scope calling union on parent
    let uf = vec[s.0];
    if let Some(parent) = uf.parent {
      //let puf = vec[parent.0];
      for i in 0..self.size {
        // but we don't even need to do a full find. We only need to to a local lookup up to next scope
        self.union(i, self.find(i, s), parent);
      }
    }
  }
  fn scope_parent(self : &Self, s : Scope){
    self.ufs[s.0].parent
  }
  // fn upstream_and_destroy? Need to fix children of scope, which if we maintain we can do. Otherwise just call destroy leaf
  //
  fn upstream_range(self : &mut, start : Scope, stop : Scope) {
    // You can call upstream in a loop
    let mut s = start;
    // actually it might be important to start at the top and work down.
    while s != stop {
      self.upstream(start);
      s = self.scope_parent(s);
    }
  }
  fn find(self : &mut Self, id : usize, s : Scope){
    // ordinary path compression
    let uf = vec[s.0];
    while let Some(parent) = uf.parent {

    }
    // No: At scope boundaries, either still do ordinary micro path compression, or perhaps merge up completely to canon of next scope.
  }

  fn delimit_find(self : &mut Self, id : usize, s : Scope, stop : Scope){
    // perform find up to scope `stop`
  }
  fn scope_find(self, id, s) {
    self.delimit_find(id, s, s)
  }
  fn union(self : &mut Self, id1 : usize, id2 : usize, s : Scope) {
    // can union 
    // maybe do parallel find scope by scope so you can early stop.
    //
    

  }
  fn push_parent(){
    // it does seem possible to insert a new scope between yourself and your parent easily.
    // make your own parent pointer point to new scope, make new scope a fresh one pointing to your old parent
  }
  fn destroy_leaf_scope(self : &mut Self, s : Scope){
    // add to dead list, clear it's data. We're incrementally heading towards a memory allocator at that point.
    // But maybe that's ok.
  }
}

```

Can you get away with just tagging? I don't really see how this works.

```rust
struct SUF = {
  uf : Vec<usize>
  scopedepth : Vec<usize>
  rank : Vec<usize>
  scopename : Vec<usize>
}
```


It's reminsceint to me of marking in delimitted containution implementation

In some sense what you want are blockers or barriers to the path compression process. Path compression should only propagate up to the scoping barrier because other scope may have the same parent. - This isn't what I think anymore?
Questions:
Magic set transformation? What does backward chaining in egglog look like? Could this use a partinitioning algo?
I guess you could do it clp/chc style 
{x = y} as a set of constraints doesn't seem that interesting. It's always possible.
Well, just pattern matching doesn't need `=`
What about a static analysis of a rewriting system.
Abstract domains of all seen terms.

## Higher order rules
We could use this
[horn into eq](https://smallbone.se/papers/horn.pdf) to reflect rules themselves into the egraph?
So what if rules are just containutation of sorts. Save points? Defunctionlization kind of? Closure kind of? A little weird. Feels a bit like magic set. Feels a bit like some kind of memoization. We could flatten out all patterns into this.

```
foo(x,y,z) => bar(z,w,q) => ziz(x,z).
```

becomes
```
foo() :- rule1(x,z).
rule1(x,z), bar(z,w,q) => ziz(x,z)
```

even rwrite rule
`foo(?x) <- add(?x,add(?x,z))`
can becomes

```
chk1(q, x) :- q = add(x,y)
foo = add(x,q) :- chrk1(q, x), q = add(x,z)
```

You only need binary multipatterns in other words.


## Semantics of Egraphs
PER over Nat is truth object.
Relations are maps into union find indices.
In isolation it looks like bottom-unit.
But other predciates map into0 some "other" unit.
A function never maps into more values than its domain size.

Partial functions ~ a -> option b = unit + b
Uninterpeted functions ~ a -> PERNAT + b = Hom(a,b)

It's a particular element of PER nat.
Refinement is a relation between PERNats. 
b is more known than a an eleemtn of the PER

Parametricty inspiration. Somehow these abstract elements hide 
mappins of eqclass to concrete values




You know, partial equivlaence relations is a more appropriate lattice.
It better represents what ywe're talking about. PER over Nat is exactly ids and unionfind.
Makeset(i)
makeset : Nat -> PERNAT

Function tables are partial functions

The I don't want to talk about "ids" could probably be takn care of via categorical style construction
projection arrows into a thing. Like a pointed thing. L is special.
     ^
     |
  -> L  <- 



[Yihong egglogish semantics](https://necessary-taker-84c.notion.site/Egglogish-6fce65a95af542f4964db0146eb00c8a)
[egg sem remy](https://hackmd.io/@remyw/egg-sem)
[formalizing egg#](https://necessary-taker-84c.notion.site/Formalizing-egg-53b650e3d91f42058172a877caf0950a)
A Herbrand universe U is the set of all possible terms you can build out of some set of function symbols
Example:
- add(-,-), succ(-), zero , the Herbrand universe is {zero, succ(zero), add(zero,zero), succ(add(zero,zero)), ...}
- for symbols a,b,c,  the Herbrand universe is just {a,b,c}.



The powerset of the Herbrand universe $$\mathcal{P}(U)$$ is the set of all sets of terms. Sets form a [lattice](https://en.wikipedia.org/wiki/Lattice_(order)) under the operations of intersection and union.

Lattices are a useful notion in computer science. The algebraic propertiers of commutativity, associatvity, and idempotence means you don't have to be careful or can change the order of operations and everything still comes out good. 

Monotone functions are functions tha respect an ordering $$x \le y \implies f(x) \le f(y)$$.  The [Knaster-Tarki theorem](https://en.wikipedia.org/wiki/Knaster%E2%80%93Tarski_theorem) says that a fixed point of monotone operations exists.
I think a lattice homomorphism is a distinct stronger concept?


A Datalog rule defines a function between $$r : \mathcal{P}(U) \rigtharrow \mathcal{P}(U)$$. You can convert this operation to an expansive operation via the combined rule $$ X -> X \cup r(X)$$ that adds in the new pieces to the pieces that were already there.

A monotonic operation between lattices is one such tha it respects the latice ordering.

Because the Herbrand universe of datalog is finite because it only had atoms / 0-arity function symbols, no monotonic operation can expand forever.

A partition of the Herbrand universe is a subset of the powerset. It is a set of sets whose union is the entire universe and which do not intersect. A partition can be interpreted as equivalence classes.
Partitions also form a lattice. There is a partial order of coarser and finer partitions. You can find the finest partition that is coarser than two others. This is a meet of those two. The partition where every element is in it's own set is the bottom, the partition consisting of just the entire set is top.

The set of all partitions Pa(U) is a subset of the powerset of the powerset of U.

A function symbol is basically a function between n copies of the Herbrand universe.
A function symbol can be lifted to function that work over powersets $$[f] : \mathcal{P}(U)^n \rigtharrow \mathcal{P}(U)$$  $$[f](X) = \{ f(x_1,x_2,...) | x_1 \elem X_1, x_2 \elem X_2, ... \}$$.

It is a little unclear what it means to lift f to work over partitions. But this notion is where the semantics of congruence closure lie.
The problem is we are tempted to be working over one particular egraph. But this is awkward and non compositional?

$$A^B$$ is a notation to represent $$ B -> A $$. The powerset of A can be written as $$2^A$$.

A lattice annotated powerset `X : Pa(U) -> X -> L` = $$ \prod_{X : P(U)} L^X $$. X represents the egraph we are currently working in.

P(T) := True.
(a -> Prop) -> Prop


The relational model
Instead of function symbols, we have relations (over what? integers? abstract keys? Maybe this is what a categorical model might help with.)
function symbols are relation symbols with a functional dependency
Rather than being a tree, a relational term has pieces which are multi ported graphs?
Congruence becomes a secondary consideration

What if we considered each argument to the function being from a different union find 
LxLxL -> L

And then we also have like a forker and joiner or somethig.
    _______
   /
---
   \_______

L -> LxL

LxL -> L  (meet)

does `f` even do anything to the union find structure?
Yes, it has to combine them. It also performs congruence closure on f application

The image of a partition
[f](PP) = { ~f(P) | P \in PP} = { { f(p) | p in P} | P in PP }
Do I need to do some union cleanup here? I might.
{   U_p_in_P{  f(p') |  for P' in PP if p in P' for p' in P  } |  P in PP } assuming {} dedups?

concrete example
{f(a) , f(f(a))}, {a} - image -> {f(a)} { f(f(a)), f(f(f(a))) }
No this isn't a problem. Because f is injective as a term function

Okkkkk....
What we're describing is kind of just egraphs with analysis and conguence close but no rules.

So we end up with L as a fixed point of this process (the analysis normalized egraph congruent?)

So... a rule is... a pattern match is...? 
L -> {matches}

matches also form a lattice. (you can merge bindings)

L -> {matches} of a multipattern can be done in any order and merged

an "applier"

multimatch =  (pat1 | pat2 | pat3) . joinmatch . ( app1 | app2 | app3 )

rule  (searcher | searcher | searcher) . (app1 | app2 | app3) : L -> L
f* = [f] . fork : L -> L
g* = [g] . fork : L -> L
and so on

fix(f* | g* | rule1 | rule2)

Yes.
Whqat really does congruence closure. It's the combo of f with the join semantics

Patterns as egraphs
we never 

Where | has semantics of join/meet on output.

Applier...

match -> L ???

fix(meet(f.fork, g.fork, a, id)) = the whole egraph normalization


exists P : Partition, P -> L
where L is a lattice
```coq
Inductive Term : Type :=
   string -> list Herbrand -> Herbrand.
(* Is this acceptable? Not sure it will be. Anyhow *)




Definition TSet := Term -> Prop. (* Bool? *)

(*
A particular restricted herbrand universe


*)

Definition schema := list (string * nat) 
Definition valid (s : schema) : Term -> bool := fun (t : term) =>
  match t with
  | name, args => if lookup (name) == List.length args then List.forall (valid s) args else false.


Record FinPartitioning := {
  partitions : list TSet;
  complete : TSet
  disjoint : Forall2 partitions (fun x y => forall t, band (x t) (y t) == false)
}.


Record Enode := {
  head : string;
  args : list nat
}.
Definition egraph := list list Enode.
(* 

Definition egraph := { Term -> Term , with fixedpoint exists}.


*)

(** conversion to TSet *)
Definition in_eclass (egraph : egraph) (eclass : list Enode) : Term -> Bool :=

Definition denote (egraph : egraph) : FinPartitioning := 


Definition Partition := list Enode. (* A little disatisfying. *)
Definition Partition := TSet.


```







A lot of things are implicit in the egraph. They have to be because it's talking about an infintie number of terms


Implicitly f(a) = f(b) in the egraph.

Q = (Herbrand Partition -> A) is the basic lattice of the egraph analysis


f : QxQxQ -> Q  is combo congruence closure and analysis transfer function
By default things can just return bottom, so you get to choose which trasnfer functions you define


a : () -> Q

So these are semantics, but then relating this back to a finite representation (and an efficient one)








## NE graph
 See also bisimulation partition refinement
 
https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.637.1146&rep=rep1&type=pdf co-nelson opppen.
Combining theories through inequalities. Somehow condindituvie/bisimulation
analysis + opt https://dl.acm.org/doi/10.1145/565816.503298 sorin. Do dataflow while optimizing?

If you can say _nothing_ in X equals anything in U\X.
cons(a,b) != not cons

So the input to not_eq is 1 set.
a pattern describes a set.
cons(?a,?x)
Indeed this is stating a form of injectivity
Or more than that? We are also saying that f(7) = cons(7,[]) is not allowed
cons is an ocean unto itself.
{cons(?,?), f(?), g(?,?)} is stating closed universe assumption only f and g have access to constructor cons.
Ok, but nothing can call f or g either. too closed

Should this be about terms? Contexts? co-terms? objects? automata? graphs?
What Set representation to use? Is Set the wrong alley?

concrete ineuqalities as the _rules_. Patterns go in the negraph?
If we find 
can match a + b using the current negraph, we derive a pattern from it we assert as disjoint?
cons(?a,?b) is a distinct _pattern_ from all others, even it it isn't a distinct function/constructor really.
cons(cons(?a,?b), ?c) is not distinct from cons(?x,?y)
Multi match? Views? Pattern synonyms
Maybe the pattern match coverage problem is a good one? Coverage and defunctness.
| Cons(Cons(a,b)) ->
| Cons(a,b) -> 
| _ -> 


I guess when you know things have distinct types you know they can never be equal. It doesn't even make sense.
If you have equality reasoning on types that can be touh to say out of hand though (unless injective)

distinct( ?x : hom(?a,?b) )
disctinct( ?x : ob )

types are a way to 



That's interesting. A formalization of the inaccessibility of certain constructions.
private.
{ ctor1, cto2, class_method1, class_metho2,  } states a closed class definition.
Can we express subtyping? Seems hard.

But is separates off an entire mini universe.

can anything call meth1?

?ctx[ clor1(?,?) ] also describes a set of terms. Anything that contain ctor1
{ ?ctx[ match(cons(?a,?b), rhs(?a,?b))  ] , ctx } No. Doesn't really work. We don't want to say has to any rhs has to include the match form?
I guess that's eta expansion. Hmm.

_Everything_ else is seperate? We have to descibe very small equality classes.

Give X, X and U\X are distinct.
What methods of describing X are useful here.
disjoint(X)

disjoint(X,Y,Z) st XuYuZ = U or disjoint(X,Y) Z is implicit = U/X/Y
but disjoint(X) /\ disjoint(Y) is the same thing.


foo(?a) != bar(?a) is there a way to talk about this?
{ .. . .. . . foo} { .... . . . . bar} but what are all the dots?

Just contexts? "dual" to terms?





subclass {ctor1, ctor2, ctor3, meth1, meth2, meth3}
superclass {ctor1, ctor2, meth1, meth2}

->
meth3 can't access ctor1 or ctor2? That's not right.

{}  {} 

pattern matching?
f(cons(?,?))





Lambda binding:
Optimal evluation work relevant?
Compiling lambda terms relevant? Closures? Reflection into host? Uncurrying trasnformation?


[egg-smol](https://github.com/mwillsey/egg-smol)
labelled equalities
eq(l,x,y)
l could be integers, a hierarchy of eq. colors
tuples of integers?
Absract symbols 
they could be a context coming from lower egraph.

## Egraphs over programs. Program analyiys


// seperately sotre the egraph and the term? Which souffle gives you by default.



x := a + b
x := 0
surely a + b is not availabe.

if we assume ssa then we never lose expression.
What if it got overwriten? Then it's not available..?




Functions from store







Wait this is the obvious killer app.
Very busy expression and available expressions




Poinbter analysis.
https://szabta89.github.io/publications/inca-pldi2021.pdf 


unification-based point-to analysis 
VSA: interval analysis + periodic analysis 
https://www.cs.cmu.edu/~aldrich/courses/15-819O-13sp/resources/pointer.pdf Anderson vs steensGaard


kCFA is a place where datalog and lambdas meet. Could there be something good there?


.type Expr = Lit n : number | Lam symbol Expr | App Expr Expr 

init($)

subterms() :-
label($,) :- init()
context(t, Hole):- init(t)
context(x, Add(Hole, y) :: c), context(y, Add(x, Hole) :: c),  :- context(Add(x,y), c)

% literlas are equal under any context.
context(Lit(n), C1) = context(Lit(n), C2) 
% alpha renaming?
context(Var(x), C1) =? context(Var(y), C2)

Interesting idea.

Anyhow. Once you build contexts, you can do cfa
sigma(l, n) :- context(Lit(n), l)
sigma(l, t) :- context(Lam(t), l), sigma( Lam(Hole) :: l,  v )

https://dl.acm.org/doi/10.1145/3136040.3136043 quoted staged rewriting

I don't want all subterms. Equal subterms should be different things.
If egraph gets top, what does that mean? Early termination, what does that mean?

Is a union find a lattice? One that largely stays the same except when crossing binders
join of two egraphs is 1. union of symbols. 2. closure of equalities.
identity element is egraph with no terms.

avalaible expression analysis is reminscent. You could use a (persistent?) hash cons. Well you could store inefficiently, but there is almost certianly some efficient wya to do this. available equalities.

Inner scopes inherit from outer scope except when viarables are introduced.

http://moskal.me/smt/e-matching.pdf ematching for fun and profit
https://github.com/yihozhang/sdl staged datalog
https://github.com/yihozhang/egraph-sqlite egraph on sqlite


grobner bases. What is a term? a monomial? a entire polynomial in canonical order?



https://www.categoricaldata.net/cql/fmc.pdf Fast Left-Kan Extensions Using The Chase. Uniqueness quantifiation

[Sketch-Guided Equality Saturation
Scaling Equality Saturation to Complex Optimizations in Languages with Bindings](https://arxiv.org/pdf/2111.13040.pdf). De bruij indicies for lambda calculus. Guidance of rewrite rules.

<https://github.com/mwillsey/thesis> willsey's thesis

<https://twitter.com/corbinsimpson/status/1456649872182939654?s=20> corbin simpson using egg for categorical combinator.

https://github.com/gussmith23/glenside



staging ego (ocaml egraph) could be fun.
Also could try to extract the alt-ergo implementation.

<https://github.com/mwillsey/snake-egg> I approve 


bdds are both more and less than hash consed if then else trees. See fillaitre paper. Can I embed bdds into an eg raph implementation? Bddbdddb used bdds as the backing store of a datalog. Pretty clever and cool. I actually feel like this might be more powerful in many cases of interest than a relational representation.
eqrel representation is also a lattice. The join is the smallest equivalernce relation that works, that's kind of the beauty of it.
What cody wants is a custom relation domain. .decl(  )


hasahing modulo alpha equivalence
- false positives and false negatives
(x + 1) can be totally different things in different contexts
why not de bruin? ok sure. de bruijn are inefficient. false negaitvfes nad false positive
position maps of variables with structure maps.

e-summary - alhpa equivalent if same e-summary


hashlog using souffle.
If I keep the numbr of entries small, I could make a hashing function and just pretend no collisions happen. Or use cryptographic hash
hashcons + union find = egraph


module system - algebraic specification
discharge using smt? A style with which to structure smt proofs.
discharge using egglog - signatures are queries, impls are databases.
Embedded in ocaml, julia, or python.
sexify using modern looking syntax (ryst like? leanlike?)
mod Foo : {

}
semi-naive ematching
applier should return (Id,Id) tuples and also Id of new nodes generated.
This is the fresh information.

I should try building a datalog.
Maybe take a particular datalog program and write it out.


congruence closure as an axiom in the theory.
f(x,y) = f(z,w) :- f(x,y), f(z,w), x = z, y = w.
seminaive based on an update to one of the equations on the right hand side.

parents(x,f(x,z)).
parents()
 :- x = z, parents(x, f(x,X)), parents(z,f(z,X)).

all tables should only be maintained modulo equality. Stock souffle does not do this for me.



Denali and epegs - denali is almost a parallel idea to the uniqson work but from a theorem prover persepctive rather than constraint programming perspective

Egraphs and ematching and instruction selection
If I did not use any union finding, egraph is a hash cons.
Ematching is hash cons matching

egraphs for program syntehsis. That's intriguing. Armando notes and Koppel paper.


Call ematch. Record all matches
Send off to cover solver.

Combine the blindell universal function + epeg





DOUBLE EGRAPH WOAAAH
Yea. I could just maintain 2 egraphs if I want to have 2 notions of equality.

https://www.southampton.ac.uk/~gk1e17/chaseBench.pdf
The chase. EGD and TGD functional dependencies
These both seem like things i want.

memoization of patterns
I used the devie
pattern(A,B,C) :- yada
to record a pattern match. This reifies the bindings of a pattern into a table.

But we can do the same in the egraph and egglog.

zzz :- f(f(f(f(f(X))))).
patmemo(X) <- f(f(X)).
zzz :- P = patmemo(X), f(f(f(P))).

congruence closure and memofixing updates

semi-naive - just search over changes for one of the predciate.
There are many many implicit flattened predicates.


Proof scripts - query and forget egraph but push result into facts / rules if true.
?+ == copy egraph. query. insert into old egraph if true.

Allows proof scripts like this
?+ x = y.
?+ y = z.
?+ z = foo.

?+ x = y.
?+ .. = z.
?+ .. = foo.

?+ x = y.
.. = z.  // allow suppression of ?+ in presence of .. syntax
.. = foo.


?+ forall X, foo(X) => bar(X).  // make fresh X. qeury egraph. If works, insert as lemma. If fails stop program here.



Scoped rules

{
  foo(X) :- bar(Y).

}
// rule is dropped here.
:- push.
:- pop.
:- push_rules.
:- pop_rules.
:- push(egraph).
:- pop(egraph).

"calculating compilers" using an egraph approach. Is this possible?
Instruction selection as an egraph problem?


Hmm. Can you use the size of eclasses to solve combinatorial problems?
Can you implement ZDD or BDD in egrpah form? hash consing is how that kind of works

https://www.youtube.com/watch?v=W4kveStDZXI&ab_channel=YOW%21Conferences hashing moduleo alpha

hashlog - egglog without the union find
Keep a hashcons data structure. It can store all known facts and trees.
hashcons matchign
Semi naive seems more dable
Could I add hashing to souffle to get egglog back?



"egraphs" for higher homotopy? ports are edges?

egraphs for graphs
Take all subgraphs. You can compose named ports to each other
Self consistency - a loop in the g-graph. (g stands for graph) Like some kind of microscope thing
The hroizotnal and vertical composition i already noted was sort of deconstructing to alll
possible decompositions using the nameless positional encoding of string digrams
If we took a string diagrams and put every possible term decopmosition into it from the get go. Because the graph is already a caonnical form in rgards to associativity. It is not in regards to other equations.
Eclass -> [  ]


Hash consing graphs ( depends on dcomposition method, unless you hold eclasses of all possible decompes)



https://asplos-conference.org/abstracts/asplos21-paper142-extended_abstract.pdf

This is interesting sounding
Did they use egraphs for instruction selection I wonder?
Like suppose you had a rewrite rules going from ir to instruction selected ir (+ a b) = (arm_add32 a b)
But you also had IR -> IR equalities
Like (+ a b) -> (+ b a)
and I suppose MIR -> MIR rules would be possible peephole optimizations

There is a similarity between PEGs and blindell's UR and or expression graphs
Actually, what it would do is pattern matching.
Pattern selection would require a secondary optimizatioon problem

How do you instruction select over an egraph
consider a muladd instruction a*b+c
but you have a*(b+d) in your tree.
You want to egraph rewrite and then cover egraph.

Parition refinement is the "dual" of union find - a system of inequalities.
Reverse congruence. f(a) /= f(b) -> a /= b
contrapositive
the dual of an egraph

If we had observations and had to deduce what went wrong
The greatest equivalence relation consistent with the facts
as compared to egarph which is least equiavlacne relation

algebra and colagebra




Egraphs = coinductive? They are the least solution to a set of equations. The looping behavior is reminscent of CoCaml and CoLP.

Cody seems to think pasting of two pullback squares could work.
Hmm. Can I make an ematching quantifier for pullbacks?

Universal quantifier
d    b
     |
     v
a -> c

p -> b
|
v
a
for any p and two morphism such that square commutes, we get a new morphism univ_0(x,y)
with equalities associated with it. And uniqueness?
so we need to be guarded by some tough equalities
ok but fine.
But then to prove universality of the pasting
We can assert some object and some square.
But we need to deduce the universal morphism and prove that it has good triangles. and uniqueness?

What about just epi and mono. Hmm. I need exactness too
https://en.wikipedia.org/wiki/Five_lemma




An igraph - an egraph for inquality reasoning? Some smart datat structure for holding inequalities rather than union find or in addition to? Then the pieces that arec monotoonic lift inequalities through constructors.

PEGs
Convert imperative to functional program essentially. Gated-SSA. Convert back
Generalizing proofs for compiler optimizations: What? Something about 

prolog gensym
Well, gensym is possibly sufficient for my egraph thing. a map to unification variables? nah



https://www.cs.cornell.edu/~ross/publications/proofgen/
Substitution as a category. Free variable nodes. Can I substitute in an egraph? Is subgraph query doable (prob not right)? Substitution via enforcing an equality between the variable nodes and the terms that 
i'm substiution them for. Or no yeah. I could really go in an cut them out of the eclass they belong to.

https://dash.harvard.edu/bitstream/handle/1/4762396/pldi84-tristan.pdf a followup paper - translation validation
https://www.cs.cornell.edu/~ross/publications/eqsat/ equality saturation compiller optimiztion
PEGs program expression graphs
gated ssa
The nodes of loop variables represent the sequence?
Partial sums. Makes sense from an inifite series perspective.
psum f = 0 : (map f 0..10) + (psum f)
!! is indexing function.
We need to lift various things via repeat
and map under layers
data MultiList acc =
MultiList = a + [] + [[]] + [[[]]] + ...
Multilist a = Free [] a
data MultiList a = Roll [MultiList a] | Pure a
Reminsicent of fock space. Not quite. There's something there.

The sum = eval psum factoring somehow makes the de bruijnn raising and lowering more local?
psum has a short self referential definition in terms of +.
sum does not generically?
There was a comment on zulip about geometric series summation
sum g^n = 1 + g * (sum x ^ n) which is a self referential defintiion.
The endpoint moving definition is in some sense equiavalent to the psum
This is inductive rather than coinductive. Is coinductive + egraph somehow important?
sum(n, f) = f(n) + sum(n-1, f)
sum(0, f) = 0 

psum(expr) = cons(0, psum(expr))
psum(n, expr) = lift(n, )


Pawel - essetnailly algerbaic theories. string diagrams something
freelinearfunctions
linearmaps.jl linearoperators.jl
interacting hopf alggerabs

Right, The term model makes differences between schedulings
Yolk.jl, mixtape
abstractinterpeter
alternaitve exceution pipline
runtimegernated

mixtape emit function can dump out bullcrap
mccoy becker
mjolner irtools
bang bang jl 
temporal relation


IR as a category. Keno papers
Single blocks optimization

The egraph as a database.

pattern matching datalog - 
The PATTERNS are dtalog? You could reify the rebuilt egraph into a database. Sure.
But then querying a pattern agains it?


conjunctive queries - np complete
worst case partial join
schedulers.
Thousands of rules.
credit assignment

simulated annealing?
oliver flatt working on proof production in summer


Explicit contexts and context lifts using named variables.
We want local transfromations, because the ergaph gets in the way of stuff
We want thing to be semantic unless we can turn off selective congurence closure.
Explcit contextx will largely be shared.

bound variable expressions
actually extracting good linear algebra
catlab stuff.
proofs.
datalog



lift(x, e)
select(y,e)
Kind of goofy
barendregt convention. gensym new sums
sum(x, e) * sum(y,e) = sum( sum())
reqiures explcit x != y check
x and y should not be eclasses. They are explicit parameters

We can punt on alpha recovery.
sum(i,i) = sum(j,j) is ok
Not this can cause problems
sum(i,i) * sum(j,j) = sum(i,i) * sum(i,,i) 
!= sum(i, sum(i, i * i)) which may result from missing inequality guard above. 
With rearrangement, is this enough?

used variables analysis. ->
sum(x, e * b) = e * sum(x,b) if e does not contain x

Model: Important.
T = (Key -> Int) -> R
sum : key -> T -> T
sum k f = sum $ map f (\i -> \m -> if k = k' then i else m k') (1 .. 10)

x :: T
x m = toReal $ m "x"

y :: T
y m = toReal $ m "y"




Egraphs as rtelations  http://effect.systems/doc/relational.pdf
Datalog + some fields are equivalence classes?
Souffle could do this?

eclass(a,b) .equiv
eclass(a,b) :- f(x,y,z), f(x1,y1,z1),
              eclass(x,x1), eclass(), ,  // One per congruence relation
enode(n, q) 

equiv(n1,n2) :- f(n1, x, y), f(n2,x2,y2), equiv(x,x1), equiv().
equiv() :-
equiv() :-


A pattern match is a query
Q(Root, A) :- f(Root, x,y), g(X, )



Alpha equiavalence:
New enode type? Pointers down or up from binding site? Or to third kind of node?
Recover alpha equiavalence via explicit search somehow
Explicitly model contexts?  x |- x  is different from a |- x
"Hypothetical" unioning? Requires persistent backtracking of unions. Seems useful for recovering alpha.
lam x f ~? lam y g.  if x ~ y => g ~ f. Niavely requires double search for lam over egraph.
Well, what might trigger a new alpha equivalence?

Name and de bruijn in parallel? lam x g g'
de bruijn. Combinators. Same thing? The swap operator was not good. Pushing lazy raising and lowering. It had some nice properties too. raise(u,l) or something? Maybe swapping sum is a bad example to work with.
Names are nice because we have non local character so we can manipulate binders but leave alone use sites
sum_j sum_i q => sum_i sum_j q
de bruijn is nice because we have canonical names. Alpha equivalence becomes automatic.


CatEngine - get david to draw me a cat engine hybrid
Metaocaml + egraph? Ocaml egraph could be good. As cody was saying

Ematching patent application?
https://patentimages.storage.googleapis.com/26/5a/2e/9a7722870e4dbb/US8103674.pdf

Type isomoprhism reasoning in egraph
fix x, 1 + x  is list.
fix x, f x ~ f (fix x, f x) fix equations
quantifiers
semantic model is relational model of paremtricity?
Theroensm for free reasoner?
Ordinary alegebra 0 + x = x, ayda yada
+ yoneda like things from that one paper
https://homepages.inf.ed.ac.uk/wadler/papers/free-rectypes/free-rectypes.txt
lfix x,, f x ~ forall x, (f x -> x) -> x



Proof production:
Does z3 actually keep proof data in the egraph?
The extended union find gives reasons.
I guess every up link has reasons
We maintain another array registering which parent gets attached to which parent.
And an array when a root becomes a child, we record a canonical term at that time. And perhaps we only need to record an enode at that time, since we can look for older stuff? Does the array build a temrpoal order on the nodes?
The "best" enode. or a random one?
Or is it insertion time. At insertion time Eclass == ENode. Maybe we want to record that?


We need to perform an extraction every time we find a new equality? Best term in Eclass equated to best term in other eclass.


Multipatterns and datalog
Allessandro made this analog that is interesintg.
You can use the egraph as a "database" of terms
And use multipatterns to insert new terms. This is just a hash cons.
But you can also use = as a special symbol on both the left and right side of prolog rules
To create new equalities, and to check out ones
What are the syntactic restrictions on dastalog?
We aren't unifying, we're just pattern matching. Is that a problem? A difference?

Semi naive evaluation. Is it possible to only try to match terms that are updated?


Alessandro has this idea of anti rules. These are probably problematic to integrate with this search. Negation is often a funny fellow


b = c :-  b, a = b, c 







Ok, looking back. Could I make a Z3 version?
Horn solver maybe. Careful triggering.

ZX calculus?

Einsum - compile to matrix form. Then do point-free rewriting. This is spore approach
https://optimized-einsum.readthedocs.io/en/stable/
https://github.com/Jutho/TensorOperations.jl

It also feels like compiling a lambda abstraction to combinators.
The bracket abstraction http://www.cantab.net/users/antoni.diller/brackets/intro.html
lam x. b =>

\x -> E K ()

sum(i -> E) = K

Am I crazy about using explicit indices? Is that not just fine? I should have a crisp objection.


sum_i = 1^T like in probability
a_ijk b_ijk =>  dumb trasnlation of otimes with dup.

logic sound with respect to model
untyped lambda is unsound? With respect to what model?
[x]y = K y
[x]x = I



sum(i, i)
sum(i, i * x) = 
-- we need to know x contains no i. This is not clear. We could imagine an "contains i" analysis.
can contain i vs has to contain i. 



Functional programmng and rewrite systems:
Very similar. 
- pattern matching
- recursion

The dom(hom) type trick more abstractly is that you can internalize
functional programs into the egraph rules. You want to do this lightly.
I used this as both guards and to produce complex reight hand sides 
(non productive ones. Hmm Is this another connection to coninductivity?)




We don't have built in higher order functions.
You lose deterministic control
(lam )
(x :: Gamma) |- succ t = Gamma |- ts
eval t env = 

De bruijn-ish something is important. We don't get alpha renaming for free so it's a natural way
to canonicalize that
Egg went a little extrajudicical
But can you write eval for a sum?
You can, I jst don't want to expand it.
eval (Sum t) env = sum [eval t (i :: env) | i <- 1..10]
Maybe gamma should just be the integer like cody said
An outer context lift
n |- succ var 

lift n = n |-, takes an m < n dimensional function and lifts it to n-d.
We can store n as an int.
Or we could store the range in the context.
Wouldn't that be somethin.

de buijn levels would be useful.
They locally record that we don't need your shit. Uh. Wait. No this is indices
sum(succ(x)) = N * x


succ(x) * succ(y) = succ(x * y) -- can extrude lifting through simple functions
succ(x) + succ(y)
x * y = y * x
sum(x + y) => sum(x) + sum(y)
sum(succ(x) * y) = x * sum(y)
sum(1) = N 
sum(var) = N * (N -1 ) / 2, or benoulli poly 
sum(succ(succ(succ))) = b(n,N)

sum(var(1)) = 
sum(var(2))
succ(var(n)) => var(n+1)

x = x * 1


Those two rules give
sum(succ(x)) => sum (succ(x) * 1) => x * sum(1) => x * N
sum(sum(succ(var) * var)) => sum( var * sum(var) ) => sum(sum(var) * var) =>


sum(sum(x)) = sum(sum(swap(x)))
swap(var) = succ(var)
swap(succ(var)) = var
swap(x * y) == swap(x) * swap(y)
swap(x + y) == swap(x) + swap(y)
swap moves through everything like succ. (Except succ. It doesn't move through succ).
Feels very expensive.


swap(succ(x)) => succ(lift_var(x)) -- Then we don't need the extra swap(succ(var)) rule.
lift_var(var) = succ(var)
lift_var(succ(x)) => succ(x)
lift_var(x * y) = lift_var(x) * lift_var


lower(n, succ(x)) = succ(lower(n-1, x))
lower(0,succ(var)) = 
lower  
raise(0, var) = succ(var)

raise(n, lower(n-1)) ? Can't be. the intermediate state makes no sense.

de bruijn do have these useful rasing and lowering operations though


Well, it may indeed be _an_ encoding. so i dunno.

A setoid egraph. 
congruence closure could be written as a rule
x = y => f x = f y 
enumrate all f, or allow matching in the head position.
This is a guarded rule.

I've said the egraph is semantical because it builds in congruence closure. So you need to be talking about something for which congruence closure makes sense.
In particular, I think you should have a model in mind for your syntax. Given a term, you should be able to give me functions for the function symbols and elements for the constants, such that your mathemtical thing obeys your rewrite system.

Yes, yes. Peano arithmetic is fiendish. I know. But each move is meaningful.
The succ forms opens up the lazy push around.



GATs for binding
Nathanael Arkor12:26 PM
You describe everything internally: so you have a type for "contexts", a type for "types", a type for "terms", etc. Then you have operations for extending contexts, etc. This is essentially the approach of "type-theory-in-type-theory", which uses quotient-inductive-inductive types (which are closely related to GATs).

Equational metalogic Fiore http://ropas.snu.ac.kr/~gil.hur/publications/soeqlog.pdf
https://crypto.stanford.edu/~blynn/lambda/logski.html the oleg paper


Cody:
```coq

Definition Ctxt := nat.

Definition ext : Ctxt -> Ctxt := S.

Inductive Lambda : Ctxt -> Type :=
| Var : Lambda (ext 0)
| App : forall Γ : Ctxt, Lambda Γ -> Lambda Γ -> Lambda Γ
| Abs : forall Γ : Ctxt, Lambda (ext Γ) -> Lambda Γ
| Weak : forall Γ : Ctxt, Lambda Γ -> Lambda (ext Γ).

Definition id : Lambda 0 :=
Abs 0 Var.

Definition K : Lambda 0 :=
Abs 0 (Abs 1 (Weak 1 Var)).
```

I want to do sums:
N^n -> N

Realtion to quantum raising and lowering operators? Is that ludicrous?
extending the context = adding on a free parameter = (N^n -> N) -> (N^{n+1) -> N)
weakening the context = (N^n -> N) -> (N^{n-1} -> N) This makes no sense. You can evaluate it, 
sum over it, maximumize over it. You can't just wekaen it.

Jon sterling using GATs from Kris
http://www.jonmsterling.com/pdfs/algebraic-universes.pdf


Note on Mechanized Equational Reasoning for Categories with Metatheory.jl

Here's the punchline

```julia

```

I'm sure you've always wondered if that was true.

In terms of a string diagrams:
![](/assets/pairproj1proj2.png)


Read on for what this means


Compile the egg version for wasm and embed


## Metatheory and EGraphs

Alessandro Cheli has made an extremely intriguing package called Maththeory.jl. As I understand it

- Homoiconicity
- Some mumbo jumbo that I don't understand but is probably very important about using RuntimeGenerateFunctions to ge the right hand side of rules to be fast
- A tuned and feature complete EGraph implementation

I've discussed implementing EGraphs in Julia on this blog before. 
- https://www.philipzucker.com/egraph-1/
- https://www.philipzucker.com/egraph-2/
EGraphs are a data structure that efficiently achieves sharing of subterms in the presence of equality reasoning. The [egg](https://egraphs-good.github.io/) project has recently innovated and brought this technique to prominence

Here's the basics of how you use the Metatheory EGraph backend at the moment

```julia
using Metatheory
using Metatheory.EGraphs


```

I wrote my EGraph implementation with the intention of using it for this blog post.
I've previously written of my abortive attempts using the automatic theorem provers E prover and Vampire and Z3.
- https://www.philipzucker.com/notes-on-synthesis-and-equation-proving-for-catlab-jl/
- https://www.philipzucker.com/theorem-proving-for-catlab-2-lets-try-z3-this-time-nope/

I don't know why these encodings did not work. It still feels to me that they should've. The black box nature of these systems is a problem for troubleshooting.

Catlab is built around a kind of logic called Generalized Algebraic Theories (GATs). 
- https://algebraicjulia.github.io/Catlab.jl/dev/#What-is-a-GAT?
- https://ncatlab.org/nlab/show/generalized+algebraic+theory

In multi-sorted first order logic, you have terms of simple sorts like G or Int. For convenient encoding of categories you need a little more magumbo. One wants to talk about A as a term of sort Object, but then also talk about $$id(A)$$ as a term of sort $$Hom(A,A)$$. You see that the sort of `id(A)` is dependent upon a term `A`. This means that some kind of dependent type system is at play. This is possible to encode into Coq for example, but GATs are a less complicated system that has enough flexibility to do this. They're some kind of dependent types lite.

Encoding this type system correctly is tricky. I naively thought in the first post that basically the issue could be ignored, since every equation is type preserving. If the types start good, and the rules are type preserving, then everything is ok right? This has not been the correct mental model of the situation. It is highly dependent upon the exact reasoning system the degree to which types can be ignored.

A somewhat brute force way of dealing with types is to encode terms as terms tagged with types. For example, instead of merely using the term `id(A)`, we replace it with the syntax `typ(id(A), Hom(A,A))` or the equiavlaent infix syntax `id(A)::Hom(A,A)` that looks like a pun on Julia syntax or `Hom(id(A), A, A)`. The latter form was pointed out to me by James Fairbanks and it has the advantage of fusing 1 level of indirection (In a sense partially fusing the tags `typ` and `Hom`). Really we want to perform this tagging recursively like `Hom(id(Ob(A)), Ob(A), Ob(A))`. This gets incredibly verbose to type out for a human.

Some other notes

- The rewrite rule `f => id(A) \cdot f` produces A out of nowhere if types are erased. That means they either need to be reconstructed.
- Catlab overloads $\otimes$. This makes sense to Julia, because Julia is tracking the types of things and uses them for dispatch. In order to track the types for dispatch in our
- It has been argued that one could use the Julia type system to encode GAT types. The construction of Metatheory.jl makes this a light weight if possible. I argue that this is unlikely. Part of the cleverness of Catlab was to avoid abusing the host type system like is common for categorical constructions in Haskell or Agda.

Type tagging maybe be familiar to the programmer in you in that is the logical reflection of the technique of dynamic typing. Dynamic types are implemented by maintaining a tag at runtime describing how to interpret the attached data. We are in essence doing the same thing in our syntactic rewriting system. We get dispatch based on this type in the same manner that Julia or python get dispatch off of their type tags.




There is absolutely no reason to overload \otimes for both morphism product and object product from the persepctive of mechanization. I admit it is nice to have such overloadings for people, but they should be quickly stripped off for internal representations via inference. I chose to keep them syntactically distinct.

The technical connotations of "sort" vs "type"



James Fairbanks10:58 AM
GATs are a fixed point of the "X can represent Y" relation so they make a good target as a level of generality


Philip Zucker: I thought way back that this preservation would just happen if you strip the types like it does for STLC or something, but it doesn't. I think this misconception is due to my inexperience doing hand calculations of this type (which almost no one does. String diagrams rule), plus I think you "code the happy path" when doing it by hand and may not even notice a situation where just shallow pattern matching on the syntax would allow you do do something verboten, since you're smart enough to not make that dumb mistake. It's also easy unless you're being hyper careful to take big steps that seem obvious but aren't actually implied by the axioms you have.

Philip Zucker: Furthering this misconception is that for a large majority of the 30 some axioms for cartesian SMC it actually _is_ completely fine, I think. So far I've only identified about 4 or so where it's a problem, one of which is the interchange law.

Philip Zucker: And it also can only be using the axioms in particular directions too. One direction is syntactically safe, but the other direction requires checking typing conditions

Philip Zucker: Trick question: Can you apply the interchange law (f ⊗ g) ⋅ (h ⊗ k) => (f ⋅ h) ⊗ (g ⋅ k) to the term (f ⊗ id(a)) ⋅ (id(b) ⊗ k)?

Philip Zucker: No you can't. In my example, f actually has type b ⊗c -> b ⊗c   and k has type c ⊗a -> c ⊗a .

Philip Zucker: The other direction is always fine though. Given (f ⋅ h) ⊗ (g ⋅ k) is well typed, so is (f ⊗ g) ⋅ (h ⊗ k)  I believe.

Philip Zucker: Again all this is obvious in string diagrams. So obvious as to be unobservable.


Egraphs as a model. Z3 uses EGraphs as models of logical statements about uninterpeted functions
We can also consider sets as models of egraphs.
An egraph is a model of a conjunction of equations if 

An interpretation of an egraph is a mapping of function symbols to functions 
and constants and equivalence classes to elements such that if there is a function symbol enode in an eclass, the function interpretation maps the interpetation of it's children classes to the class the enode lives in.
This might be easier to read in mathemtical symbolism.




### Bits and Bobbles

Where to go from here:

2. Actually integrating with Catlab. Does it scale?
3. Daniele Palombi has brought the coend calculus https://arxiv.org/pdf/1501.02503.pdf This seems like a very interesting application. I think the direct attack on this problem using Metatheory requires understanding how to deal with alpha equivalence in the EGraph Conversation here: <https://julialang.zulipchat.com/#narrow/stream/277860-metatheory.2Ejl/topic/Formal.20Proofs.20for.20CT.3F>
4. String diagrams <https://julialang.zulipchat.com/#narrow/stream/230248-catlab.2Ejl/topic/Using.20Metatheory.20for.20String.20Diagrams> There is a compelling argument that string diagrams are a preferred representation, normalizing the associativity,commutative, and unit properties of a categorical construction. It has been suggested by Alessandro and others that teneralizing the EGraph data structure in some sense may be to go.
4. Proof production. Giving 


One wonders if perhaps with my new understandings I could get z3 to work.

I had some verbose encoding I wanted to try
But I also feel like this internalized type thing could work in z3

The external z3 ematcher


Alpha conversion. Add parameters to function symbols.
sum(n, f) : (N^{n+1} -> N) -> (N^{n} -> N)
n is the number 
sum(0, f) = f ??? Eh why bother
sum(1, f)

ind(n, i) == proj(n,i) : N^n -> N
the ith projection of an n tuple. Play the roles of indices
sum(1, sum(2,  ind(2, 1) * ind(2,2)  )  )  )
sum(n, sum(n-1, ind(n, )  ))
Based on the semantic model, I feel like this makes sense.

Every operation also needs these scope tags.
These scope tags are equiavalent to marking both de bu9ijn indices and level

likewise for derivatives
(R -> R) -> (R -> R)
D(n,m, f) marking n input size and m output size
Or perhaps start with only scalar.

Huh. Maybe everything is working in fock space?
Then sigma is a lowering operator.
Fock space is a useful model of a world where we're moving around the number of variables in existence
Disjoint sum of function spaces

adag is adding on a delta function
adag(x)
adag(i,x)

sum reduces the number of free variables by summing over the leftmost one
Ok, but we want to sum over more than just the leftmost.


What about explicilty modelling homotopy functions.
f(0) = a
f(1) = b
g
g
k(1/2) = f(1) = g(0) - contingent upon a proof of f(1) = g(0) that this new function is definable?
k = compose
allowance of a move
 f(x,t) = f
 f(0,0) == 
f()
forall x : [0,1], f(x) = x
f




A decalartive rule interchange format



Could we literally use smtlib?



(set-option :verbose)
(set-option :scheduler :backoff)
(set-option :node_limit)
(set-option :type-check)
(declare-sort  )
(declare-fun  f)
(declare-fun  f)
(assert (=  expr1 expr2 ))
(assert (!=  expr1 expr2 ))
(check-sat)

(declare-rule )
(declare-eq   )
(check-eq  expr1 expr2)
(addexpr expr)
(simplify  expr :iter :timeout :node_limit :  )
(push) -- pushes rules or pushes state of egraph?
(pop)
(push-rules)
(pop-rules)
(clear-egraph)
(exit)

https://rust-cli.github.io/book/crates/index.html

We could have the thing build the corresponding rust file for you.
For guards we'd need a full programming languge
I could build in the facilities to 


There is something rather intuitinistic about the egraph.
If you had propsitions in the egraph, having 
p = True, is really more like p = Proved.
Since not having it does not imply that p is false
p = False is known falsehood
p = True is known Falsehood
neither is unknown
I guess it's more like 3 valued logic.



Condictivtely, egraph is "well-typed"
Each GUARDED rewrite rule maintains well typed-ness

Given the left hand side has matched a pattern that is in fact well typed,
we can infer some equational constraints about the types.
If these equational constraints do not fully imply the typing of the equational
rule, then these extra conditions must be added as guards.



We should 
1. Check the condition
2. Add the typing terms to the egraph so it at least know to refine these.



Definition of well typed:?



Ituitively speaking, an egraph represents a possibly infinite set of terms.
A pattern represents an infinite set of terms. A pattern `f(?a, x, ?a)` represents the set of terms that include $\{ `f(x,x,x)`, `f(y,x,y)` , f(g(c,d), x, g(c,d))...\} $, ie. all the terms . Tis descrption format of sets forms a lattice. The lattice operations of join and meet are defined via 

A (multi)rooted egraph represents a possibly infinite set of terms. It is the set of terms you can build by starting at the root and following the links.
The egraph `[x a]` where a has an edge to the class represents the terms `{x, a(x), a(a(x)), a(a(a(x))) ... }`. 

The allowance of cycles in the egraph makes it unclear to me how to precisely describe the infinite terms. There's something very coinductively at play here.

Perhaps it represents the set of terms with possibly class ids at the leaves. That feels more honest somehow. You start with the root id S_1 = {root_id}. Then you can expand one step to expand this S_2 = {a(root_id} or S_2 = {a(root_id), root_id}. Eventually a subset of these will be the finite terms. 





James made a number of good points



Maybe a highest de bruijn index analysis?
Lowest?
Bothm right,.
Then if they split

sum_examp = @theory begin
   sum( sum(a(0) * b(1))) |>  sum(a(0)) * sum(b(0)) # factoring
   sum( sum(a(0) * b(1))) |> sum( sum(a(1) * b(0))) # permute sum symbol
end

Bidning forms: de bruij indices with raising and lowering
Avoiding accidental dummy clash. Moving pieces out from 


There was that one paper that showed the equational form of the yoneda lemma
in terms of fxied point operators and stuff.

 = a^b  a * b, yada yada.




Dowke higher order unification mentions associativty as a problem like comprehension axioms.

Uniform type tagging vs inline type annotations is kind of like closure vs defunctionlaization
A uniform representation / a specliazed one. A closed world of constructors vs an open one.
Rust enums make the closed work convenient and fast.

Higher order equality reasoning. Equalities of equalities. Dijsktra style. Equality patterns.
Actually by adding equality nodes to every other node, we get equality patterns for free.
(eq(a, a)) but of course.
eq(x,y) => eq(z,w) but then we also need to propagate z = w downward into the graph. Hmm.
Mutiple kinds of equivalnce relations interacting?

Actually only is eq(x,y) is in same eclass as true should be propagate it
eq(x,y) = p  is a condition equation upon the value of p. only if we learn p is true should we propagate this info.
ForAll([x,y], (eq(x,y) == True) ==  (x == y) )
ForAll([x,y], (eq(x,y) == True) ==  (x == y) ) vs
ForAll([x,y], eq(x,y) ==  (x == y) ) ? This is still correct in a sense. It's just that I want to trigger on (eq(x,y) == True)
Can i write a trigger like that in Z3? I'm not sure i can

and(x,y) == x == y == or(x,y)
egraph equality, predicate equality, 
or(x,y) == or(y,x)
or() = asssociatve
or(x,x) == x

eq(y, y)
eq(y,x) => eq(x,y)
eq()

definitional and propositional equality.
eq() can be a question, tentative knowledge, however equailvance clases in the egraph are known knowledge.

Mathmeth
https://www.cs.cornell.edu/home/gries/Logic/Equationalhistory.html
https://www.cs.cornell.edu/home/gries/Logic/Equational.html

EGraphs that are string rewriting.
Mark out EClass 1 as special markjer for empty string.

a memoizing trie? DAG trie. Double ended trie. Links going up and down.


Take the technique of my path post but add more concrete objects.
We do I need the types. I keep getting confused.
id_A != id_B. They need to be kept as distinct objects.

Note just because I'm using z3 "Function"s does not mean we are only discussing categories of functions. Z3 uninterpeted functions are pretty much a completely syntactical construct. Well, ok in a sense we are in that vbia a Yoneda embedding really they are natural transformations between HomSet functors.


Well, I could just keep generating new canonical types.

```python
def all_objects():
  a,b,c = "a","b","c"
  for i in range(n):
    # instantiate the laws for these news objects?

```

How are we going to denote otimes? At the symbol level?
otimes( F, G  ???
F and G are natural trasnformations and otimes is a thing that takes natural transformations returns a new natural transformation
otimes(F, G, FG)
otimes( hom(-,A), hom(-,B), hom(-,AB))
otimes( hom(-,A), hom(-,B)) -> hom(-, AB)

add in all the definitions of otimes, and it's axioms

The extra bits of GATs are sort of what is needed to throw into first order logic in order to make categorical constructions more elegant, in particular the partiality of compose (compose requires that morphisms meet on the same object)
Compose can be defined as a mere relation on morphisms in first order logic, but it is clunky. compose is typically a partial function, for which you'll need to enforce extra axioms to cut that subset out of relations. Extra axioms that you need to keep using over and over increases the complexity of both interactive and automatic proof. It is worht considering if there is a way to make something so fundamental baked into your reasoning system rather than just an axiom in the system. This is perhaps the entire study of logical reasoning systems baked in a nutshell. Want to study computation? Well maybe beta reduction should be baked in your reasoning system. Or maybe not. Worth trying.
A sufficiently flexible system can also build a raft of technqiues, encodings and lemmas that the underlying fundamental reasoning system is not particularly relevant.


a variable of sort "hom(-,A)" represents an morphisms that ends on (codomain is) A



How does z3 even encode types to it's egraph. The types and arity just become part of the function symbol?
Yeah, you could intern the whole thing. arity, string and types


2 tricks:
1. Using the morphisms ~ function. Associativty axioms replaced by function composition. 
2. Using Z3 sorts as objects
3. brute force object expansion.


Interesting example: two symbo0ls a b and they commute. Each element of this monoid is isopmorphic to just a pair of 
naturals.
Can we prover (2,2) + (2,2) = (4,4)?



Metatheories ability to canonicalzie dynamically might be very useful.




# A More Naive EGraph

I know that a significant fraction of Julians worship at the shrine of performance. This is not my default shrine. I still feel like most problems I encounter in my hobbies and work are limited by how difficult the are to phrase and solve even naively, and once that is done performance is 9 times out of 10 not an issue. If it is, then it is time to tweak and reconsider. This is of course informed by my problem domains, that I'm rarely trying to build libraries for others, and the fact that I leverage a massive, mind boggling raft of tools built by people who are deeply concerned about such things, and, uncharitably, that my work does not matter to anyone.



Alessandro Cheli (who is a dynamo of energy) has been building a package called Metatheory.jl, which includes a more feature complete and optimized egraph implementation written in Julia than the one I've described in my blog posts. In addition, my understanding is he's trying to take homoiconicity seriously.

So the version of egraph I'm about to describe to you is not my recommended one, unless you're in a time crunch maybe. Nevertheless, because of it's simplcity, I think there is more conceptual clarity to it.








Or flip something out of the trie to put it in the egraph.


https://taliasplse.wordpress.com/2020/02/02/automating-transport-with-univalent-e-graphs/ 
Talia had a blog post?

Egraph notebook from allssadro

https://colab.research.google.com/drive/1tNOQijJqe5tw-Pk9iqd6HHb2abC5aRid?usp=sharing#scrollTo=zikCWjHH14YH

Ed Yang's egraph in python 
https://twitter.com/ezyang/status/1340507843292770306?s=20
https://gist.github.com/ezyang/c3db0e55a7661998c8a66ea8619f1081

Struct
head:
args:
end
 curried in maps.

Term => EClass becomes
Head => (Args => EClass)

What happens if two args becomes unified?
Is that a problem to keep them seperate?


It's kind of nice to not key on something changing under our feet.
It's not so nice that we can't resolve args without checking into the
intdisjointset
Using straight up pointers we could be pretty fast.
No. It's hard to make an indexing structure that respects the equivalence relation

If i used fixed size tuples in an array, 
Then it could be pretty fast in a certain sense.

Dict{:Symbol, Array{  Tuples{Args, Class}  }}

The product equiavlanece class? Yes.


merge(E,E) = just append arrays
normalize(  ) = for each symbol
        double loop check? Insufficient since we merge classes
        if we get a match .

Wait. That normalization is congurence colsure?
If all the arguments are equiavlanet, then the terms itself is equivalent.

0, unary and binary can get you pretty far. Maybe everywhere
With precompilation

struct Egraph
unionfind :: IntDisjointSet
constants :: Dict{Symbol, Vector{ Int64 }}} # IntSet?
unary:: Dict{Symbol, Vector{ Tuple{ Int64, Int64  }  }}
binary:: Dict{Symbol, Vector{ Tuple{ Int64, Int64  }  }}

abtriary?::Dict{ (Symbol,arity Int64)   , Array{Int64, 2}}}
parent_sym?:: Dict{Term, :Symbol}

end


Could keep the vectors weakly sorted?




Metatheroy.jl and alessandro
Matchcore
He's using Expr. Fine. I still don't really see how 
RuntimeGeneratedFunctions.jl
The world age problem - modality?


Perhaps a mistake was trying to match catlab syntax as much as possible
From haskell, I know many type parameters are inferrable.
Inferrable data in some sense should be kept out of the syntax tree. They just gum it up.
I got bit exactly by this when working with a theorem prover whose mechanism was out of my control
Forward reasoning on forall id(A).f => f because it could instantive f with a nonsenical type unless guarded.
I still can't hel but feel my original opinion in my first pose was essentially correct

Catlab annotates more than Haskell does, but it is not fully annotated either
It relies on type inferrence
We could add perhaps inferable annotations to catlab.
We also want a de-elaboration for the rewrite system?
Stupid algo: try to remove parameter, run inferrance. If it comes back something?

I feel like we don't need types. The rewrite rules respect the typing. Preservation.




id(A) the A is unnecassary. there is always an id that works.
Unification

If the translation from Catlab is nontrivial and not general purpose for all GATs, that takes a lot of bite out of working in julia in the first place. I might as well just stick to native rust.




A special patern for assocaitve rules.
Have rerwite rule comp/2( A comp/2(B,C)) => comp/3( A,B,C) # normalizaes associativty


Allow matching for neighboring positions in term
comp/n(... ,  X,Y, ... ) => 


2 obvious tasks
Make pattern matching fast
actually try to apply to catlab or some other domain?


http://taktoa.me/eqsat/Thesis.pdf remy gldschmit's bachleor's eqsat
https://gist.github.com/ezyang/c3db0e55a7661998c8a66ea8619f1081 yang python egg



In an application where we are trying to do equational reasoning, we have some pile of universally quantified equations like $\forall x. x + zero = x$ .
The e-graph is storing ground terms, ones that do not represent a universal quantification. The e-graph stores the fact $seven + zero = seven$ and $two + zero = two$ separately even though these are instantiations of the same underlying fact.

A natural approach to equational rewriting is to turn your equations into rewrite rules, which are a related but distinct thing. Rewrite rules pattern match a left hand side and replace it with a right hand side. 
Rewrite rules have an asymmetric flavor between the right and left hand side, whereas equality is more symmetric.
Applications of rewrite rules do no necessarily commute. Applying rule 1 and then rule 2 is not necessarily the same as applying 2 then 1.
One can then apply in some order the rewrite rules, hoping for the best, or maintain a set of all terms reachable.


SymbolicUtils arranges its matchers to take an expression, a dictionary of already known bindings, and a callback function that takes a new dictionary and the number of elements matched. Here's a snippet from the library for comparison.

[link](https://github.com/JuliaSymbolics/SymbolicUtils.jl/blob/cd18c76fd09078c38393b398e681329f257ecfe8/src/matchers.jl#L1)
```julia

#### Pattern matching
### Matching procedures
# A matcher is a function which takes 3 arguments
# 1. Expression
# 2. Dictionary
# 3. Callback: takes arguments Dictionary × Number of elements matched
#
function matcher(val::Any)
    function literal_matcher(next, data, bindings)
        islist(data) && isequal(car(data), val) ? next(bindings, 1) : nothing
    end
end
```


Related Libs:
* SymbolicUtils
* Match.jl
* MLStyle.jl

Make egraph generic like egg by implementing in terms of a children and istree function.
Kind of how symbiolic utils does it.

end

generic egraph over anything that implements istree yada yada. call getchildren(::T) rather than .args
children!() tpo update children
children
Basically converts it to


$\forall x. x + zero = x$ becomes 

The equations that produce these equivalences

In application to finding new rewrites, we need to be adding new equalities to the EGraph.





Duality
If you reverse all edges, DAGs remain DAGs.
Unification propagates downwards
Congruence closure propagates upwards

What if we reversed the dag and hash consed all the parents? How similar would congruence closure look like to unifacation

Hashcons Ids vs union find ids. "Fundamental" indirections. The catlab people have convinced me that there is some fundamaenetal character to the indirection that occurs via foreign keys inb databases. So should we too consider there to be a fundamental character to the Ids?
memo :: f(Id) -> Id. Set of endofunctors f on Id? 
A unification relation ~ ( term(x) , otherterm(x) ) . The signatures of the two don't have to match, but the variable sets do. Whereas the opposite is true of composition.
 f Id  <-  Id  ->  g Id  ~~~~ g Id2 <- Id2 -> h Id2.
 Pullback gives Id3 and equivalence set of Id1 Id2.
  Maybe consider the hash cons version?   Id <- Id -> Id
  the met parts perform union [ 2,6,8,1]   [2,5,7,9,5,3]
  No it makes more sense going the other way.
    Stuff -> EquivClas <- Stuff   union find
    [1 ,4,5]   
    Then 
function compose_cospan(f,g)
   unionfind = IntDisjointSet( max(f.apex, g.apex))
   for (x,y) in zip( f.right, g.left)
     merge(x,y) 
    end
    newleft = find_root.( f.left)
    NEWRIGHT = find_root(g.right)
    # maybe a normalization step to return to a range 1..Nequiv_class
    CoSpan( newapex, newleft, newright )
end

It does seem like this makes sense. I dunno what you do with it.
I mean, a pushout _is_ union right?
This is in catlab under colimit.
Does this suggest that maybe I should be implementing EGraphs as a CSet?
There is this complicated schema of Equiavlanece nodes and hash Ids.
    [1,56,7,8,  ] 


EGraphs as a CSet
objects:
EClass
FunHash

morphisms:
1 per function symbol
Maybe functors? Takes multiples EClass

congruence closure does feel like some kind of universal property. It's the largest relation under something

If function symbols are morphisms,
then They can be represented as n-d arrays on the available equaivlance classes.
It avoids the need for a hashmap. At the great expense of being able to be less lazy?
We need like a lazy sparse array. That uses 0 to denote uncomputed.
But a hash table is a lazy sparse array
I guess we could have 1 hash per function symbol. Since we always know the head.
Yea, these forms don't seem useful, but it's an interesting persepctive.

A data structure is a lot like a database

I guess the other interesting takeway that one might have is the other direwction
A hashmap can be like an avluator. memo[ f x y z ] = result.
memo[f x y z] ~ curry ~ memo[f][x y z]
So we don't have to make the correspondence morphism = array

So, where to next?
3 roads.

- implemente pattern matching in z3py
- implement pattern matching in julia
- bind to egg

Egg reference the Z3 macthing paper nad the simplify matching paper
"
E-graphs and E-matching. E-graph were originally proposed several decades ago as an efficient
data structure for maintaining congruence closure [Kozen 1977; Nelson 1980; Nelson and Oppen
1980]. E-graphs continue to be a critical component in successful SMT solvers where they are
used for combining satisfiability theories by sharing equality information [De Moura and Bjørner
2008]. A key difference between past implementations of e-graphs and egg’s e-graph is our novel
rebuilding algorithm that maintains invariants only at certain critical points (Section 3). This makes
egg more efficient for the purpose of equality saturation. egg implements the pattern compilation
strategy introduced by de Moura et al. [de Moura and Bjørner 2007] that is used in state of the art
theorem provers [De Moura and Bjørner 2008]. Some provers [De Moura and Bjørner 2008; Detlefs
et al. 2005] propose optimizations like mod-time, pattern-element and inverted-path-index to find
new terms and relevant patterns for matching, and avoid redundant matches. So far, we have found
egg to be faster than several prior e-graph implementations even without these optimizations.
They are, however, compatible with egg’s design and could be explored in the future. Another key
difference is egg’s powerful e-class analysis abstraction and flexible interface. They empower the
programmer to easily leverage e-graphs for problems involving complex semantic reasoning
"

Term Indexing - Chapter 26 of the Handbook of Automated Reasoning
Data strucures - 
 - Trees or dags. Aggressive sharing vs hash cons. Nelson Oppejn 1980
 - Flatterms. flatten out tree into preoder traversal. Possilby with skip pointer
  - Prolog terms


  - automata based
  - Code trees 


String based indexing - idea: convert patterns into approximate string matching pattern

position sdtrings. We can lay out the terms in some sequence, let's say a preorder traversal. In addition can annotate with positions
This does actually remind me of Code2Vec

https://link.springer.com/chapter/10.1007/3-540-62950-5_59 shostak congurence as a completion algorithm

https://www.microsoft.com/en-us/research/wp-content/uploads/2016/12/krml253.pdf - leino pit claudel

It seems like having a slow but interpretable e matcher would be helpful. 


bjorner and de moura good ematching
prolog - warren machine
Avbstract machine
 pc - current instruction ? weird.
 reg[] - storing ground terms
 bstack - backtracking

```haskell
type Symbol = String
data Machine = 
  | Init Symbol Machine
  | Bind Int Symbol 

data State = State {pc :: Int, bstack :: [Machine] , reg :: [Term] }

cont (Init m) = m

run :: Machine -> State -> State
run (Init f ) { r = [Term f args]   } = s { reg = args  }

```



code trees


Path indexing