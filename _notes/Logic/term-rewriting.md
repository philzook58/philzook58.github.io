---
layout: post
title: Term Rewriting
---

- [Abstract Rewrite Systems](#abstract-rewrite-systems)
- [String rewriting systems](#string-rewriting-systems)
- [Completion](#completion)
- [Term Orderings](#term-orderings)
- [Termination](#termination)
- [Higher order rewriting](#higher-order-rewriting)
- [Egraph](#egraph)
- [Graph Rewriting](#graph-rewriting)
- [Systems](#systems)
  - [Maude](#maude)
    - [Unification](#unification)
    - [Equation Search](#equation-search)
    - [Category](#category)
  - [K](#k)
- [Other Systems](#other-systems)
- [Misc](#misc)

https://www.stephendiehl.com/posts/exotic02.html 

Term rewriting and all that
Term rewriting - Terese

# Abstract Rewrite Systems
This is sort of a study of relations and transitvitym, symmettry.

confluence
church rosser

# String rewriting systems
Word problem
Monoid presentation

converting to term rewriting system fff ---> f(f(f(X)))

# Completion
Knuth bendix

Naive completion

```python
# Fig 7.1 in TRAAT

# rewrites as tuples
R = {("a", "b")}

while not Rnew.issubset(R):
  R = R.union(Rnew)
  Rnew = {}
  for (lhs,rhs) in R:
    lhs1 = reduce(lhs)
    rhs1 = reduce(rhs)
    if lhs1 < rhs1:
      Rnew.add((lhs1, rhs1))
    else:
      Rnew.add((rhs1, lhs1))

# Could use maude to actuall perform reduction.
```


```python
def init_eqs(E):
  R = set()
  return (E, R)

def deduce(ER, u, s, t):
  (E,R) = ER
  # confirm u -> s, u -> t
  return (E.union({(s,t)}), R)

def delete(ER,s):
  (E,R) = ER
  assert s in E:
  return (E.diff((s,s)), R)

def 


```


# Term Orderings

# Termination
https://github.com/TermCOMP/TPDB termination problem database

https://termination-portal.org/wiki/Termination_Portal
Termcomp 2022 https://termination-portal.org/wiki/Termination_Competition_2022

2021- 02

Coq and termination
Accessibility relations, Sam's paper
Bove-Capretta method - a Defunctionalization of the Acc method?
Adding an accessibility parameter - delays the requirement of proof to when it receives this




2020-12-07

Polynomial interpetations - each function symbol goes to some polynomial. variable stay variables.
f(g(x,y)) ->   yada yada
If you bound you coefficents to integers and small, the nonlinearity of the coefficients from f and g aren't persay a problem

RPO. recsurive path orderings.

String rewriting termination. The simpler model.
abc -> cdf
assign each guy to an nonegative integer.
a + b + c > c + d + f.

This one is actually an ILP.

This is polynomial interpetation where concat/cons symbol has intepretation of plus and each constant symbol has interpetation of a number.

http://www.cs.tau.ac.il/~nachumd/papers/termination.pdf dershowitz termination review 1987

The obviously terminating stuff always decreases
Doesn't always decrease, but clearly we lose 3 aaa to make a c but only gain 2 a from a c. We're losing net a every time we make a step.
c -> aa
aaa -> c

strategy : build string model of finite depth term rewriting system. See if it works.
build ground terms instantiation on term rewrite system. Constrain somehow
Possibly try to encode "good" thing in objective function.
Find failure. iterate.
This is a cegis.



2020-03-09

A Harmonic Oscillator. Prove that it is stable. Build lyapunov function. Can do with SDP. V >= 0, st. $latex \frac{d}{dt} xVx <= 0$. Or better yet $latex \frac{d}{dt} xVx <= \eps$ or $latex \frac{d}{dt} xVx <= eps (x V x)$.

Also could consider breaking up space into polyhedral regions (quadrants for example. Find a piecewise linear lyapunov function.

Another interesting problem is to prove escape from a region. Prove that osciallator eventually escapes x>=1. No prob. We also get a bound on the time it takes.  V(x) = cx. dot V = c xdt = c A x <= eps forall x >= 1.

min eps,   forall x. c A x - eps <= lam (x - 1)  ... this is not possible. lam needs to become a positive polynomial. No, it is possible if lam = cA xhat  and eps <= lam.

An interesting discrete analog of this system would be a swapper. x0 >= 1 implies x0' = x1, x1' = x2, x2' = x3, x3' = x0-1. The minus 1 gives us a small decay term.

For a string rewriting system, the simplest thing is just look at some kind of count on the symbols. Maybe with some weighting. It may be that you are always decreasing. If just count doesn't work, you can try 2-grams or other features/combos. This feels something like a sherali-adams 

For term rewriting, we could try to ignore the parse structure and use the count as string rewrite as above. Polynomial interpetation appears to want to interpret a term that is applied as a polynomial. This seems like it would create difficult nonlinear constraints for both verification and synthesis. Although if you constrain each polynomial to be bounded integers, it may make sense to pound them into a sat solver. Ok if each intepretation is only linear, then the combined would still be linear for verification.

AProve [http://aprove.informatik.rwth-aachen.de/index.asp?subform=home.html](http://aprove.informatik.rwth-aachen.de/index.asp?subform=home.html) aachen

TTT innsbruck [http://eptcs.web.cse.unsw.edu.au/paper.cgi?ThEdu19.4](http://eptcs.web.cse.unsw.edu.au/paper.cgi?ThEdu19.4)

Integer and Polynomial Programs. This means something rather different from integer programming. The idea is that all variables are integer, but you still have a notion of time. Guarded transitions. It seems likely I could compile this into an integer program. Reify inequality conditions.

Cegar loop. Can run program to get a bunch of traces. Use traces and find a decreasing function on all traces.

[https://link.springer.com/chapter/10.1007/978-3-540-72788-0_33](https://link.springer.com/chapter/10.1007/978-3-540-72788-0_33) SAT solving for temrination checking. It does appear they slam nonlinear arithmetic problems into sat solver.s

Dependency pair? What is this. People seem to think it is very important

The control community has similar questions and similar yet different appproaches. They often want continuous state.

[https://github.com/blegat/SwitchOnSafety.jl](https://github.com/blegat/SwitchOnSafety.jl)

[https://github.com/blegat/HybridSystems.jl](https://github.com/blegat/HybridSystems.jl)

SpaceEx. Platzer's stuff.  JuliaReach

Barrier functions. I think the idea is the you put a function that is diverging at the region you're worried about. If you can guarantee that this function is not diverging. 

Sum of Squares certificates. Describing sets as sublevel sets.

The S-Procedure. I think this is that you can relax all inequalities using your assumptions $latex  f(x) >=0 implies g(x) >=0$ then $latex g(x) >= \lambda f(x)$ and $latex \lambda >= 0 $ is sufficient. Sometimes it is necessary I think.

Hybrid Systems. Piecewise affine systems. 

Reachability. We want to figure out how to rewrite one equation into another. Building an A* style lower bound distance could be quite helpful. A lower bound cost to get to some position. In terms of a control objective function S(x,x'), V(x,x'). In a small finite graph this could be computed. But suppose we didn't have enough flexibility. Finite graph, linear function of the features.

Ok. Some things. My concern about nonlinearity for multiply composed functions. 1. you might interpet some things differently (as fixed polynomial interpretation). Makes sense for constructors and data structures, where we have some reasonable suggestions. Looking at HEADs seems to matter a lot / give important over approximations of the behavior of the system. integer transition system. We can pattern match on fixed integers. f(x, 1) = yada.   f(x,y) -> f(y+1,x).  This we can do with guards.  f(x) | x > 7 -> g(x + 7).  f ~ 1 + a x + bx^2 + ... and so for g. Then f(x) >= g(x) + lam guard is lyapunov condition. We want struct inequality, that is the point of the integer nature of the system.  f(x) | x < 7 -> f(x**2 -  ) 

sum(n, acc) -> sum(n - 1, acc+n)

# Higher order rewriting

# Egraph
See 
- egraphs
- egglog

A form of nondestructive term rewriting
# Graph Rewriting

Compiling to Graph combinators
CHR is a ready to go (destructive) graph rewriting system

Terms are graphs. So are DAGs
Graphs may come in ported vs non ported forms. Are edges equivalent?

```prolog
%re
:- use_module(library(chr)).
:- initialization(main,main).
%:- chr_constraint s/0, s/1, s/2, i/0, i/1, k/0, k/1, k/2.

:- chr_constraint ap/3.

%flat(A + B,AB) <=> plus(A,B,C), flat(A), flat(B).
%flat(s(I,J)) <=> {gensym(X), s(I,J,)

main() :- print("hello"), term(s(i)).

term(ap(X,Y), Id) :- gensym(Id), term(X, XId), term(Y,YId), ap(XId, YId, Id).

ap(i, X, Id) <=> X = Id. %?
ap(k, X, KX), ap(KX, Y, KXY) <=> ?


/*
term(i, Id) :- gensym(Id), i(Id).
term(i(X), Id) :- gensym(Id), term(X, XId), i(XId, Id).
term(k, Id) :- gensym(Id), k(Id).
term(k(X), Id) :- gensym(Id), term(X, XId), k(XId, Id), 
term(k(X,Y), Id) :- gensym(Id), term(X, XId), term(Y, YId), k(XId, YId, Id). 
term(s, Id) :- gensym(Id), s(Id).
term(s(X), Id) :- gensym(Id), term(X, XId), s(XId, Id), 
term(s(X,Y), Id) :- gensym(Id), term(X, XId), term(Y, YId), s(XId, YId, Id). 



ite()
proj()
proj()
add(x,y,z)
*/
```

```

region(Id). % ~ blocks
cfg_edge(Id1,Id2). %  edges between blocks.
add(X,Y,Z) % dataflow edge
data_region(Z, R) % what region data calculation is in. optional
phi(X,Y,Z) % phi
ite(InReg, Data, ThenReg, ElseRegion, )


```


# Systems

## Maude

[Bool]
looks like maude has reflective reasoning

polymorphic operators. Huh

attributes
memo - memozie the result
otherwise attribute
print 

a matching equation

load
reduce in MYMOD 
sort A.
subsort A < B.

```
fmod MyNat is
    sort Nat .
    op zero : -> Nat .
    op s_ : Nat -> Nat .
    op _+_ : Nat Nat -> Nat .
    vars N M : Nat .
    eq zero + N = N .
    eq (s N) + M = s (N + M) .
endfm 
```

http://maude.cs.illinois.edu/w/index.php/Some_Papers_on_Maude_and_on_Rewriting_Logic papers

Maude formal environment
 coherence, temrination, 
 CETA library

 full maude is a seperate library thing?

 Debugger. That's interesting. Have it pause at each action?
 Ematching quantifier logging done right

 search command, that's cool.
 Takes pattern
 Search types. 

 red in STRING : "hello" + "world".

 nonexec eq

 ceq cmb commands for conditional equation and conditional membership
 We can easily enulate these.

(relation is-zero Zero)

I feel like catlab ought to be trivially encodable into this system
Brutal.

[Maude as a Library: An Efficient All-Purpose Programming Interface](https://link.springer.com/chapter/10.1007/978-3-031-12441-9_14)
https://github.com/fadoss/maude-bindings
https://fadoss.github.io/maude-bindings/

[Pure Type Systems in Rewriting Logic: Specifying Typed Higher-Order Languages in a First-Order Logical Framework](https://courses.engr.illinois.edu/cs522/sp2016/PureTypeSystemsInRewritingLogic.pdf)

frozenness. could frozen survive rebuilding? survive hash consing?
[20 years of rewriting logic](https://www.sciencedirect.com/science/article/pii/S1567832612000707)


[Programming and symbolic computation in Maude 2020](https://www.sciencedirect.com/science/article/am/pii/S2352220818301135)
[Theorem Proving for Maude Specifications Using Lean](https://link.springer.com/chapter/10.1007/978-3-031-17244-1_16)

https://fadoss.github.io/maude-bindings/
```python
import maude
maude.init()
m = maude.getModule('NAT')
t = m.parseTerm('2 * 3')
t.reduce()
print(t)x
```




[Context-sensitive Rewriting Lucas](https://www.researchgate.net/publication/341029369_Context-Sensitive_Rewriting)

There is a sense that we've already screwed up context even before we've done anything equational just because of hash consing. Hash consing makes trees into dags and now terms are not in unique contexts.
Context tagging is a way to undo or prevent work that hash consing does.
Maybe rebuilding and hash consing are a kind of rewriting step and therefore may need to be activated only in certain circumstances

TPDB format for termination includes context sensitive anotations
it affects termination, so that makes sense.


Memo - can mark terms as memo so they memoize the normal form they write to.

OPerator strategires - can mark which arguments must be evaluated before the total operator is evaluated. Functional modules only

Frozen - can mark whether whole subterms are frozen. Is this that different?

System modules vs functional modules. System modules specify concurrent rewrite systems. Functional modules are assumed church rosser and terminating

https://fadoss.github.io/strat-examples/

rewriting graphs can be model checked with respect to ltl formula. That's cool

http://maude.cs.illinois.edu/w/images/0/0f/BMgrt_2003.pdf proof system


http://maude.cs.uiuc.edu/maude1/tutorial/ tutorial for maude exampls


```
fmod A-GRAPH is
   sorts Edge Node .
   ops n1 n2 n3 n4 n5 : -> Node .
   ops a b c d e f : -> Edge .
   ops source target : Edge -> Node .

   eq source(a) = n1 .  eq target(a) = n2 .
   eq source(b) = n1 .  eq target(b) = n3 .
   eq source(c) = n3 .  eq target(c) = n4 .
   eq source(d) = n4 .  eq target(d) = n2 .
   eq source(e) = n2 .  eq target(e) = n5 .
   eq source(f) = n2 .  eq target(f) = n1 .
endfm
```

path example. Shows  the subsorting technique. In the manual they show some weird "kind" example.
```
fmod PATH is
   protecting NAT .
   protecting A-GRAPH .

   sorts Path Path? .
   subsorts Edge < Path < Path? .
   op _;_ : Path? Path? -> Path? [assoc] .
   ops source target : Path -> Node .
   op length : Path -> Nat .

   var E : Edge .
   var P : Path .

   cmb (E ; P) : Path if target(E) == source(P) .

   eq source(E ; P) = source(E) .
   eq target(P ; E) = target(E) .
   eq length(E) = s(0) .
   eq length(E ; P) = s(0) + length(P) .
endfm
```

This is cool. It's sequent proof search 

```
mod SEQUENT-RULES-PROP-LOG is
  protecting PROP-LOG .
  sort Configuration .
  subsort Sequent < Configuration .
  op empty : -> Configuration .
  op __ : Configuration Configuration -> Configuration
                                         [assoc comm id: empty] .
  vars R S : PropSet .
  vars P Q : Prop .

  rl [Identity] :        empty
                    => -----------
                       |- (P, ~ P) .

  rl [Cut] :           |- (R, P) |- (S, ~ P)
                    => ---------------------
                            |- (R, S) .

  rl [Weakening] :       |- R
                    => ---------
                       |- (R, P) .

  rl [Disjunction] :     |- (R, P, Q)
                    => ----------------
                       |- (R, (P \/ Q)) .

  rl [Conjunction] :   |- (R, P) |- (S, Q)
                    => -------------------
                       |- (R, S, (P /\ Q)) .

  rl [Truth] :          empty
                    => -------
                        |- tt .
endm
```

manual rule application https://github.com/fadoss/maude-bindings/blob/master/tests/python/apply.py

### Unification
```python
# https://github.com/fadoss/maude-bindings/blob/master/tests/python/unify.py
import maude
import itertools

maude.init(advise=False)

##### From Maude 3.1 manual, §13.4

maude.input('''fmod UNIFICATION-EX1 is
	protecting NAT .
	op f : Nat Nat -> Nat .
	op f : NzNat Nat -> NzNat .
	op f : Nat NzNat -> NzNat .
endfm''')

uex1 = maude.getModule('UNIFICATION-EX1')

uex1_t1 = uex1.parseTerm('f(X:Nat, Y:Nat) ^ B:NzNat')
uex1_t2 = uex1.parseTerm('A:NzNat ^ f(Y:Nat, Z:Nat)')

print('Unifiers for', uex1_t1, 'and', uex1_t2)

for unifier in uex1.unify([(uex1_t1, uex1_t2)]):
	print('Unifier', unifier)
	print('X =', unifier.find('X'))
	print('T =', unifier.find('T'))
	print('B:NzNat =', unifier.find('B', uex1.findSort('NzNat')))
	print('X:NzNat =', unifier.find('X', uex1.findSort('NzNat')))

	print('σ({}) = {}'.format(uex1_t1, unifier.instantiate(uex1_t1)))
	print('σ(3) =', unifier.instantiate(uex1.parseTerm('3')))
```

### Equation Search


```python
import maude

test_mod = """
  mod SEARCH is
    sort Num .
 
    op _+_ : Num Num -> Num .
    ops a b c d e f : -> Num .

    vars n m p  : Num .
    rl [lassoc] : (n + m) + p => n + (m + p) .
    rl [rassoc] : n + (m + p) => (n + m) + p .
    rl [comm] : n + m => m + n .

  endm"""
maude.init()
maude.input(test_mod)
mod = maude.getModule('SEARCH')

t = mod.parseTerm("(a + b) + c")
# t.search takes in parameters. I thnk the first one is no step, one step, *step
for (sol, subst, seq, steps) in t.search(5, mod.parseTerm("c + (b + n)"), depth=2):
    path = seq()
    print(subst) # n = a
    print(path) # an interleaved list of term and rule.

```

I do feel like there is way to hack cost into this. Define cost via computational equations... Hmm.

### Category

```python
import maude

test_mod = """
  fmod TESTMOD is
    sort Term .
    op foo : Term -> Term .
    ops x bar : -> Term .
    eq foo(x) = bar .
  endfm"""


test_mod = """
  fmod CATEGORY is
    sort Ob Morph .
    //subsort Morph < Morph? .
    op comp : Morph Morph ~> Morph .
    op id : Ob -> Morph .
    vars f g h .
    vars a b c .
    eq comp(comp(f,g), h) = comp(f, comp(g, h)) .
    eq comp(id(a),f) = f .
    eq comp(f, id(a)) = f .
    cmb comp(f,g) : Morph if type(f) = hom(A,B) /\ type(g) = hom(B,C) .

  endfm"""
maude.init()
maude.input(test_mod)
mod = maude.getModule('CATEGORY')

t = mod.parseTerm("id(a)")
print(t.reduce())
print(t)

```

"matching equations" are multipatterns rather than guards



## K
<https://dl.acm.org/doi/pdf/10.1145/3314221.3314601> instruction semantics for x86 in K
https://kframework.org/index.html
intepreter, compiler, formal prover thing
http://www.matching-logic.org/

https://kframework.org/faq/ 
Systems to compare to according to them
Redex, Maude, Spoofax, OTT, [Rascal](https://www.rascal-mpl.org/),  ATL and model driven

[popl : matching logic: foundations of K framework](https://www.youtube.com/watch?v=Awsv0BlJgbo&ab_channel=ACMSIGPLAN)

[Generating Proof Certificates for a Language-Agnostic Deductive Program Verifier](https://xchen.page/assets/pdf/LCT+23-paper.pdf) encpdong matchng loic into metamath?
# Other Systems

Pure
Obj
ASF+SDF https://homepages.cwi.nl/~paulk/publications/FASE99.html/node5.html (superseced by Stratego and Rascal)
ELAN (superseded by Tom http://tom.loria.fr/wiki/index.php/Main_Page ) 
mcrl2

Strategy
Stratgo

PLT redex - context sensitive rewriting?

https://link.springer.com/chapter/10.1007/978-3-030-17502-3_6 term rewriting engine competiton
rule engine competition benchamrks 
https://hal.inria.fr/hal-01883212/document
https://rec.gforge.inria.fr/ but it isn't responding
https://sourcesup.renater.fr/scm/viewvc.php/rec/

[dedukti term rewritng engine](https://drops.dagstuhl.de/opus/volltexte/2020/12357/pdf/LIPIcs-FSCD-2020-35.pdf)

[cafeobj](https://cafeobj.org/intro/en/)

https://redex.racket-lang.org/

[cafeobj](https://cafeobj.org/intro/en/)

 
RMT - rewriting modfulo theories https://profs.info.uaic.ro/~stefan.ciobaca/inriaparis2017/pres.pdf https://github.com/ciobaca/rmt/




# Misc
[Gershom Bazerman on "Homological Computations for Term Rewriting Systems" ](https://www.youtube.com/watch?v=WdawrT-6Qzk&ab_channel=PapersWeLove)

[rewritng modulo SMT and open system analysis](https://shemesh.larc.nasa.gov/fm/papers/wrla2014-draft.pdf)


[tools in term rewriting for education](https://arxiv.org/pdf/2002.12554.pdf)