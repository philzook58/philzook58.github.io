---
layout: post
title: Term Rewriting
---


https://www.stephendiehl.com/posts/exotic02.html 

Term rewriting and all that

confluence
church rosser
termination

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

[K vs. Coq as Language Verification Frameworks](https://runtimeverification.com/blog/k-vs-coq-as-language-verification-frameworks-part-1-of-3/)
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

# String rewriting systems
Word problem
Monoid presentation

# Knuth Bendix

# Termination
https://github.com/TermCOMP/TPDB termination problem database

https://termination-portal.org/wiki/Termination_Portal
Termcomp 2022 https://termination-portal.org/wiki/Termination_Competition_2022

# Higher order rewriting


# Misc
[Gershom Bazerman on "Homological Computations for Term Rewriting Systems" ](https://www.youtube.com/watch?v=WdawrT-6Qzk&ab_channel=PapersWeLove)

[rewritng modulo SMT and open system analysis](https://shemesh.larc.nasa.gov/fm/papers/wrla2014-draft.pdf)

