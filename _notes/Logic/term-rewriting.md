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
print(t)
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



## K
<https://dl.acm.org/doi/pdf/10.1145/3314221.3314601> instruction semantics for x86 in K
https://kframework.org/index.html
intepreter, compiler, formal prover thing
http://www.matching-logic.org/

https://kframework.org/faq/ 
Systems to compare to according to them
Redex, Maude, Spoofax, OTT, [Rascal](https://www.rascal-mpl.org/),  ATL and model driven

[popl : matching logic: foundations of K framework](https://www.youtube.com/watch?v=Awsv0BlJgbo&ab_channel=ACMSIGPLAN)

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

