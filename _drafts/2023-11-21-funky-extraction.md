
Roughly, extraction is taking compact pile of stuff in an egraph an gettng a term out. Ultimately, ther systems are ingesting terms, so for applications you need this.

Part of the appeal of the egg approach is that you can extract _good_ terms.

In this post, I don't want to talk about how to best solve for good terms, but instead some interesting varietions on the expressivity or semantics of extraction.

For an extraction elgorithm, there is a question
`(Egraph, Term) -> (Cost, Term)`

A different fascinating possibility raised by _ is considerng the extraction problem that wants to produce a set of equatons equivalent to an egraph (a set of equations that should you add those terms and union them in a frsh egraph, you get back the same egraph). This is a methodology for finding a "good" set of equations rather than a single good term.
`Egraph -> [(Term, Term)]`
They phrased this as a form of quantifier elimination.

It is a reasonable problem that you may insert a pile of equations and receive a "solution".
Solutions are often equations with an isolated left hand side, and a right hand side that only contains certain entities.
These are definitions.

Scoping. Egraphs and egglog have a pretty bad story here.
You can use egglog as a theorem prover, but you have to skolemize and herbrandize yourself. This situation is reminiscent of a resolution solver, where the basic operational mechanims does not really support quantifiers either, so clausal form is produced in a preprocessing pass.

Termination

The most naive mode of extraction is a term model. In this model, we pay for a term every time we use it.

It is often closer to the truth to consider a DAG model, in which you only need to pay for a term once and may reuse it again and again.

There is also a spectrum between them.

Cycle breaking.
In the PEG paper using egraphs as an IR, they produced egraphs that are not produceable from a process of adding terms and term rewriting rules. These egraphs were not "well founded" in some sense that it would be interesting to have a nice definition of. There is intrinsic knot tying.

The simplest example is an egraph with a single looping enode and eclass. It perhaps represents the truly infinite term `f(f(f(f(f(f(...))))))`

```mermaid
f self loop.
```

If you run an iterative greedy dynamic programming approach, it does not terminate or terminates with infnite cost. If you start trying to get a term out, that will also not terminate because there is no term to be had in there.

You can kind of produce egraphs like this if you allow yourself access to a raw fresh-eid, or if you make a temporary nonsense placeholder to tie the knot with, whch you subsequently set the cost to infinity.

While PEGs are couched in the language and greek letters remiscent of SSA-like compiler IRs, to my mind basically it is an equational theory of coinductive streams, akin to what you find in Haskell. The contents of the streams are the symbolic state of the system.

# Examples Where Methods Help

Greedy did so well that  started to be convinced that it was actual optimal or guaranteed some fraction of optimal. Taking big benchmarks where a priori no one knows the optimal answer made this unclear.
It is not the case. You can design some simple examples where the greedy heuristic is arbitrarily bad.

# Methods

The extraction gym is a good place to look to see some ideas people have had.
Brute Force.

Greedy.

ZDD
ILP
MaxSAT
Answer Set Programming

One I really like is from the Kestrel talk, monte carlo optimization. It is a somewhat sad fact of life that exact optimizatin methods are actually not _that_ useful. This is because 1. they are often computationally expensive 2. heuristics are often pretty good and very fast 2. they can require mangled modelling to fit into thir language 3. Optimizing beyond the fidelity of the model to reality is pointless and in fact often counterproductive. This is a form of overfitting, the bane of machine learning.
Figuring out an accurate model of a cpu is very very hard.
Profile guided optimization.
So just run the program! Maybe weight your sampling a bit towards things you think are good.
