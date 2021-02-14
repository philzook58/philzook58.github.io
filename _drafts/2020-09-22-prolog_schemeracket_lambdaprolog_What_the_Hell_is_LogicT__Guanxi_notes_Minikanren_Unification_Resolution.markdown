---
author: philzook58
comments: true
date: 2020-09-22 15:37:08+00:00
layout: post
link: https://www.philipzucker.com/?p=1865
published: false
slug: prolog, scheme,racket, lambdaprolog, What the Hell is LogicT / Guanxi notes
  Minikanren, Unification, Resolution
title: prolog, scheme,racket, lambdaprolog, What the Hell is LogicT / Guanxi notes
  Minikanren, Unification, Resolution
wordpress_id: 1865
---


Hmm. Gauntlet thrown.
Byrd is not sure how prolog can? do this stuff.
https://www.youtube.com/watch?v=aS8oj2GXras&feature=youtu.be&ab_channel=LecturesbyProf.EadesatAU

meta interpeter, sure.

Hmm. Could one do barliman style in lambda prolog?
F, ex1, ex2, ex3.
2012 quine ppaper
2017 barliman paper

Tree automa, lvar, language for fixpoints.
Not depth first, not breadth first,
coniductive logic programming UT Dallas
Abstract Interpretation ~ tabling. What does that mean?

nada Amin
lambda kanren
defeasible logic

proof checker running backwards



Scheme workshop



https://git.sr.ht/~sforman/Prolog-Junkyard/tree/master/miscellaneous/itc.pl interval tree clocks in prolog
https://www.metalevel.at/trs/ knuth bendix completion
https://arxiv.org/abs/1706.00231 auto differentiating uysing constraint handking rules

http://adam.chlipala.net/papers/MakamICFP18/MakamICFP18.pdf prototpying functional language using higher order logic programing makam
chlipala
https://www.tweag.io/blog/2019-11-28-PCF-makam-spec/

Egraphs in prolog
Unification variables give native union find data strcuture
Hash consing - ??
equal( (t, E1), (t2,E2) :- E1 = E2. % union find joining

Great. But then we need to possibly union find parents

t(x,y) ====> t(E1,E2)

equal(  t1, t2  ) :- lookup( t1 )

file:///home/philip/Downloads/ODonnell1987_Chapter_Term-rewritingImplementationOf.pdf

https://core.ac.uk/download/pdf/81972151.pdf Logic programming with equations.

Eqlog - goguen and mesegaer?

assert_equal(EGraph,   ,EGraph') :- lookup(t1, E1), lookup(t2, E2), E1 = E2, EGraph' = EGraph
assert_eqyal(  ) :- lookup(t1, E1), lookup(t2, E2)

rebuild(EGraph, EGraph' ) :- 

rebuild(EGraph) :- EGraph = (  , Map )

To miss a parent inference isn't wrong, it's just wasteful

If we do no hash consing, we do have to store every known term.
We also need a map from Eclasses back to terms don't we?

What if we broke apart. are association lists so bad?
f(g(y)) ===> [  f(G) => F , g(Y) => G, y => Y ]

Or we could use the HEADS as keys in assoc. and then assoc list the leftovers.
This isunder the assumptyiong that variables

== for search
[ == , ]

We may want to prune duplicates occasionally
If we interweave 

Can we even achieve apttern matching without an index from ENodes => terms?
Yessss.....?
Given a pattern ( EClass, g(f(A)) )
We can look in g/1 for Eclass on the right hand side.
For those matches, we build a subproblem of matching the pieces of the left hand size ENodes.





With tabling?
Tabling gives us some kind of memoization

equal?(Egraph, t1,t2) :- lookup(EGraph, t1, E1), lookup(EGraph, t2, E2).
equal?(arg1(  ) :- eqwal?(args1, args2), assert_equal(EGraph, t1, t2)

Stratified prolog predciates. This euqation paper mentions this 
and this tabling thing mentions it https://www.swi-prolog.org/pldoc/man?section=tabling-non-termination


Datalog and program analysis
https://www2.cs.sfu.ca/CourseCentral/721/jim/DatalogPaper.pdf - What you always wanted to know about datalog
http://rightingcode.org/tutorials/popl20/ popl 2020 - reasoning tools using llvm and z3
Z3 has a datalog style reasoning engine in it

First you need to get a program as a mapping


The Chase - get existentials in the head. Wisnesky says somethign to do with jkabn extensions and lawvere theory
What was up with the notion of quantifiers as adjoints anyway?
Maybe also some kind of completion?
Datalog +-
Formulog
Bap KB as datalog
What 

Typeclasses vs Canonical Structures. I don't get it.
Could I make a model? Maybe in prolog?
Diamond problem
Inheritance.
What are typeclasses? "Kind of like prolog"
Things are incompatible for some reason?
Canonical structures add unification hints?
https://hal.inria.fr/hal-00816703v1/document canonical structures ofr the working coq user


So what is the synctatic condition that precludes search?
1. nonoverlapping 

Would it be more interesting to just 
What am I understanding here?

Canonical structures was suggesting that some kind of inconstency would manifest.
Maybe lambda prolog gets us closer. We can have existential variables and such.

extensible unification


nat === (carrier nat_abGrp) :- 
A === A.


nat == carrier(Eq) :- Eq == natEq.
carrier(Eq,nat).



nonunifiable(L) :- all( /= , L ).


% haskell has no backtracking
% every case has a cut.
eq(tup()) :- !.
eq(tup(A,B)) :- !, eq(A), eq(B)

% 

eq(int, prim__equal_int).
eq(tup(A,B), lambda( x, case( x, tup(a,b) => bool_and( apply(EqualA, a) , apply(EqualB, b )  )    )  )  ) :- 
      eq(A, EqualA), eq(B, EqualB).
eq(tup(A,B), comp(and, par(EqualA,EqualB)))


eq(int).
eq()
eq(tup(A,B)) :- eq(A), eq(B).


ord(bool).
ord().

functor( maybe )
functor(compose(F,G)) := functor(F), functor(G)

traversable :-

% superclass
class(ord(A)) :- call(ord, A), class(eq(A))



"diamonds appear evertwhere. See pullbacks" ~ Hale


Transcribing rules to prolog and coq.
In Coq the cookbook is that you make an inductive. One constrctor per rule.
If you call eauto, coq will perform prolog style backchaining search. See Chlipala
You could write these as functions rather than as 
The data type is the proof structure.

Prolog is the same thing. It's less imposing than coq though.
You make predicates and :- for each condition.
Prolog has built in nondtermisnion and unification.


Tying rules in prolog.
I did the point-free simply typed lambda calculus
type(fst, tup(A,B), A).


type(Gamma |- plus(A,B) : nat ) :- 
          type(Gamma |- A : nat), type(Gamma |- B : nat)
type(Gamma, lam(X, Body) |- fun(A,B )) :- type() , type( [X | Gamma]


http://www.coli.uni-saarland.de/projects/milca/esslli/comsem.pdf computational semantics. some interesting material here
https://samples.jbpub.com/9780763772062/PrologLabBook09.pdf - prolog experiment in discretem mathemtiacs logic and computatilbitly



They start with defining a set of atoms like

var(x).
var(y).

forall(x, stupid(x)).


https://www.youtube.com/watch?v=RwBiHLoQ3E4&ab_channel=PapersWeLove niko matsakis - lambda prolog

https://rust-lang.github.io/chalk/book/recursive.html chalk. harrop formula


The Otten sequent calculus prover is very similar to a meta circular intepreter for prolog

Horn clauses (or harrop formula) 



Lambda-mu calculus and prolog. Focusing is relevant.
Prolog has an imperative reading


Executing the Algebra of Programming

type(fst, prod(A,B) -> A ).
type(snd, prod(A,B) -> B ).
type(id, A -> A).

interp(fst, tup(A,B), A ).
interp(snd,  tup(A,B), B).
interp(id, A , A).
interp(fan(F,G), A, tup(B,C)) := interp( F, A, B) , interp(G, B, C).  
interp(comp(F,G), A, C ) :- interp( F, A, B ), interp(G, B, C).
interp(conv(F), A, B) :- interp(F, B, A).
interp(cata(F) , fix(A) , C )  :-  interp(map(cata(F)), A, B) ,  interp(F, B, C)

% map instance for ListF
interp(map(F), cons(A,B) , cons(A,B2) ) :- interp(F, B, B2).
interp(map(F), nil, nil).

% in constrast to map instance for list
interp(map(F), [], []).
interp(map(F), [X | XS], [Y | YS]  ) :- interp(F, X, Y), interp(map(F), XS, YS).





% convert to listf form
listf([], nil).
listf([A | XS ], cons(A,fix(L))  ) :- listf(XS, L).


Different style


cata(F, fix(A), C) :- map(cata(F), A, B), call(F, B, C).
fst(pair(A,B), A).

comp(F, G, A, B) :- call() , call()


% define what it means to be a functional relation
functional( fst, fst).
functional( snd, snd).
function(  )

% prolog is database stuff ~ relation algebra. It makes perfect sense.


interp( map )

Converting prolog to abstract machine form
step( Stack Result ) :-


oprolog veriffication

Warrne and Maier 1988 textboook
proplog - propsitional goals only. 
datalog - constants only
prolog - functional symbols

% tail recursive formulations
factorial(N,F) :- factorial(0, N,1,F)
factorial(I,N,T,F) :- I < N, I1 is I+1, T1 is T * I1, factorial(I1, N, T1,F)
factorial(N,N,F,F).

hitchikers guide to prolog machine
https://drops.dagstuhl.de/opus/volltexte/2018/8453/pdf/OASIcs-ICLP-2017-10.pdf


ref a
ref b

https://formal.iti.kit.edu/beckert/leantap/leantap.html Beckert posegga leantap
https://link.springer.com/chapter/10.1007%2F3-540-36377-7_6 metacircular abstarct interpretation in prolog
https://www.metalevel.at/acomip/

Pfenning constructive logic course http://www.cs.cmu.edu/~fp/courses/15317-f17/schedule.html
Programs as proof search
He considers the prolog predictaes as the judgements themeselves
As compared to considering the pile of predicates as entedcedents of a sequent
Bottom up search ius forward reasoning, top down is backward reasonining
bidrectional type checking - https://arxiv.org/pdf/1908.05839.pdf



Prolog semantics -
Since prolog can not terminate you can take that denotational semantics perspective.
https://www.swi-prolog.org/pldoc/man?section=WFS well founded semantics. - True/False/unknown
https://en.wikipedia.org/wiki/Well-founded_semantics
http://www.cse.unsw.edu.au/~cs4415/2010/resources/gelder91wellfounded.pdf
http://dai.fmph.uniba.sk/~sefranek/links/FixPointSurvey.pdf  fixpoitn semantics for logic programming a survey. melvin fitting
Melvin fitting has a number of interesting bokos http://melvinfitting.org/

So prolog already has belnap bools in it. 


What does it look like to mix prolog with exact reals?



Modes and determinism annotations.

Kowalski - hgistory of prolog https://www.researchgate.net/publication/277670164_History_of_Logic_Programming



tabling - 
Tabling is some kind of memoization.
It is connected to bottom up strategies
swi prolog https://www.swi-prolog.org/pldoc/man?section=tabling
https://www.metalevel.at/prolog/memoization
https://biblio.ugent.be/publication/6880648/file/6885145.pdf tabling as a library with delimited control
https://www.cambridge.org/core/journals/theory-and-practice-of-logic-programming/article/abs/delimited-continuations-for-prolog/DD08147828169E26212DFAF743C8A9EB delimitted continuations for prolog
https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.294.9440&rep=rep1&type=pdf XSB extending prolog with tabled logic programming. XSB prolog is the most advanced tabling implementation (still? maybe that is old information)
https://github.com/SWI-Prolog/tabled-prolog-book warren wrote a book draft
https://www3.cs.stonybrook.edu/~warren/xsbbook/book.html ok This may not be being finished anytime soon
Tabled typeclass resolution


http://www.covingtoninnovations.com/mc/plcoding.pdf - coding guidelines for prolog

https://swi-prolog.discourse.group/t/algebra-in-prolog/1849 - algerba in prolog
https://github.com/maths/PRESS prolog equation solving system


scryer prolog - a rust based implemnentation . https://github.com/mthom/scryer-prolog
Interesting links
Precise garbage collection in Prolog 
"Can Logic Programming Execute as Fast as Imperative Programming?" - Peter van Roy
indexing dif/2 https://arxiv.org/abs/1607.01590 calls for if_ predicate
debray allocator

https://wiki.nikitavoloboev.xyz/programming-languages/prolog notes

https://mercurylang.org/documentation/documentation.html mercury

Names:
Kowalski
schrijver
Nuemerekl
Markus triska
Wielemaker
Warren
Miller
Nadathur
melivn fitting

https://www.metalevel.at/prolog/theoremproving 
presburger and resolution
https://www.youtube.com/watch?v=b2Px7cu2a68&feature=youtu.be&ab_channel=ThePowerofProlog term rewriting in prolog

https://dl.acm.org/doi/book/10.1145/3191315
Declarative Logic Programming: Theory, Systems, and ApplicationsSeptember 2018
Has another WAM tutorial in it

So


prolog modes

https://www.metalevel.at/prolog/attributedvariables attributed variables

https://sicstus.sics.se/sicstus/docs/latest4/pdf/sicstus.pdf sicstus prolog manual


Exact reals. The semantics already has this three valued logic flavor

```
partition([X,Y]).
partition([X,Y]) :- partition([[X, X+Y / 2]]).
partition([[X,Y]) :- partition( [X+Y/2 , Y  ]).

interval(X), stuff.


sqrt()

```

Using prolog multiple answer streams is kind of like relying on haskell laziness.
It's this intrinsic lANGUAGE construct being used as a streaming datatpe
Unclear if wise. Fast but inflexible and unclear. Too clever for own good.

clpq
clpr

delmittied dontinuation. The contiuation is a goal stack.
But is the continuation also catching choice point stack?


homoiconic. Term syntax is identical to 


Maier and Warren 

T_p, the immediate conseqeunce operator. Applying one round of prolog/datalog/ etc rules

Proplog


SMT-log
Datafun - a fiunctional datalog https://www.cl.cam.ac.uk/~nk480/datafun.pdf https://www.youtube.com/watch?v=gC295d3V9gE
datalog - stephenel diehl https://www.stephendiehl.com/posts/exotic04.html
uZ - datalog in Z3
souffle
doup


What are appli8cations of datalog
program analysis. That points to analysis tutorial

Datalog ~ polynomial time in some sense. 
 So application wise, it can be fixed point computations
 Or we can encode

 send more money
 num(0) num(1)
 num(2)
 adder(  )

 https://sites.google.com/site/pydatalog/Online-datalog-tutorial
 nqueens - they unroll it significantly.

Some examples
http://cse.unl.edu/~riedesel/pub/cse413/des/doc/manualDES.pdf

 ok farmer goat. As a path search basicaly

state(goat, foxm, chienbk, ) :- 



Parsing a grammar. This is an odd one. Encode positions of string in database.
t(1,a,2).
t(2,b,3).
t(3,a,4).
t(4,b,5).
t(5,a,6).
a(F,L) :- t(F,a,L).
a(F,L) :- a(F,M), t(M,b,L).
a(F,L) :- a(F,M), t(M,a,L).
DES> a(1,6)
{
 a(1,6)
}
Info: 1 tuple computed.

Games? 

Domain modeling with datalog
https://www.youtube.com/watch?v=oo-7mN9WXTw&ab_channel=%23pivorakLvivRubyMeetUp

https://github.com/ptarau/TypesAndProofs
More theorem provers

binprolog - analog of CPS. Add a new parameter to every predicate

LD resolution

monoid of clauses - unfolding
bin(A :- BBBB) = (A>C :- BBBB>C)


2020/9
Propagators.

Kmett. The Art of the Propagator https://dspace.mit.edu/bitstream/handle/1721.1/44215/MIT-CSAIL-TR-2009-002.pdf?sequence=1&isAllowed=y 

The gecode manual [https://www.gecode.org/doc-latest/MPG.pdf](https://www.gecode.org/doc-latest/MPG.pdf)

Adding constraints or smt. I have a seperate store for them (in the state)? explicit probe annotations to check still satisfiable.

9/1/20

I was looking at prolog again. Jesus nothing changes.

What are the good programs. The art of prolog has an open access link

Difference lists are cool. They really are similar ot hughes lists. Or al ist that keeps a pointer to it's end

Using it for theorem proving is cool. Where are those examples? The lambda prolog book has some exmaples. There is a propsitional satisfiabilioty prover in art of prolog. Propositional solver in powr of prolog [https://www.metalevel.at/prolog/theoremproving](https://www.metalevel.at/prolog/theoremproving) [http://vidal-rosset.net/g4i_prover.html](http://vidal-rosset.net/g4i_prover.html)   http://jens-otten.de/tutorial_cade19/slides/prover_tutorial_CADE19_2.pdf

[http://tca.github.io/veneer/examples/editor.html](http://tca.github.io/veneer/examples/editor.html) minikanren examples. 

[http://io.livecode.ch/](http://io.livecode.ch/) more minikanren examples [https://www.youtube.com/watch?v=0FwIwewHC3o](https://www.youtube.com/watch?v=0FwIwewHC3o) implementing microkanren 

https://www.youtube.com/watch?v=0FwIwewHC3o

nomial logic programming [https://arxiv.org/pdf/cs/0609062.pdf](https://arxiv.org/pdf/cs/0609062.pdf) alphaprolog. Chris mentioned this nominal thing as nother way of dealing with binders

Datalog - souffle.  Reading gorup paper [https://arxiv.org/pdf/1207.5384.pdf](https://arxiv.org/pdf/1207.5384.pdf). Sttratification. relations indexed on program point/ abstract state of program point. Interval analysis encoded in binary to datalog?

425/20 I was playing with prolog recently. Pretty cool 

What is the deal with scheme and racket? i just don't have the  revelation.

[http://home.pipeline.com/~hbaker1/CheneyMTA.html](http://home.pipeline.com/~hbaker1/CheneyMTA.html)

Lisp in easy pieces

[http://cs.brown.edu/~sk/Publications/Books/ProgLangs/2007-04-26/](http://cs.brown.edu/~sk/Publications/Books/ProgLangs/2007-04-26/)

[https://schemers.org/](https://schemers.org/)

I was looking at disjoint set data structures again [https://en.wikipedia.org/wiki/Disjoint-set_data_structure#cite_note-Conchon2007-9](https://en.wikipedia.org/wiki/Disjoint-set_data_structure#cite_note-Conchon2007-9)

Kmett's latest propgator talk was mentioning using group actions somehow in unification? [https://www.youtube.com/watch?v=s2dknG7KryQ](https://www.youtube.com/watch?v=s2dknG7KryQ)

george wilson - https://www.youtube.com/watch?v=nY1BCv3xn24 intutition for propagators.

[http://hackage.haskell.org/package/discrimination-0.3](http://hackage.haskell.org/package/discrimination-0.3) What the hell is this? Fritz Henglein. 

[http://conway.rutgers.edu/~ccshan/wiki/blog/posts/WordNumbers1/](http://conway.rutgers.edu/~ccshan/wiki/blog/posts/WordNumbers1/)

https://www.reddit.com/r/haskell/comments/a9yze4/is_there_an_arraylike_data_structure_which_gives/

interesting comments  

[https://www.lri.fr/~filliatr/puf/](https://www.lri.fr/~filliatr/puf/) a coq formalization of a persistent union find data structure.  They use persistent arrays, which do some kind of rebalancing operation. 

Persistent data structures. Wassup with them?

## 2019

Combine LogicT with an OSQP monad for branch and bound

[http://overtond.blogspot.com/2008/07/pre.html](http://overtond.blogspot.com/2008/07/pre.html)

[https://github.com/dmoverton/finite-domain](https://github.com/dmoverton/finite-domain)

[https://blog.plover.com/prog/haskell/monad-search.html](https://blog.plover.com/prog/haskell/monad-search.html)

[https://www.schoolofhaskell.com/user/chowells79/even-more-money](https://www.schoolofhaskell.com/user/chowells79/even-more-money)

[https://blog.jle.im/entry/unique-sample-drawing-searches-with-list-and-statet](https://blog.jle.im/entry/unique-sample-drawing-searches-with-list-and-statet)

Select Monad

Branch and Bound

Ed kmett is up to funny business

[https://www.youtube.com/watch?v=ISNYPKiE0YU&t=916s](https://www.youtube.com/watch?v=ISNYPKiE0YU&t=916s)

Propagators

[https://www.sciencedirect.com/science/article/pii/S1571066105805444](https://www.sciencedirect.com/science/article/pii/S1571066105805444)

Typed logical variables in haskell by Claesson and Ljundogjgklds

[https://people.seas.harvard.edu/~pbuiras/publications/KeyMonadHaskell2016.pdf](https://people.seas.harvard.edu/~pbuiras/publications/KeyMonadHaskell2016.pdf)

Also by claesson, the key monad paper. 

[http://www.cse.chalmers.se/~koen/](http://www.cse.chalmers.se/~koen/)

Interesting guy. He is coqauthor with hughes on quickcheck.

Atze van der Ploeg is both Key monad paper and reflection without remorse. They have an FRP paper that sounds interesting

He metnioend a number of interesting things. He's doing very reference heavy code? Kanren. 

He mentoins intension vs extensional equality. Judgemental eqaulity is the one inside the type checker. Is it ~ ? And intwnsional equality is the one within the language itself, that is :~: . Extensional. nuPRL starts with an untyped lambda calculus and then you teahc the system typing derivations? What is nuPRL's deal

Union-find algortihm - as part of unification?

nerualkanren, synquid. Two program synthetsis projects. Synquid uses liquid typing

Oleg Shen paper using efficient charing for logic programming

[https://www-ps.informatik.uni-kiel.de/~sebf/data/pub/icfp09.pdf](https://www-ps.informatik.uni-kiel.de/~sebf/data/pub/icfp09.pdf)

[http://sebfisch.github.io/explicit-sharing/](http://sebfisch.github.io/explicit-sharing/)

Maybe sebastein fischer is the name I should assicuate more storngly?

[https://sebfisch.github.io/research/](https://sebfisch.github.io/research/)

The Curry language. Haskell + logic. Egison has weirdo patterns too. Multiple patterns can match? Non-linear pattern require. Realted to view patterns? view patterns are a weirod syntax. realted to guard patterns. DOn't need to introduce intermediate names

[https://people.eecs.berkeley.edu/~necula/autded/lecture15-tactics.pdf](https://people.eecs.berkeley.edu/~necula/autded/lecture15-tactics.pdf)

View patterns might be a way of getting something like the Agda .x syntax, where something is forced to be something by unification?

[https://gitlab.haskell.org/ghc/ghc/wikis/view-patterns#Relatedwork](https://gitlab.haskell.org/ghc/ghc/wikis/view-patterns#Relatedwork)

Kmett mentions a "octagonal" domain. What the hell is he talkiing about. He also moentions interval and polyhedral which makes more sense

https://www-apr.lip6.fr/~mine/publi/article-mine-HOSC06.pdf

Huh. Interesting. It is in between power of polyhedral and interval. allows sums/differences of two variables. I think I've heard this called difference logic. This paper also mentions galois connections. Galois connections are studied in the context of abstract interpetation?

https://arxiv.org/pdf/1807.08711.pdf 

Using Agda and galois connections. Interestign example of sets of even and odd numbers.

This other paper does an interesting thing of defining division in terms of a glaois connection. Might we also get a good definition of fractions that way? a fraction t ~ m/n is a "number" such that forall z. x <= y   -> x * t * n <= y * m?  There is an notion of negative numbers, fractions, etc as reified weirdo operations that can't be solved yet. Hmm. Yeah, This jives with galois theory doesn't it. That book I was reading was talking about field extensions. Or number systems being invented to make more equations solvable. The reals make ? solvable. fractions make division solvable. Complex makes roots solvable. finite field extensions make simple algerbaic equations solvable. 

[https://www.sciencedirect.com/science/article/pii/S1567832612000525](https://www.sciencedirect.com/science/article/pii/S1567832612000525)

% -----------------------------------------------------------------
% leanseq.pl - A sequent calculus prover implemented in Prolog
% -----------------------------------------------------------------

% operator definitions (TPTP syntax)

:- op( 500, fy, ~).     % negation
:- op(1000, xfy, &).    % conjunction
:- op(1100, xfy, '|').  % disjunction
:- op(1110, xfy, =>).   % implication
:- op( 500, fy, !).     % universal quantifier:  ![X]:
:- op( 500, fy, ?).     % existential quantifier:  ?[X]:
:- op( 500,xfy, :).

% -----------------------------------------------------------------
prove0(F) :- prove([] > [F]).
% -----------------------------------------------------------------

Oliveira, that same guy as the Search monad and some other thingds

I suppose perhaps there is something similar happening in functional programming. to make recrsuively defined functions solvable, you need to extemnd the language with a Y-combinator or some of fixed point operator.

Interval airthemteic in a theorem prover. That is a way of getting sets. Min and Max. Interesting

This is also a pleasant by Backhouse

http://www.cs.nott.ac.uk/~psarb2/G53PAL/FPandGC.pdf

indirect equality

m=n ===  forall k. k <= m <=> k <= n

Galois connection between convex hulls of integer points? There is a sequence of abstractions for integer programming. You can turn dimension by dimension into integer so there are 2^D different domains to talk about. And there is this grid of connections that forms a lattice itself? Like the top is the completely R^D, and the bottom is Z^D. Using these connections is the branch and bound procedure. 

Floor and Ceil are also galois connections. Maybe also round? I had been thinking in terms of ibjects being individual numbers, not convex sets of numbers. Convex sets does tie in much better to categorical thinking

http://www.cs.tau.ac.il/~msagiv/courses/asv/absint-1.pdf

An interesting paper tutorial on galois connections. V cool.

monotone functions between are like natural tranfromations?

One place used dup as the adjunction to max.

There may be more to galois connections than adjunctions, since they are assuming a meet and join operation. Some interesting doncturctions like the porduct of galois connections.

[https://www.youtube.com/watch?v=KxeHGcbh-4c](https://www.youtube.com/watch?v=KxeHGcbh-4c)  

minikanren is strongly unification based. it is using search for the unification map. In simplest form [UniMap]

[https://github.com/JeffreyBenjaminBrown/learn-logict](https://github.com/JeffreyBenjaminBrown/learn-logict)

https://www.msully.net/blog/2015/02/26/microkanren-%CE%BCkanren-in-haskell/

[https://gup.ub.gu.se/file/207634](https://gup.ub.gu.se/file/207634) logic typed variable claesson

[http://dev.stephendiehl.com/fun/006_hindley_milner.html#unification](http://dev.stephendiehl.com/fun/006_hindley_milner.html#unification) unification.

[http://webyrd.net/arithm/arithm.pdf](http://webyrd.net/arithm/arithm.pdf)

[https://ro-che.info/articles/2017-06-17-generic-unification](https://ro-che.info/articles/2017-06-17-generic-unification) unification-fd . 

[https://winterkoninkje.dreamwidth.org/100478.html](https://winterkoninkje.dreamwidth.org/100478.html)

unification-fd inserts itself in the same position Fix does.

Lattices. Subsumption lattice for unufication. More and less general partial order. meet and join. top and bottom

## Notes from 2017 -Resolution and unification

So I was learning about about minikanren. There are some videos online. Minikanren is a logic programming language (like Prolog) that embeds easily into other languages because it has a small core.

Logic programming is weird mainly (partially) because you define relations rather than functions. Relations do not have a input output relationship like functions do. In a sense they are like functions where you get to choose which thing is output and which things are input. Pretty crazy.

The most obvious way to do this to me is to make every function a bag of functions. Just write one function for every possible choice of output variable. These functions may need to be non-deterministic, outputting multiple possibilities, for example for y = x^2 gives x = +sqrt(y) or -sqrt(y). However, this isn't really how logic programs are written. Instead they deduce how to use a relation as a function.

I find most intro to prolog stuff off putting, talking about socrates(man), when that is not a problem I have ever given a crap about.

Resolution is the classical logic version of function composition.

a-> b and b->c can be combined easily into a function a-> c.

Implication in classical logic is weird. It translates to

a->b  ====> (not a)  or b

When a is true, b has to be true. When a is false, b can be true or false.

For the statement a implies b to be true then it needs to evaluate to false only when a is true and b is false

not  (a and (not b))

using De Morgan's law you can distribute nots turning ands into ors.

Then that becomes

(not a) or b.

If you have

((not a) or b) and ((not b) or c)

it does not matter what b is really because either b or not b will be false

so this is equivalent to

(not a) or c

since at least one has to be true to make the whole expression true

Unification

Predicate logic allows propositions to depend on variables. Think Prolog.

A simple question given two expressions is whether there are values of the variables that make the expressions equal.

I do this in my head sometimes when I'm looking a a parametric haskell type.

The type variables need to be matched up with two different expressions.

Sometimes this can be too hard to do in my head, especially when the type variables end up being functions.  So there is need for an algorithmic procedure. I mean, also because you want a computer to do it.

First off, let's suppose we have the two expressions in tree form.

Nodes can be Or, And, Predicates, Not.

We'll want them in some canonical form too so that we don't get tripped up by the commutativity or distributivity of Boolean operators

We need to collect up a bucket of deduced equivalences as we go down the trees of the two expressions. Whenever we hit a variable, we check if we have a substitution in our bucket. If so, replace it. If not, we put into our equivalences that variable is equal to whatever the other expression has in that place. When we hit something that trips us up, we announce failure and the expressions couldn't be unified.

The prolog algorithm is roughly guess a pair of terms in the goal (the executing state) and knowledge base (the code base) that will unify. Try to unify them. If they do, then use resolution to get rid of those terms.

Like what if we reflected into Eisenberg's Stitch? Or what was Weirich's thing? People have been talking about intrinsically typed system-F lately.

