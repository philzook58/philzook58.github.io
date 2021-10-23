---
author: philzook58
comments: true
date: 2020-09-20 03:24:45+00:00
layout: post
link: https://www.philipzucker.com/?p=2677
published: false
slug: Partial Evaluation Tricks
title: Partial Evaluation Tricks
wordpress_id: 2677
---

https://github.com/metaocaml/metaocaml-bibliography 

https://wiki.hh.se/wg211/index.php/Main_Page program generation working group


https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.81.8435&rep=rep1&type=pdf pattern matching via partial evaluation

https://stackoverflow.com/questions/46614561/implementing-partial-evaluation-in-swi-prolog
The clause/2 predicate  is like a macro?
https://github.com/leuschel/logen
https://github.com/leuschel/ecce
https://stackoverflow.com/questions/35261361/prolog-generate-unique-symbol gensym
is gensym sufficient for making eigenvariables like lambdaprolog?
interp(Env, lam(B), lam(B)). % this is wrong.
interp(Env, app(F,X), R) :- interp( Env, F, lam(B)), interp(Env, X, X'), interp([ X' | Env], B, R )
interp([H | T], z, H).
interp([H | T], s(X), R) :- interp(T, X, R). % nah this ain't right. we need to do raising and lowering.

interp(Env, var(X), R) :- lookup(X, Env, R).
interp(Env, lam(X,B), lam(X,B)). % X not in Env?
interp(Env, app(F,X), R) :- interp( Env, F, lam(V,B)), interp(Env, X, X1), gensym(var, V), interp([ V-X1 | Env], B, R )

http://okmij.org/ftp/Prolog/index.html#lambda-calc - he implements a pure copy_term using gensym basically


Staged logic programming is kind of like CLP. CLP collects up constraints to be solved later (at future stage).
Instead staged logic programming is collecting up constraints in the original unification language.
Can I not make new clauses? To fully do this at compile time requires that the compile time query terminates. Otherwise i need to jump between compile and runtime (which is how clp works)

interp(plus(x,y,z), q)

What I'd expect staged minikanren to look like is a minikanren that outputs minikanren clauses.
We should be able to break down at compile time minikanren programs to base unifications.
But what about things that bind to multiple results? I guess we could insert conde for as many results as there are? Or we could maintain the substitutions structure across 

 (conde (== q 3) (== q 4)) `(appendo ,q ) ==> (conde (appendo 3) (appendo 4)) 

In prolog, building code doesn't feel crazy.


staged minikkanren https://www.twitch.tv/videos/1010688093?t=01h34m31s lisp symposium 2021
unified approach solving seven programming prbs icfp 2017
collasping towers of interpeters
Pink - stage polymorphic evaluator
quoted unification. pushes it off to later stage
augment state of minikanren with code? (delayed goals?)
partial reduction - logic programs. Partial evaluation of logic programs?
decompiler from a compiler? Huh.

reflective towers? What and why?
3-lisp 
Brown - Wand 
Blond - Danvy
Black - Asai
Pink

errors bring up to a meta level.
(base-eval)
(exit 'hello)
EM - eval at metalevel.
metacontinuation is an inifnite stream of state
Each state represents "registers" of a level.
(env, cont)
Lazy so we only build levels as we need them.


https://www.youtube.com/watch?v=SrKj4hYic5A&ab_channel=StrangeLoopConference
metalevels


cogen in six lines
https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.51.7918&rep=rep1&type=pdf

What if you defunctionalize and apply the trick to the stack? going to machine and back sounds reminscent of supercompiling.
Interplay of Positive and negative.

fun x -> (4 + (x + 7))
fun x k -> 

data Stack = ToDORight Expr | 
             LeftDone Int
             | Ret



"The Trick" is  eta expansion.

Supercompilation is not like super optimizers. Super means supervise apparently. The idea I think is that you execute the program on a symbolic ish machine view all the states, and recompile that to a new program.
States themselves are kind of expressions.
Refal is very reminsicent of abstract machines and the classical logic thing, with focuses and the importance of patterns.
It is also hyper bizarre

Another possible thing is that it is partial evaluation + memoization.
Is this distinct from common subexpression collection?

Can I supercompile addition expressions? Boolean expressions?

The "trick" they call splitters and things. 

For addition, perhaps it could be nice to split unknown x as 0 or not zero. Not always useful.


https://stackoverflow.com/questions/9067545/what-is-supercompilation
supercopliation is partial evaluation plus other stuff.
https://www.microsoft.com/en-us/research/wp-content/uploads/2016/07/supercomp-by-eval.pdf?from=https%3A%2F%2Fresearch.microsoft.com%2Fen-us%2Fum%2Fpeople%2Fsimonpj%2Fpapers%2Fsupercompilation%2Fsupercomp-by-eval.pdf supercompliatiob by example - bolingbroke and peyton jones


partial evaluation as evaluation inference rules with some removed or staging them. It does feel kind of like the bidirectional thing. Take a system and enhance it or duplicate it with extra annotations.

https://twitter.com/codydroux/status/1382019718224211975?s=20 cody and andras kovacs.

Commutation rule / conversion
CSP/orthogonality

Type polarity is realted to PE? neagtive positive. Push pull streams strymonas. "The Trick" is an eta expansion. Maybe if cubical does something good to coinductives, then it does something nice to PE?

https://twitter.com/jjcarett2/status/1381727925314142212?s=20
carette and kmett takliong about something
Online PE considered fast? Clearly i don't understand online vs offline
Chu constructions. Something about linear logic
Supercompilation = +ve -ve info flowe. Huh that actually brings up google results
https://www.reddit.com/r/compsci/comments/1e7cs1/supercompilation_by_evaluation_pdf/
https://themonadreader.files.wordpress.com/2014/04/super-final.pdf
http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.51.881 a positive supercompier
https://link.springer.com/article/10.1007/BF03037260  Program transformation system based on generalized partial computation Yoshihiko Futamura, Zenjiro Konishi & Robert Glück 
Hmm. Carette has either a strange model of terminology of
http://www.xoft.ru/~anklimov/papers/1993.Occam's.Razor.in.Metacompuation.pdf occams razor in metacomputation. "Propagation of inequations" according to carette
"If you avoid packing unpacking online PE is fast" What could this be referring to? finally tagless?


Something I'm been wondering about is the relationship of symbolic execution and partial evaluation. The opaqueness of future stage code is very similar to the opaqueness of a symbolic variable. It feels like the techniques of staged metaprogramming should be useful for writing more easily verifiable code.
Loop unrolling as a staged metaprogamming thing vs unrolling for BMC
Known compile time structure unpacking
Abtract analysis boosting
CPS and ?
What if I used the ASP techniques to build parser combinators that are easily verified via Z3. In python?


But I dunno. Staged metaprogrmming example 1 is loop unrolling if the bounds of the loop are known at compile time. This is also of course what one wants to do for symbolic execution

Example 2 is sturcture unpacking if the structure is known at compile time (removing record construction destruction overhead). This is also what you want to do for symbolic evluation

Case splitting (The trick) feels like path exploration. Where you make the queries along a particular path

The First Set Last set stuff is the familiar idea of using an abstract intepretation result to boost an SMT query

CPS trasnformation and let lifting = ????


Staged minikanren
Rosette



Virtual machine compiling?


Of course you want to simplify as much at compile time

Partial evaluation in Julia.

Partial evaluation is when you have a program and you supply a portion of it's arguments ahead of time.
In light of this information, there may be significant simplifications that can occur, although because of still missing arguments, the computation cannot be completely computed. The unknown input variables are blockers of computation.
You could have some arbitrary rewriting simplication system do this, but it is more principled to have this partial evaluator take a form that is systematically connected to a standard evaluator.

- Loop unrolling - If you know the bounds o the loop ahead of time
- constexpr - 
- Pattern matching - Unroll the pattern into 
- 


One way this might happen (and it is illuminating) is to consider a deeply embedded DSL where you explicitly represent the AST of your language of interest as a data type.
However there is a shallower approach available when your language offers the appropriate compile-time computation facilities.
Julia has a lisp-y quasiquoting macro system that is really neat.

If you like o think of it this way, it is that analog of string interpolation.
```julia
:( 1 +  $(2 + 3) )
# :(1 + 5)
```

#### The Power Example


## Tricks

### The Trick
A big trick is that one can convert a runtime value into a compile time value by guarding under a runtime check.
The nonobvious step in refining a program to be partially evaluatable is that you may have to insert extra runtime checks than you would ordinarily use but the payoff is that the information you gain at compile time is worth the cost of the runtime check.
In other words it is case splitting

One simple example of this is special case unrolling small n.

```julia
function foo(x::Char)
  if x > 9
  else
end


```

```julia
function foo(x::Expr)
    :(if $foo == 1
    
    
    )
end

```



### Let lifting

### CPS



###






Carette generative programming course
https://www.cas.mcmaster.ca/~carette/CAS761/F2018/index.html
https://www.cas.mcmaster.ca/~carette/CAS761/F2020/index.html



Mjolnir





https://mpickering.github.io/papers/parsley-icfp.pdf

I have more stuff in the coq metaocaml post https://www.philipzucker.com/metaocaml-style-partial-evaluation-in-coq/

- https://github.com/stedolan/ppx_stage
- https://github.com/thierry-martinez/metapp
- https://github.com/thierry-martinez/metaquot https://ppxlib.readthedocs.io/en/latest/ppx-for-plugin-authors.html#metaquot
- Nada Amin course https://namin.seas.harvard.edu/publications  https://www.cl.cam.ac.uk/teaching/1819/Metaprog/materials.html
- Yallop https://www.cl.cam.ac.uk/~jdy22/ https://www.cl.cam.ac.uk/~jdy22/papers/certified-optimisation-of-stream-operations-using-heterogeneous-staging.pdf

http://wry.me/~darius/writings/peval/ - a hacker's intro to partial evaluation

tutorial notes on partial evaluation - consel and danvy 93 https://www.researchgate.net/profile/Charles_Consel/publication/2810226_Tutorial_Notes_on_Partial_Evaluation/links/54ba866e0cf24e50e9403382/Tutorial-Notes-on-Partial-Evaluation.pdf
From rmpf thesis
Partial Evaluation of Pattern Matching in Strings dnavy 89
Fast partial evaluation of pattern matching in strings danvy 03
Implementing Multistage Languages Using ASTs, Gensym, and Reflection - xavier taha

Shifting the stage: staging with delimited control
Closing the stage: from staged code to typed closures


Quine invented qasuiquotation in the 40s
https://3e8.org/pub/scheme/doc/Quasiquotation%20in%20Lisp%20(Bawden).pdf Quasiquotation bawden

https://www.cs.purdue.edu/homes/rompf/papers/ofenbeck-gpce17.pdf staing for generic programming in space and time rompg

ones, N.D., Gomard, C.K., Sestoft, P.: Partial Evaluation and Automatic Program Generation. International Series in Computer Science 
https://cs.stackexchange.com/questions/2869/what-are-staged-functions-conceptually

Generative Programming" by Czarnecki and Eisenecke

- 
7/4/20

Partial evaluation has some tricks

Basically

  1. Do CPS
  2. Specialize branching

Partial evluation of AExp, BExp

staged-fun. And this is already available in a friendly Haskell compiler near you.

It really helps to have a system where you can see the result of the partial evaluation. You may be surprisied by what you see. Coq is decent.  But you can also get the dump of 

The optimizations that partial evaluation achieves are also I suspect the optimization achieved by the folklore CPS transformation for making faster code. Part of the optimization an optimzing compiler _is_ partial evaluation.

Some of the things that people like to do in the type system can also (perhaps even more naturally) be done with a partial evaluation system. 

In systems like Ocaml and Haskell, the types are fully erased at runtime, so that any type level computation becomes compile time computation.

One thing that is done is to convert something into a special type by checking that it obeys teh predicate. Like taking [a] -> Maybe (Vec 10 a) needs to confirm that the length of the list is in fact 10. Then that fact is recorded for further use, inviting possible optimizations. But we can do basically the same thing. is_length_10 : code [a] -> code bool. And type vec = (int * code [a])

Like what about a  (code int, Z3.expr) as a kind of refined int type. 

Coq is from one persepctive a kind of janky restrictive Ocaml with steroidal metaprogramming capabilities. 

We can use this to perform rewrite rules. It isn't quite as straightforward as you might hope. When you perform rewrites in a proof, I'm not so clear how to get the new forms reflected back. But there is at least one trick, you can use an existential variable and then unify it at the end.

The canonical fusion is `map f . map g = map (f . g)` It avoids two passes over the same structure.  An even better fusion is build/fold fusion. If you build up a big structre just to consume it immediately, this can often be fused into 

Here are some examples using rewrite rules to fuse

    
    <code>Lemma idea2: { q : list nat -> list nat | forall l,  map S (map S (map S l)) = q l}.
    Proof. eexists. intros. Print map_map.
           (* assert  (map S (map S (map S l)) = map S (map S (map S l))). *)
           pose (map S (map S (map S l))) as opaque_lhs .
           assert (opaque_lhs =  map S (map S (map S l))).
           reflexivity. 
           rewrite map_map in H. rewrite map_map in H.  unfold opaque_lhs in H. rewrite H. auto. Defined.
    Print idea2.</code>

Recursion schemes in coq.

MetaOcaml in coq. A similar trick can be. Coq by it's nature doesn't appear to be so super concerened about efficiency differences in implementations. Things that are equal under. MetaOcaml allows controlled inlining and other partial evaluations at compile time in order to create more efficient programs that remain clearly written.

MetaCoq. Why have I not even downloaded it?

[https://youtu.be/fJ5HHvWZWfc?t=7584](https://youtu.be/fJ5HHvWZWfc?t=7584) Modal analysis of metaprogramming

This reminds of well-typed ASTs. Sometimes those well typed asts have an explicit slot for contexts. In some sense, an introspective well typed metaprogramming langueg should reflect the surface language into a well typed ast. Pure opaqueness is a cop out. It is acceptable but not desired.

box letbox vs box unbox

