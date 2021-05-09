---
date: 2021-02-07
layout: post
title: Sequent Category Stuff
---


Sequents include the signature. This is very important.
https://ncatlab.org/nlab/show/sequent+calculus They suggest the context can be made implciit in certain settings.
In proppsiytional logic, the context is empty. In single sorted FOL, you can gather up the constants by inspecting the propositions. At least a minimal number of constatsd. You can weaken both the cedent and the context. In Coq, The area before the turnstile plays both roles. Mashing distinct things together becasue you can is not always good. Type theorists should be aware of this as that is sort of a complaint of set theory

http://www.lix.polytechnique.fr/~dale/pisa14/lecture2.pdf
Hmm Identity rules are compose and id.



https://en.wikipedia.org/wiki/Categorical_logic
Categorical Logic
A |- B

cut = composition
axiom = identity

proof terms = categorical expressions

Am I overthinking it with regards to quantifiers = adjoint?
Maybe we should have explicit named variables.

A(x) |- Q(x)

Ex x, A(x) |-

```
prove( G > D, comp(F,G) ) :- 

```

http://therisingsea.org/notes/ch2018-lecture9.pdf

$$ \begin{prooftree}
\AxiomC{$ f : A \vdash_V B $}
\AxiomC{$ g : B \vdash_V C $}
\RightLabel{cut}
\BinaryInfC{ $  f \cdot g : A \vdash_V C  $  }
\end{prooftree}
$$

$$ \begin{prooftree}
\AxiomC{}
\RightLabel{ax}
\UnaryInfC{ $  id_A : A \vdash_V A  $  }
\end{prooftree}
$$

$$ \begin{prooftree}
\AxiomC{$  f : A \vdash_V B  $}
\RightLabel{weak var}
\UnaryInfC{ $  f : A \vdash_{V \cup \{x\}} B  $  }
\end{prooftree}
$$

Substitution axiom

$$ \begin{prooftree}
\AxiomC{}
\RightLabel{terminal}
\UnaryInfC{ $  unit(A) : A \vdash_{V} \top  $  }
\end{prooftree}
$$

$$ \begin{prooftree}
\AxiomC{}
\RightLabel{initial}
\UnaryInfC{ $  absurd(A) : \bot \vdash_{V} A  $  }
\end{prooftree}
$$

Should I signify meta variables somehow?

Different variables sets are different categories. We could define perhaps auto upcasting of some kind.
This is unsatisfying in how arbitrary it seems and clearly we want to make statements about categories regardless of variable sets



The terms are just another way of formatting the proof tree in some sense. If you look at the syntax of the term, you can determine exactly which rule is about to applied.


http://therisingsea.org/notes/ch2018-lecture13.pdf
Weakening is unprojection
The interpetation of Sets
A(x,y) |- B(x,y) means B is subset A
The free variables are a different category? The sequnt should be labeled by them
A |-x B is different from A |- B or  \Sig ; A |- B
In prolog prover, we do explicitly track free vars.
The various quantifiers forall x , exists x only make sense in particular categroies and are typed
such that they remove 
forall x_(xyz->yz) might be a way of denoting this exact quantifier.

Weakening W_x_(yz->xyz). W_x is a schema

Morphisms aren't sequents. They are proofs. We compose proofs by applying a cut rule.
This is the same as f . g = \x -> let y = f(x) in g(y)



From above we can see that all these thigns must be intimately related. There is a paremtric polymorphism at play.
It is just like the STLC vs System F. STLC terms like id= \x -> x are homogenous in some sense that we can see.
Things like forall x and W_x are schema for producing concrete things.

How can you compose arrows of different free variables? Via

We need explcit weakening of free variable steps.

http://therisingsea.org/post/seminar-ch/
Oh man what a rush.
I feel like i get the quantifier adjoint thing now.

Is the next step figuring out how one would do set theory?
Raw First order logic is only set theory in its wekeast sense.

cody says empty right hand side of sequent + normal form on the left becomes reolustion proving.
Makes sense as a refutation proof.
Put into a normal form

Every combo of multi/single/empty on left or right gives something interesting

suingle single - categorical
multi multi - seqeunt
multi single - natural
empty single - hilbert
empty multi - 
What about single left, multi right?


Could be fun to:
First order logic
Intuitionistic logic (with lambda terms checkbox)
tactical proving. I could take in a tactic script
[split, case(H), ] in prolog syntax.


typeclass resolution - returns proof terms, 
Each instance is named.

natEq for exmaple
Eq a, Eq b => pairEq : Eq (a,b)
Expands to
Eq((A,B), pairEq(DictA,DictB)) :- Eq(A, DictA), Eq(B, DictB)

We could do a runtime typeclass mechanism.


Bart Jacobs cateogrical loigc
Scott and lambek

Logical frameworks
Isabelle is a logical framework?

Jacobs:
objects
(s1,s2) s.t. s1 <= s2
([ 0..10 if even ], 0..10  )
forgetful functor to set, take second eleent

morphisms = u from x to y defined over the larger set s.t. forall x  x(i) implies (y(u(i)))
Fixing I - subsets of i. Morphisms are inlcusion functions.

Yes Jon Stirling mentioned variables as baby sheaves. I would like to understnad the baby version
The category of variables = sets of variables. Functions between them
[x => y, z => y] .
A map from variables to predicates is a functor. 


adjoints - 
Baez student youtube video
Awodey and Bauer notes

There seem to be more layers though


http://angg.twu.net/LATEX/2021excuse.pdf edward ochs- category theory an excuse to learn type theory
https://news.ycombinator.com/item?id=26203257 HN occmments on native type theory. 
https://www.cl.cam.ac.uk/~amp12/papers/catl/catl.pdf Pitts categrocal logic
Bart Jacobs book


The sequent calculus as an intermediate language makes a related but distinct choice.
There is no non determinism
Computation = Proof Check.
See Paul Downing tutorial.

Type checking = Proof Check.

Hilbert systems ~ Combinator calculi

Prolog trace and gtrace

What is a sequent?
A sequent is a judgment but implication is a proposition.
Sequents are not nested. Implications are.
Sequents are more meta.
In a complete proof they represent belief - pfenning's down
In an incomplete proof they represent queries - pfenning's up

Sequents may not make sense outside of a proof tree.



See leanTAP paper.


What is prolog really?
Horn clauses?
A pile of axiomns  forall x, exists(y) B(x,y) /\ C /\ D => A(x)

A goal: exists x, A(x) /\ B /\ /\

Resolution perspective  -> CNF

Linear logic has nice proof search properties. Somehow encodes state search?


Traditional prolog and this lmabda prolog community have a different pserpewctive on what prolog means.

Automated Theorem Proving by Pfenning has a connection between his "verifcations" and birectional type checking

A up = verified
A down = A can be used.


Inverse method?
Focusing. Changes the machines slightly. One formula is in focus.
"Uniform proof"
"Abstract Logic Programming"

Tableau - It _is_ sequqnt calculus in disguise somehow.

Negation normal form



Inference Rules - what are they? We draw things with horizontal bars. There are things above and below the bars.
In one sense the turnstile, implication and inference rule are all similar things. Perhaps operating and different "layers". The inference rules are more "meta" than implication.

A decidable inference rule is one such that there exists a function
above_live -> below_line -> Bool

A Prolog predicate
rule( above_line, below_line ).

A more general inference rule mighjt not be decidable and might initiate a possibly non terminating proof search in order to find . I have heard of undecidable judgements coming up in the context of higher order unification 

Relations can be rearranged in all sorts of ways though.
It is tempting to have

below_line -> [above_line]
backward reasoning
type checking

or
above_line -> [below_line]
Forward reasoning, type inference

or even perhaps a mixed case
(some_above, some_below) -> [ (some_above, some_below)]




tactics
th below_line -> ( prop_above_line , prf_above_line ->  prf_below_line )
Huh. Accidental lens.

Implkemeting inference rules in stnadard ML http://www.cs.cmu.edu/~fp/courses/15317-f17/recitations/recitation7.pdf sterling

Turnstile as an infix relation on syntax.


https://news.ycombinator.com/item?id=24091096 Guy Steele videos.

If I tried to explain ther "eamnning" of arithemtic by explaining to to operationalize it in a computer, I would be doing you a disservice. And yet I'm tempted to do so for inference rules






Jape


I could make a sequent calculus in javascript.

make a codepen if one wants to edit it

Use MathJax 
http://docs.mathjax.org/en/latest/input/tex/extensions/html.html to set clickable id
http://docs.mathjax.org/en/latest/input/tex/extensions/bussproofs.html bussproofs


If we could use tauprolog, we could maybe automate proofs in interesting ways.

 
Lambda Mu calculs



A category of single argument sequents.
Point-free programming requires you mantain your context implicilty.
Categorical combinators tend to have some inefficiencies. Maybe even intrinsic inefficiencies
A single hyphothesis, so it do not need to be named
It is in this form that logic clearly

Because there is only 1 right hand sand, it is natural deduction
Proof terms are point free expressions


Objects are formula. Morphisms are sequents.
Horizontal bars are categorical constructins which you may posit or not.
You can say its cartesian closed, but it doesn't have to be




https://tiarkrompf.github.io/notes/?/dependent-types/


var fun = f => {tag : "fun", "f" : f  }
var app = (f,x) => {tag : "app", f : f, x : x}

var app = (f,x) => {
    if(f.tag == "fun") return f.f(x)
    else return {tag : "app", f : f, x : x}
}

function eval(x , env) { // denote
    switch(x.tag){
        case "Var":
            return env[x.x]
        case "Lam":
            return z => { 
                 env[x.x] = z // but make immutable.
                 eval( z.body, env ) }
        case "App":
            return eval(x.f , env)( eval(x.x,env) )
        
    }
}

function reify(x) {
   if (x isinstance Function){
       v = fresh()
       return lam(v,  reify(x(v)) )
   }
   else{
       return x
   }
}