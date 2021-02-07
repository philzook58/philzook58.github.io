
https://en.wikipedia.org/wiki/Categorical_logic
Categorical Logic
A |- B

cut = composition
axiom = identity

proof terms = categorical expressions




adjoints - 
Baez student youtube video
Awodey and Bauer notes

There seem to be more layers though



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