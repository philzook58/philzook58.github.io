---
author: Philip Zucker
date: 2021-02-07 10:45:34+00:00
layout: post
title: Automated Propositional Sequent Proofs in Your Browser with Tau Prolog
tags: 
- prolog
- javascript
- proof
-  sequent
---

<script src="https://cdn.jsdelivr.net/npm/tau-prolog@0.3.0/modules/core.min.js"></script>
<script src="https://cdn.jsdelivr.net/npm/tau-prolog@0.3.0/modules/lists.js"></script>
<script src="https://cdn.jsdelivr.net/npm/tau-prolog@0.3.0/modules/js.js"></script>

<script>
function simple_query(file, query, cb){

    var session = pl.create(10000);
    var show = function(answer) {
        document.getElementById("output").innerHTML = session.format_answer(answer);
        console.log(
            session.format_answer(answer)
        )   ;
    };

    session.consult(file, {
    success: function() {
        // Query
        session.query(query, {
            success: function(goal) {
                // Answers
                session.answer({
                    success: function(answer) { show(answer); cb(answer); },
                    error:   function(err) { show(err);/* Uncaught error */console.log(session.format_answer(err)) },
                    fail:    function() { 
                        /* Fail */ 
                        document.getElementById("output").innerHTML = "Failed To Prove.";
                        document.getElementById("sequent").innerHTML = "";  
                        console.log("failure")},
                    limit:   function() { /* Limit exceeded */ console.log("limit exceeded")}
                })
            },
            error: function(err) { /* Error parsing goal */
            show(err);
            console.log(session.format_answer(err)) }
        });
    },
    error: function(err) { /* Error parsing program */  show(err) ;console.log(session.format_answer(err))  }
});
}

function pretty_formula(formula){
    if(formula.id == "~"){
        return `\\neg ${pretty_formula(formula.args[0])}`;
    }
    var op = null;
    switch(formula.id){
        case "&":
            op = "\\land"
            break;
        case "|":
            op = "\\lor"
            break;
        case "=>":
            op = "\\implies"
            break;

    }
    if(op != null){
        return `(${pretty_formula(formula.args[0])} ${op} ${pretty_formula(formula.args[1])})`;
    }
    return formula.toJavaScript();
}

function pretty_formula_no_paren(formula){
    if(formula.id == "~"){
        return `\\neg ${pretty_formula(formula.args[0])}`;
    }
    var op = null;
    switch(formula.id){
        case "&":
            op = "\\land"
            break;
        case "|":
            op = "\\lor"
            break;
        case "=>":
            op = "\\implies"
            break;

    }
    if(op != null){
        return `${pretty_formula(formula.args[0])} ${op} ${pretty_formula(formula.args[1])}`;
    }
    return formula.toJavaScript();
}


function pretty_list(l){
    switch(l.id){
        case ".":
            if(l.args[1].id == "[]"){
                return `${pretty_formula_no_paren(l.args[0])}`;
            }
            return `${pretty_formula_no_paren(l.args[0])} , ${pretty_list(l.args[1])}`;
        case "[]":
            return "";
    }

}

function pretty_sequent(seq){
   var hyps = seq.args[0];
   var concs = seq.args[1];
   return `${ pretty_list(hyps) } \\vdash ${ pretty_list(concs) }`
}

function pretty_proof(proof){
    console.log(proof);
    if (proof.id == "ax"){
            return `\\RightLabel{$ax$} \\AxiomC{} \\UnaryInfC{$ ${ pretty_sequent(proof.args[0] ) } $}`;
    }
    // Unary rules
    var label = null; 
    switch(proof.id){
        case "rimpl":
            label = "R\\implies";
            break;
        case "land":
            label = "L \\land";
            break;
        case "ror":
            label = "R \\lor"
            break; 
        case "lneg":
            label = "L \\neg"
            break; 
        case "rneg":
            label = "R \\neg"
            break;
       }
       if(label != null){
           return `${pretty_proof(proof.args[1])}
                     \\RightLabel{$ ${label} $} \\UnaryInfC{ $ ${pretty_sequent( proof.args[0] )} $ }`;
       }
       // Binary Rules
        var label = null; 
        switch(proof.id){
            case "rand":
                label = "R \\land";
                break;
            case "lor":
                label = "L \\lor";
                break;
            case "limpl":
                label = "L \\implies"
                break; 
       }
       if(label != null){
           return `${pretty_proof(proof.args[1])}
                   ${pretty_proof(proof.args[2])}
                     \\RightLabel{$ ${label} $} \\BinaryInfC{ $ ${pretty_sequent( proof.args[0] )} $ }`;
       }
}

    function prove(){
        //var query = `prove0(${document.getElementById("querybox").value}, P).`;
        var query = document.getElementById("querybox").value;
        console.log(query);
        simple_query(document.getElementById("prolog_code").value, 
           query , answer => {
              document.getElementById("sequent").innerHTML = `$$\\begin{prooftree}${pretty_proof(answer.links.Proof)}
                \\end{prooftree}$$`;
                MathJax.typeset()
 

           });
    }

function htmlDecode(input) {
  var doc = new DOMParser().parseFromString(input, "text/html");
  return doc.documentElement.textContent;
} 
function fillbox(e){
    console.log(e);
 document.getElementById("querybox").value = `prove0((${htmlDecode(e.innerHTML)} ), Proof).`;
}
//simple_query("fruit.pl","fruits_in([carrot, apple, banana, broccoli], X)." );
</script>

<b>Prolog Code:</b>
<textarea id="prolog_code" rows="20" style="width:100%"> 
% -----------------------------------------------------------------
% leanseq.pl - A sequent calculus prover implemented in Prolog
% -----------------------------------------------------------------
:- use_module(library(lists)).   

% operator definitions (TPTP syntax)

:- op( 500, fy, ~).     % negation
:- op(1000, xfy, &).    % conjunction
:- op(1100, xfy, '|').  % disjunction
:- op(1110, xfy, =>).   % implication
:- op( 500, fy, !).     % universal quantifier:  ![X]:
:- op( 500, fy, ?).     % existential quantifier:  ?[X]:
:- op( 500,xfy, :).

% -----------------------------------------------------------------
prove0(F, P) :- prove([] > [F], P).
% -----------------------------------------------------------------

% axiom
prove(G > D, ax(G > D, A)) :- member(A,G), member(A,D), !.

% conjunction
prove(G > D, land(G > D, P) ) :- select1( (A & B) ,G,G1), !,
                prove([A , B | G1] > D, P).

prove(G > D, rand(G > D, P1,P2)) :- select1( (A & B) ,D,D1), !,
                prove(G > [A|D1], P1), prove(G > [B|D1], P2).

% disjunction
prove(G > D, lor(G > D, P1,P2)) :- select1((A | B),G,G1), !,
                prove([A|G1] > D, P1), prove([B|G1] > D, P2).

prove(G > D, ror(G > D, P)) :- select1( (A | B),D,D1), !,
                prove(G > [A,B|D1], P ).

% implication
prove(G > D, limpl(G > D, P1,P2)) :- select1((A => B),G,G1), !,
                prove(G1 > [A|D], P1), prove([B|G1] > D, P2).

prove(G > D, rimpl(G > D, P)) :- select1((A => B),D,D1), !,
                prove([A|G] > [B|D1], P).

% negation
prove(G > D, lneg(G > D, P)) :- select1( ~A,G,G1), !,
                prove(G1 > [A|D], P).

prove(G > D, rneg(G > D, P)) :- select1(~A ,D,D1), !,
                prove([A|G] > D1, P).

% -----------------------------------------------------------------
select1(X,L,L1) :- append(L2,[X|L3],L), append(L2,L3,L1).
% -----------------------------------------------------------------

 </textarea>
<label for="querybox"> <b>Query:</b> </label>
<textarea id="querybox" style="width:100%" rows="2">prove0(((a & b) => a), Proof). </textarea>
<button onclick="prove()">Prove</button>


<div id="sequent"></div>
<label for="output"><b>Output:</b></label>
<div id="output"></div>

<b>Example Queries: </b>
- <a id="ex2" onclick="fillbox(this)" href="javascript:void(0);">((a => b) => a) => a</a> Peirce's Law
- <a id="ex2" onclick="fillbox(this)" href="javascript:void(0);">a | ~ a</a> 
- <a id="ex2" onclick="fillbox(this)" href="javascript:void(0);">(~(~a) => a)  & (a => ~(~a))</a> Double Negation
- <a id="ex2" onclick="fillbox(this)" href="javascript:void(0);"> ((a & b) => ~((~a \| ~b))) & (~((~a | ~b)) => (a & b)) </a> De Morgan's Law  
- <a id="ex2" onclick="fillbox(this)" href="javascript:void(0);">a & b | a & ~b | ~a & b | ~a & ~c</a>
- <a id="ex2" onclick="fillbox(this)" href="javascript:void(0);">(~b => f) & ((b & f) => ~i) & ((i | ~b) => ~f) => b</a>
- <a id="ex2" onclick="fillbox(this)" href="javascript:void(0);">(~b => f) & ((b & f) => ~i) & ((i | ~b) => ~f) => (i & f)</a>

### What is this?

The above is basically Jens Otten's prover from the "Build Your Own First-Order Prover" at CADE 2019 <http://jens-otten.de/tutorial_cade19/> in particular lecture 2.
I added a tracing parameter to it so that I can draw the sequent using [MathJax](https://www.mathjax.org/).
Note that my javascript is looking for a query variable called `Proof` in order to draw the output.

### What is a Proof Anyway?

Proofs are actions or things that convince you of something.

How's that for really nailing it down?

Some examples of stuff that might be considered "proof":

- A solution to a set of linear equations is proof that they can be solved.
- A dual vector is proof of optimality of a linear program.
- A convincing English paragraph is proof.
- Use of a cryptographic key can prove your identity.
- A trace of a complete search program that failed to find a solution is proof of its nonexistence.

There is a sense that for something to be a proof requires it to be relatively easy to check the proof.

A narrower view of proof is that proof is a pile of formal manipulations of syntax.
One thing that you can prove is the truth of a proposition combined using logical connectives. 

A [sequent](https://en.wikipedia.org/wiki/Sequent) is a structure that represents a partial state of a proof. It contains a breakdown of formula.
$ A,B,C,... \vdash D,E,F,...$. Spiritually a sequent represents the knowledge or [judgement](https://en.wikipedia.org/wiki/Judgment_(mathematical_logic)) that the conjunction of the antecedents implies one of the consequents, but a sequent could be just considered pure syntax, merely a dead data structure to hold a pile of meaningless symbols.

The sequent proof viewed from the bottom up is a stepwise breakdown of formula until they are trivially true.
From the top down it is the combination of simpler facts into more complicated ones.

It's all a very funny shell game. Somehow proofs take small steps that each feel so simple that they aren't doing anything and build up a statement that is non obvious.

# Prolog

[Prolog](https://www.metalevel.at/prolog) is neat. Here I'm using [Tau Prolog](http://tau-prolog.org/), which a prolog that is written in Javascript.
Prolog is roughly what you get when you add search and unification as primitive constructs in a language.

Prolog has multiple readings, which makes it pretty special.
In one reading Prolog formula are themselves statements of axioms of a particular form ([Horn clauses](https://en.wikipedia.org/wiki/Horn_clause)) that lends itself to a simple proof procedure.
It also has a fairly declarative reading as a nondeterminstic match statement that tries each match in turn.
Another interesting one is to consider `:-` to be the horizontal bar of an inference rule.

One model of the state of a prolog execution is as a sequent. The trace of prolog execution is is a sequent style proof. See [Nadathur and Miller](https://www.amazon.com/Programming-Higher-Order-Logic-Dale-Miller/dp/052187940X) or Frank Pfenning's [notes](http://www.cs.cmu.edu/~fp/courses/15317-f17/) for more

Notable tricks from the [Jens Otten](http://jens-otten.de/tutorial_cade19/) tutorial (which I highly recommend):
1. Invertible rules. Rules that are reversible (in what sense?) can be eagerly applied. Use cuts !
2. Using prolog variables and `copy_term`. Prolog variables may not work for higher order logic, but they do work for first order, since we're never substituting a bound variable inside another. Prolog variables are a different face . The trick to Keep some terms around is to include a Freevar list in copy term.
3. Skolemization
4. Iterative deepening. No surprise here. This is a pretty standard way of making prolog search complete.

For more on these tricks, it is worthwhile to examine the leanTAP paper <https://formal.iti.kit.edu/beckert/leantap/>.

There is a little bit of glue code in javascript to call the Tau Prolog solver. I used HTML textarea as input elements and sort of willy nilly grabbed from them.

```javascript
function simple_query(file, query, cb) {

    var session = pl.create(1000);
    var show = function (answer) {
        document.getElementById("output").innerHTML = session.format_answer(answer);
        console.log(
            session.format_answer(answer)
        );
    };

    session.consult(file, {
        success: function () {
            // Query
            session.query(query, {
                success: function (goal) {
                    // Answers
                    session.answer({
                        success: function (answer) { show(answer); cb(answer); },
                        error: show,
                        fail: function () {
                            document.getElementById("output").innerHTML = "failure";/* Fail */
                            console.log("failure")
                        },
                        limit: function () { /* Limit exceeded */ console.log("limit exceeded") }
                    })
                },
                error: show
            });
        },
        error: show
    });
}

function prove() {
    var query = document.getElementById("querybox").value;
    console.log(query);
    simple_query(document.getElementById("prolog_code").value,
        query, answer => {
            document.getElementById("sequent").innerHTML = `$$\\begin{prooftree}${pretty_proof(answer.links.Proof)}
                \\end{prooftree}$$`;
            MathJax.typeset()
        });
}
```

### The Pretty Printer

The pretty printer is straightforward and a little janky. I am using the bussproofs package that is included in mathjax to write out my proofs trees nice.
<http://docs.mathjax.org/en/latest/input/tex/extensions/bussproofs.html?highlight=bussproofs>


Bussproofs flatten the tree as a post order traversal, meaning you write a node after all it's children have been visited. It is most easily seen by examining this example. You can read more here <https://www.math.ucsd.edu/~sbuss/ResearchWeb/bussproofs/BussGuide2_Smith2012.pdf>.

```
\begin{prooftree}
\AxiomC{A}
\UnaryInfC{B}
\AxiomC{C}
\BinaryInfC{D}
\AxiomC{E}
\AxiomC{F}
\BinaryInfC{G}
\UnaryInfC{H}
\BinaryInfC{J}
\end{prooftree}
```
$$
\begin{prooftree}
\AxiomC{A}
\UnaryInfC{B}
\AxiomC{C}
\BinaryInfC{D}
\AxiomC{E}
\AxiomC{F}
\BinaryInfC{G}
\UnaryInfC{H}
\BinaryInfC{J}
\end{prooftree}
$$

Traversing through returned Tau Prolog objects is pretty straightforward. There are `id` fields that hold the name of the functor and `args` is an array holds the children. I figured it out via judicious use `console.log` as Tau Prolog doesn't have the most documentation I've ever seen.

```javascript

function pretty_formula(formula) {
    if (formula.id == "~") {
        return `\\neg ${pretty_formula(formula.args[0])}`;
    }
    var op = null;
    switch (formula.id) {
        case "&":
            op = "\\land"
            break;
        case "|":
            op = "\\lor"
            break;
        case "=>":
            op = "\\implies"
            break;

    }
    if (op != null) {
        return `${pretty_formula(formula.args[0])} ${op} ${pretty_formula(formula.args[1])}`;
    }

    return formula.toJavaScript();
}

function pretty_list(l) {
    switch (l.id) {
        case ".":
            if (l.args[1].id == "[]") {
                return `${pretty_formula(l.args[0])}`;
            }
            return `${pretty_formula(l.args[0])} , ${pretty_list(l.args[1])}`;
        case "[]":
            return "";
    }

}

function pretty_sequent(seq) {
    var hyps = seq.args[0];
    var concs = seq.args[1];
    return `${pretty_list(hyps)} \\vdash ${pretty_list(concs)}`
}

function pretty_proof(proof) {
    if (proof.id == "ax") {
        return `\\RightLabel{$ax$} \\AxiomC{} \\UnaryInfC{$ ${pretty_sequent(proof.args[0])} $}`;
    }
    // Unary rules
    var label = null;
    switch (proof.id) {
        case "rimpl":
            label = "R\\implies";
            break;
        case "land":
            label = "L \\land";
            break;
        case "ror":
            label = "R \\lor"
            break;
        case "lneg":
            label = "L \\neg"
            break;
        case "rneg":
            label = "R \\neg"
            break;
    }
    if (label != null) {
        return `${pretty_proof(proof.args[1])}
                     \\RightLabel{$ ${label} $} \\UnaryInfC{ $ ${pretty_sequent(proof.args[0])} $ }`;
    }
    // Binary Rules
    var label = null;
    switch (proof.id) {
        case "rand":
            label = "R \\land";
            break;
        case "lor":
            label = "L \\lor";
            break;
        case "limp":
            label = "L \\implies"
            break;
    }
    if (label != null) {
        return `${pretty_proof(proof.args[1])}
                   ${pretty_proof(proof.args[2])}
                     \\RightLabel{$ ${label} $} \\BinaryInfC{ $ ${pretty_sequent(proof.args[0])} $ }`;
    }
}
```

You can also look at the source of this page to see everything in context. <https://raw.githubusercontent.com/philzook58/philzook58.github.io/master/_posts/2021-02-07-javascript-automated-proving.md>
It's just all slammed together.

### Bits and Bobbles

- I should also adapt the first order logic sequent prover. I haven't understood it yet and it's a bit more complicated.
- It would be interesting to take the Tableau and Connection provers from Otten's lecture 3 and use maybe D3 to visualize those proofs.
- It would be cool to make an interactive prover like Jape or [Logitext](http://logitext.mit.edu/main). MathJax has the ability to give ids to elements, so they could be made clickable with callbacks. <http://docs.mathjax.org/en/latest/input/tex/extensions/html.html> I wonder if this is how Logitext does it?
- [ELPI](https://github.com/LPCIC/elpi/) is a Lambda Prolog (prolog with lambda terms) implementation is written in ocaml, and can be compiled to javascript. Someone even wrote javascript bindings to it, although I'm not sure what state they are in.  <https://github.com/voodoos/elpi-js> . Lambda leantap <https://www.csc.liv.ac.uk/research/techreports/tr2003/ulcs-03-017.ps>. Sounds like one can avoid the weirdness of prolog encoding of binding forms.
- Chalk <https://rust-lang.github.io/chalk/book/what_is_chalk.html>
- MiniKanren <http://minikanren.org/>
- These prolog theorem provers are not really competitive with the big boys. <http://www.tptp.org/CASC/J10/WWWFiles/DivisionSummary1.html> Still one wonders if they are good for specialized problems since flexible.
- Models of typeclass resolution, type inference, etc in prolog. Model the algebra of programming in prolog (point free realtional catamorphisms etc ). Categorical Logic.

### Links

- <http://jens-otten.de/tutorial_cade19/>
- <http://tau-prolog.org/>
- <https://pbrown.me/blog/hello-tau-prolog/>
- <https://github.com/RBornat/jape>
- <https://www.metalevel.at/prolog/theoremproving>
- <https://github.com/bobatkey/interactive-natural-deduction>
- <https://bentnib.org/docs/natural-deduction.html>
- <https://personal.cis.strath.ac.uk/robert.atkey/cs208/dancer-paradox/>
- <http://logitext.mit.edu/main>
- <http://www.netlib.org/problem-set/pelletier/full.predicate/problems> Pelletier problems
- <http://okmij.org/ftp/Prolog/index.html>
