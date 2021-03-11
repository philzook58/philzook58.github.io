---
author: philzook58
date: 2021-02-06
layout: post
title: Auto prover 2
---

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



Should I try to figure out the tableau prover and build a d3 visualiziation for it?

Should I attempt to use js_of_ocaml for something interesting?


https://cdibbs.github.io/folproof/ interactive fol prover

https://github.com/jyp/FOL minimal fol prover
https://www.d3-graph-gallery.com/graph/network_basic.html

Could we make an interactive prover using these seeds?
Leave reason for each step inferred sometimes.
Discharge into external z3 call


# Sequents, Matrices, and Tableaus

What is the correspondence here?
Tableaus and Matrices represent equivalence classes of sequent proofs. A tree is not persay the end all be all of what a proof is. There 




<!-- <script src="/assets/elpi-js/lib/elpi-api.js" type="module"> </script> -->
<!-- <script src="/assets/elpi-js/lib/elpi-worker.js" type="module"> </script> -->

<script type="module">
import Elpi from "/assets/elpi-js/lib/elpi-api.js";
function log(l, p, t) { 
      console.log(l, p, t);
}

function answer(arg, ass) {
      console.log(JSON.stringify(arg));
      console.log(ass);
}


const elp = new Elpi(log, answer);
elp.compile([{ name: "toto.elpi", 
            content: "world \"hello\". world \"pussycat\"."}]);

elp.queryAll("world A.");


</script>


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



    function prove(){
        //var query = `prove0(${document.getElementById("querybox").value}, P).`;
        var query = document.getElementById("querybox").value;
        console.log(query);
        simple_query(document.getElementById("prolog_code").value, 
           query , answer => {
              //document.getElementById("sequent").innerHTML = `$$\\begin{prooftree}${pretty_proof(answer.links.Proof)}
              //  \\end{prooftree}$$`;
              //  MathJax.typeset()
 

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