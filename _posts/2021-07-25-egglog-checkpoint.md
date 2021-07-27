---
author: Philip Zucker
date: 2021-07-27
layout: post
title: "Egglog: a Prolog Syntax for Egg, Checkpoint I"
tags:
- rust
- egraphs
---

### Tickle This

<script type="module">
        export { run };
        import init, { run_wasm } from '/assets/egglog1/egglog.js';

        async function run() {
            await init();
            var query = document.getElementById("query").value;
            const result = run_wasm(query);
            console.log(result);
            document.getElementById("result").value = result;
        }
        window.run = run;
        //run();
</script>

<textarea id="query" rows="20" style="width:100%">/* Base equality facts */
y = x.
z = y.
foo(biz) = bar(baz,plum(bippo)).

/* Base egraph insertions. No implied equalities. For "seeding" the egraph. */
f(x).
bar(boo).
plus(p,r).

/*
TODO: general looking prolog-like rules 
bar(X) :- f(X) = q.
biz(Z) = baz(biz(boz)) :- fizzy(floozy), buppo(Z).
*/

/* rewrite rules. Variables denoted by capitalization */
/* In principle just syntactic shorthand for plus(X,Y) = C :- plus(Y,X) = C. */
plus(X,Y) <- plus(Y,X).
X <- f(f(f(X))).
X <- f(f(X)).

/* bidirectional rewrite. A useful syntactic shorthand for two rewrite rules. */ 
plus(X,plus(Y,Z)) <-> plus(plus(X,Y),Z).

/* Guarded rewrite. */
fiz(baz) <- bar(boo), x = z.


/*  Query equalities. Ground queries (no variables) only at the moment.
    Note that this does NOT insert into the egraph. */
?- f(x) = x, x = x, y = x, plus(p,r) = plus(r,p), junk(boo) = otherjunk(baz).

/* Query simplification */
f(f(f(f(x)))).
?-  f(f(f(f(x)))).

/*
TODO: Directives.
:- node_limit(1000).
:- include("mylibrary.pl")
*/
</textarea>
<button onclick="run()">Run</button>
<textarea id="result" rows="20" style="width:100%"> </textarea>

Github repo. Look for future progress here: <https://github.com/philzook58/egglog>

### What is this?

Well, I've been visiting the folks for the first time since covid hit (saw my dad's rock band Catalyst play. They're pretty good!) and I had some time to make some progress on an idea I had. I'm getting a little turned around on what exactly I'm trying to do, so a checkpoint report and some affirming doots would be appreciated.

The [egg](https://egraphs-good.github.io/) library is pretty cool. It implement egraphs, a data structure for storing equalities between terms.

The analogy of egraphs to datalog has been fascinating to me. See here for more about that:
[Encoding E-graphs to Souffle Datalog](https://www.philipzucker.com/egraph-datalog/).

Datalog and the egraph are monotonic, in that they just keep gaining new inferences and never make missteps. Theorem proving like in a DPLL SAT solver or prolog makes guesses that may end up being wrong and needs to backtrack them.
This analogy has had me thinking that something prolog-esque might be a nice surface syntax for describing rules for egraphs.

There tend to be similarities between rewrite rule systems and prolog/horn clauses for some reason. Recently at work I was decribing how one can encode reachability problems of a control flow graph (CFG) into horn clauses, which is the basis I believe of the usage of constrained horn clause solvers (CHC) in program verification. Cody piped in that he liked to think about it in some way as a rewrite rule system, but that is the church he worships at.

Egg's implementation and verbiage is currently oriented around a rewrite rule perspective. Thinking about the horn clause perspective suggests different useful constructs. In particular, in my exploration of using egraphs for categorical reasoning <https://www.philipzucker.com/rust-category/>, guard conditions are very important and take a more prominent role, so the added flexibility might really come in handy there.

The egraph can itself be considered a kind of database. This perspective has been pointed out to me by (internet) conversations with Alessandro Cheli and Yihong Zhang. An equality in the egraph is obviously interesting information, but even just a term being in the egraph can sometimes be usefully interpreted as saying that the term is well formed or well typed. This was something I relied on in my category theory thing to remove some unecessary well typed conditions. Similar to datalog we can take the bottom up execution semantics.

- Things to the right of `:-` are things to lookup in the database
- Thing to the left of `:-` are things to insert into the database

An ematching rewrite rule , for example `plus(A,B) <- plus(B,A)`, in this language can be encoded as
`plus(A,B) = C :- plus(B,A) = C`. This is awkward though, and the case will be very common, so it is reasonable to introduce the notation `plus(A,B) <- plus(B,A)` as a syntactic shorthand for this form. 

Some interesting extensions to ematching present themselves in this notation. There is no fundamental obstruction to allowing multiple predicates on the right hand side of a clause. This can correspond to both the notion of guarded ematching, but also to the notion of multi triggers that you can find for example in [Z3](https://moskal.me/pdf/prtrig.pdf). Also, in principle the equality you insert on the left side of the clause may have very little to do with what you searched for in the right hand side, other than you need to instantiate every variable found in the left hand side from the right hand side. This is different in flavor than a rewrite rule.

Anyway, I haven't got all the way there yet, but I've got a bad parser working hooked up to basic egg! Huzzah!

[nom](https://github.com/Geal/nom) is a nice parser comnbinator library for rust.
I actually found a seperately packaged prolog parser <https://docs.rs/prolog_parser/0.8.68/prolog_parser/> desigend for [Scryer prolog](https://github.com/mthom/scryer-prolog), but it seemed complicated. I tickled out what do by looking at the list of combinators here <https://github.com/Geal/nom/blob/master/doc/choosing_a_combinator.md>

Egg is designed around building your own custom syntax enum type in rust, but really the built in SymbolLang actually covers everything I really want to do with egg at the moment. It is less efficient, but you need to be running a dynamically defined egraph problem as you do in a cli form of egg, I don't really see a way around it.

I compiled again to wasm, which is a big plus for rust for me. I described this in my previous post. <https://www.philipzucker.com/rust-category/> The same funky bug is still there.


## Bits and Bobbles

- I started trying to make literally a compiler from egraph queries to datalog using souffle's built in equivlaence class mechanism, but I was just bleeding asymptotic complexity at every turn. I grew deeply discouraged. The WIP was here <https://github.com/philzook58/egraph>
- Can we have Harrop formula like in lambda prolog? Forall is a way of introducing gensyms and is very natural for expressing some problems. In principle I can use ematching to increase the rule set, but I bet it would be fairly inefficient, so it would be better to preprocess and optimize. I'd also need a way to check rules for duplicates.
- My parser is trash. I need better errors and I need to deal with whitespace better.
- Term and GroundTerm are copies of egg::Pattern and egg::RecExpr of symbollang. Should I just get rid of them?
- Infix operators.
- Egg Analyses. In my application domains, I haven't felt much use of these. Constant folding is nice. Neutral terms. I don't know how to even syntactically express these well in datalog. Relations have union as join. Can consider other joins.
- <https://github.com/egraphs-good/egg/issues/84> What about taking in s-expressions/json and outputting them? Taking in commands from stdin
- Do I need to go in and play with the machine data type?
- Dealing with multi patterns.
- It feels convenient to have to have queries inserted in the database.
- A description I kind of like right now for egraphs is to consider a naive representation of destructionless rewrite rule application and consider the kind of sharing that is possible. Classical rewriting mutates the trees you're rewriting. Instead of doing that, you could copy the entire tree. This is very wasteful however. If your rewrite occurs near the top of the tree, you can share subtrees via pointers. If you're rewrite happens near the bottom you can share the parent structure by adding the indirection of "eclass" nodes.

### More stuff I wrote about egraphs
- <https://www.philipzucker.com/egraph-datalog/>
- <https://www.philipzucker.com/staging-patterns/>
- <https://www.philipzucker.com/a-simplified-egraph/>
- <https://www.philipzucker.com/union-find-dict/>
- <https://www.philipzucker.com/metatheory-progress/>


## Da Real Egglog

<iframe width="560" height="315" src="https://www.youtube.com/embed/XonNy7s2Nhk" title="YouTube video player" frameborder="0" allow="accelerometer; autoplay; clipboard-write; encrypted-media; gyroscope; picture-in-picture" allowfullscreen></iframe>