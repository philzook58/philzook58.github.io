---
date: 2021-12-23
layout: post
title: 'Naive E-graph Rewriting in Souffle Datalog'
tags: datalog egraph
description: I use Souffle datalog to perform egraph like rewriting. It's cute.
---


Rewriting using equations is a compelling way to do a expression simplification, symbolic calculations, compiler optimizations. Egraphs are a data structure that keeps around all the possible equivalent terms instead of destructively rewriting them.

I previously wrote a [blog post](https://www.philipzucker.com/egraph-datalog/) sketchily describing how to encode some of the steps (ematching and congruence closure) in egraph rewriting using [Souffle datalog](https://souffle-lang.github.io/). The intention was to compile a nicer high level language (which became [egglog](http://www.philipzucker.com/egglog/). Give it a try in the browser! It's neat!) to these pieces via flattening of expressions mostly and insertion of indirections to eclass id.

I abandoned using souffle for egglog at a certain point because I realized it was unlikely to beat [egg](https://egraphs-good.github.io/) at it's own game, and it turned out actually doing the encoding I described before was not that clarifying or pleasant. A big issue is the stratification requirements of datalog (which maybe souffle let's you turn off?) and my reliance on the gensym counter. I was tying myself in knots trying to macro expand into stages of ematching and congruence closure. It sucked.

I have since come to understand more features of souffle that are not stock datalog. One such powerful feature is [algebraic data types](https://souffle-lang.github.io/types#algebraic-data-types-adt). Yes. Souffle datalog already has tree data structures available.

A simplified variant of egglog is what I like to call "hashlog". It is still a bottom up datalog-like evaluation, but instead of being backed by an egraph, you can be backed by a hash cons data structure.

My understand of the backing data structure of souffle ADTs make souffle already a hashlog. I think that ADTs are flattened into tables with unique ids for each node in the ADT.

In addition, Souffle already supports a [union find equivalence datastructure](https://souffle-lang.github.io/relations#equivalence-relations).

So at a high level, souffle already supports the data structure ingredients of egraphs. It is actually not so painful to encode egraph rewriting or egglog queries directly in souffle without compilation from a higher level language.

Here is an extremely simplest example of Hutton's razor: Addition expressions.

```
#define term(a) eq(a,a)

.type AExpr = Lit {n : number}
            | Plus {a: AExpr, b : AExpr}

.decl eq(x : AExpr, y : AExpr) eqrel
// in the case of no expected saturation, you can early stop with this directive
//.limitsize eq(n=4)

//congruence
eq(t1,t2) :- t1 = $Plus(a1,b1), t2 = $Plus(a2,b2), term(t1), eq(a1,a2), eq(b1,b2).

// termification
term(a), term(b) :- term($Plus(a,b)).

// constant propagation
eq(t, $Lit(a + b)) :- t = $Plus($Lit(a), $Lit(b)), term(t).

// Commutativity of addition
eq($Plus(a,b), e) :- eq($Plus(b,a), e).

// Associativity
eq($Plus($Plus(a,b),c), e) :- eq($Plus(a,$Plus(b,c)), e).
eq($Plus(a,$Plus(b,c)), e) :- eq($Plus($Plus(a,b),c), e).

// Initialization
term($Plus($Lit(3), $Lit(4))).

.output eq
```

Run with `souffle arith2.dl  -D -`

```
---------------
eq
x       y
===============
$Lit(3) $Lit(3)
$Lit(4) $Lit(4)
$Plus($Lit(3), $Lit(4)) $Plus($Lit(3), $Lit(4))
$Plus($Lit(3), $Lit(4)) $Plus($Lit(4), $Lit(3))
$Plus($Lit(3), $Lit(4)) $Lit(7)
$Plus($Lit(4), $Lit(3)) $Plus($Lit(3), $Lit(4))
$Plus($Lit(4), $Lit(3)) $Plus($Lit(4), $Lit(3))
$Plus($Lit(4), $Lit(3)) $Lit(7)
$Lit(7) $Plus($Lit(3), $Lit(4))
$Lit(7) $Plus($Lit(4), $Lit(3))
$Lit(7) $Lit(7)
===============

```

Note that souffle by default has the C preprocessor available. This is very convenient but also abusable. Constant propagation is directly expressible using the same mechanisms here, whereas in egg it is an analysis.
"Termification" is the filling of the union find with the subterms. It is unclear if my little trick of making the `term` database exactly equal to `eq(a,a)` is a wise one.

There are some other useful macros one can make to make rewrite rules look better
```
#define RW(a,b) eq(b, myextremelyfreshvalue) :- eq(a, myextremelyfreshvalue)
#define BIRW(a,b) RW(a,b). RW(b,a)
```

In addition, one could macroize out the congruence closure and termification relations.

Here's a very similar example using a slightly larger input language. This also shows extraction of smallest equivalent terms to the input `QUERY`.

```
#define term(a) eq(a,a)
#define RW(a,b) eq(b, myextremelyfreshvalue) :- eq(a, myextremelyfreshvalue)
#define BIRW(a,b) RW(a,b). RW(b,a)

.type AExpr = Lit {n : number}
            | Var {x : symbol}
            | Plus {a: AExpr, b : AExpr}
            | Mul {a: AExpr, b : AExpr}

.decl eq(x : AExpr, y : AExpr) eqrel
//.limitsize eq(n=4)

//congruence
eq(t1,t2) :- t1 = $Plus(a1,b1), t2 = $Plus(a2,b2), term(t1), eq(a1,a2), eq(b1,b2). // subtle: include term(t2) or not
eq(t1,t2) :- t1 = $Mul(a1,b1), t2 = $Mul(a2,b2), term(t1), eq(a1,a2), eq(b1,b2).

// termification
term(a), term(b) :- term($Plus(a,b)).
term(a), term(b) :- term($Mul(a,b)).

// constant propagation
eq(t, $Lit(a + b)) :- t = $Plus($Lit(a), $Lit(b)), term(t).
eq(t, $Lit(a * b)) :- t = $Mul($Lit(a), $Lit(b)), term(t).

// Commutativity
eq($Plus(a,b), e) :- eq($Plus(b,a), e).
eq($Mul(a,b), e)  :- eq($Mul(b,a), e).

// Associativity
BIRW( $Plus($Plus(a,b),c), $Plus(a,$Plus(b,c)) ).
eq($Plus(a,$Plus(b,c)), e) :- eq($Plus($Plus(a,b),c), e).
eq($Mul($Mul(a,b),c), e) :- eq($Mul(a,$Mul(b,c)), e).
eq($Mul(a,$Mul(b,c)), e) :- eq($Mul($Mul(a,b),c), e).

// distributivity
eq($Plus($Mul(a,b), $Mul(a,c)), e) :- eq($Mul(a, $Plus(b,c)), e).
eq($Mul(a, $Plus(b,c)), e)     :- eq($Plus($Mul(a,b), $Mul(a,c)), e).


.decl size(t : AExpr, s : unsigned)
size($Lit(a),1) :- term($Lit(a)).
size($Var(a),1) :- term($Var(a)).
size(t, 1 + sa + sb) :-  t = $Mul(a,b), term(t), size(a,sa), size(b,sb).
size(t, 1 + sa + sb) :-  t = $Plus(a,b), term(t), size(a,sa), size(b,sb).



// Initialization
//term($Plus($Lit(3), $Lit(4))).
#define QUERY $Mul($Lit(4),$Plus($Var("x"), $Lit(4)))
term(QUERY).


.decl res(t : AExpr)
res(t) :- eq(QUERY, t) , minsz = min n: {eq(QUERY,t2), size(t2,n)}, size(t, minsz).

.output res
```

Caveats:
- Congruence closure must be written as an explicit clauses
- It is inefficient implementation of an egraph
- It stores too much redundant information

However there are also huge upsides, mainly related to how featureful souffle is.

Upsides:
- Full egglog expressiveness and more
- Built in integer calculations
- Some analysis can be written as datalog programs
- Extraction can be written as datalog programs
- More Declarative than Rust
- Souffle is parallelizable and can be compiled to C++ code.
- Souffle can read and write to either CSV or SQLLite.
- Souffle supports proof generation of some kind

There may be some point in the application space where the upsides outweigh the downsides. In any case, I think this clarifies the intended semantics of egglog and was worth a blog post.

# Bits and Bobbles
There is a possibility that one could rewrite the datalog in a style that is more efficient. Perhaps using a `parents` table to speed up congruence closure and other memoizing features. Another possibility is to not actually build the full equivalence relation over all terms, but instead do indirection through the congruence relation at every ematch location. This would be horrible to write though.

[Subsumption](https://github.com/souffle-lang/souffle/pull/2114) (a recent addition to souffle) may allow for forgetting of redundant egraph info, keeping the tables smaller.

Perhaps if the developers of souffle are interested in such things, they could find a way to have more direct efficient support for egraphs

I note that the souffle authors have a [similar example](https://github.com/souffle-lang/souffle/blob/master/tests/example/rewrite/rewrite.dl) to the above in their test folder 

How useful might magic transforms be for proving purposes?

You can have (and must have) different `eq` relations if you have multiple ADTs you've defined. This is good and bad.