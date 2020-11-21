---
author: philzook58
comments: true
date: 2018-02-07 16:41:12+00:00
layout: post
link: https://www.philipzucker.com/?p=980
published: false
slug: Purescript dump corefn
title: Purescript dump corefn
wordpress_id: 980
---

Here is a description, somewhat out of date

https://github.com/paf31/24-days-of-purescript-2016/blob/master/22.markdown



Here is Phil Freeman using dump-corefn to derive lens

https://github.com/paf31/purescript-derive-lenses

https://github.com/paf31/purescript-derive-lenses/blob/master/src/Main.purs

He really is using it the pretty obvious way. Straight up digging through the JSON and then with hardcoded strings slamming it together. Makes sense.

Hmm. It used to be written in Haskell and then he rewrote it in purescript.





Here is a project trying to build out a toolset natively in purescript

https://github.com/paulyoung/purescript-corefn

This might have problems keeping up to sync with changes in format. Use purescript haskell bridge to automatically do so?





Here is the directory in the purescript compiler

[https://github.com/purescript/purescript/tree/master/src/Language/PureScript/CoreFn](https://github.com/purescript/purescript/tree/master/src/Language/PureScript/CoreFn)

I think this approach makes a lot of sense. Basically, could parse using fromJSON, process however you'd like in haskell and then output using toJSON. However, there is something inelegant and bad about needing Haskell in addition to purescript. That means in order to use this stuff, you'd have to know the Haskell ecosystem a bit too.



I would really like a rewrite engine. I'm concerned I'd want more type info than corefn makes available? Maybe not. I can tell whether a typeclass function came from the same dictionary or different ones.

Here's a big dump of some random file so you can inspect what corefn looks like right now

Maybe be helpful to copy to a json viewer http://jsonviewer.stack.hu/

    
    {"Algos":{"imports":["Algos","Data.DivisionRing","Data.Function","Data.List.Lazy","Data.Ring","Data.Semigroup","Data.Semiring","Data.Show","Prelude","Prim","Vec"],"builtWith":"0.11.6","exports":["Lit","Plus","Times","Inv","Sub","One","Zero","mstep","mstep'","powermethodstep","step","step'","showExpr","semiRingExpr","ringExpr","divExpr"],"decls":[{"Lit":["Constructor","Expr","Lit",["value0"]]},{"Plus":["Constructor","Expr","Plus",["value0","value1"]]},{"Times":["Constructor","Expr","Times",["value0","value1"]]},{"Inv":["Constructor","Expr","Inv",["value0"]]},{"Sub":["Constructor","Expr","Sub",["value0","value1"]]},{"One":["Constructor","Expr","One",[]]},{"Zero":["Constructor","Expr","Zero",[]]},{"step'":["Abs","dictMatVec",["Abs","dictSemiring",["Abs","dictMatVec1",["Abs","pa",["Abs","pinv",["Abs","b",["Abs","x",["App",["App",["Var","Data.Function.apply"],["App",["App",["Var","Vec.matvec"],["Var","dictMatVec"]],["Var","pinv"]]],["App",["App",["App",["Var","Data.Semiring.add"],["Var","dictSemiring"]],["Var","b"]],["App",["App",["App",["Var","Vec.matvec"],["Var","dictMatVec1"]],["Var","pa"]],["Var","x"]]]]]]]]]]]},{"step":["Abs","dictMatVec",["Abs","dictSemiring",["Abs","dictRing",["Abs","dictDivisionRing",["Abs","a",["Abs","p",["Abs","b",["Abs","x",["App",["App",["App",["App",["App",["App",["App",["Var","Algos.step'"],["Var","dictMatVec"]],["Var","dictSemiring"]],["Var","dictMatVec"]],["App",["App",["App",["Var","Data.Ring.sub"],["Var","dictRing"]],["Var","p"]],["Var","a"]]],["App",["App",["Var","Data.DivisionRing.recip"],["Var","dictDivisionRing"]],["Var","p"]]],["Var","b"]],["Var","x"]]]]]]]]]]},{"showExpr":["App",["Var","Data.Show.Show"],["Abs","v",["Case",[["Var","v"]],[[[["ConstructorBinder","Algos.Expr","Algos.Lit",[["VarBinder","x"]]]],["Var","x"]],[[["ConstructorBinder","Algos.Expr","Algos.Plus",[["VarBinder","x"],["VarBinder","y"]]]],["App",["App",["App",["Var","Data.Semigroup.append"],["Var","Data.Semigroup.semigroupString"]],["App",["App",["Var","Data.Show.show"],["Var","Algos.showExpr"]],["Var","x"]]],["App",["App",["App",["Var","Data.Semigroup.append"],["Var","Data.Semigroup.semigroupString"]],["Literal",["StringLiteral"," + "]]],["App",["App",["Var","Data.Show.show"],["Var","Algos.showExpr"]],["Var","y"]]]]],[[["ConstructorBinder","Algos.Expr","Algos.Times",[["VarBinder","x"],["VarBinder","y"]]]],["App",["App",["App",["Var","Data.Semigroup.append"],["Var","Data.Semigroup.semigroupString"]],["Literal",["StringLiteral","("]]],["App",["App",["App",["Var","Data.Semigroup.append"],["Var","Data.Semigroup.semigroupString"]],["App",["App",["Var","Data.Show.show"],["Var","Algos.showExpr"]],["Var","x"]]],["App",["App",["App",["Var","Data.Semigroup.append"],["Var","Data.Semigroup.semigroupString"]],["Literal",["StringLiteral"," * "]]],["App",["App",["App",["Var","Data.Semigroup.append"],["Var","Data.Semigroup.semigroupString"]],["App",["App",["Var","Data.Show.show"],["Var","Algos.showExpr"]],["Var","y"]]],["Literal",["StringLiteral",")"]]]]]]],[[["ConstructorBinder","Algos.Expr","Algos.Inv",[["VarBinder","x"]]]],["App",["App",["App",["Var","Data.Semigroup.append"],["Var","Data.Semigroup.semigroupString"]],["Literal",["StringLiteral","("]]],["App",["App",["App",["Var","Data.Semigroup.append"],["Var","Data.Semigroup.semigroupString"]],["App",["App",["Var","Data.Show.show"],["Var","Algos.showExpr"]],["Var","x"]]],["Literal",["StringLiteral",")^-1"]]]]],[[["ConstructorBinder","Algos.Expr","Algos.Sub",[["VarBinder","x"],["VarBinder","y"]]]],["App",["App",["App",["Var","Data.Semigroup.append"],["Var","Data.Semigroup.semigroupString"]],["App",["App",["Var","Data.Show.show"],["Var","Algos.showExpr"]],["Var","x"]]],["App",["App",["App",["Var","Data.Semigroup.append"],["Var","Data.Semigroup.semigroupString"]],["Literal",["StringLiteral"," - "]]],["App",["App",["Var","Data.Show.show"],["Var","Algos.showExpr"]],["Var","y"]]]]],[[["ConstructorBinder","Algos.Expr","Algos.One",[]]],["Literal",["StringLiteral","I"]]],[[["ConstructorBinder","Algos.Expr","Algos.Zero",[]]],["Literal",["StringLiteral","0"]]]]]]]},{"semiRingExpr":["App",["App",["App",["App",["Var","Data.Semiring.Semiring"],["Abs","v",["Abs","v1",["Case",[["Var","v"],["Var","v1"]],[[[["ConstructorBinder","Algos.Expr","Algos.Zero",[]],["VarBinder","x"]],["Var","x"]],[[["VarBinder","x"],["ConstructorBinder","Algos.Expr","Algos.Zero",[]]],["Var","x"]],[[["VarBinder","x"],["VarBinder","y"]],["App",["App",["Var","Algos.Plus"],["Var","x"]],["Var","y"]]]]]]]],["Abs","v",["Abs","v1",["Case",[["Var","v"],["Var","v1"]],[[[["ConstructorBinder","Algos.Expr","Algos.One",[]],["VarBinder","x"]],["Var","x"]],[[["VarBinder","x"],["ConstructorBinder","Algos.Expr","Algos.One",[]]],["Var","x"]],[[["VarBinder","x"],["VarBinder","y"]],["App",["App",["Var","Algos.Times"],["Var","x"]],["Var","y"]]]]]]]],["Var","Algos.One"]],["Var","Algos.Zero"]]},{"ringExpr":["App",["App",["Var","Data.Ring.Ring"],["Abs","__unused",["Var","Algos.semiRingExpr"]]],["Abs","x",["Abs","v",["Case",[["Var","x"],["Var","v"]],[[[["VarBinder","x1"],["ConstructorBinder","Algos.Expr","Algos.Zero",[]]],["Var","x1"]],[[["VarBinder","x1"],["VarBinder","y"]],["App",["App",["Var","Algos.Sub"],["Var","x1"]],["Var","y"]]]]]]]]},{"powermethodstep":["Abs","dictSemiring",["Abs","a",["Abs","v",["App",["App",["App",["Var","Data.Semiring.mul"],["Var","dictSemiring"]],["Var","a"]],["Var","v"]]]]]},{"mstep'":["Abs","dictSemiring",["Abs","pa",["Abs","pinv",["Abs","ainvn",["App",["App",["App",["Var","Data.Semiring.add"],["Var","dictSemiring"]],["Var","pinv"]],["App",["App",["App",["Var","Data.Semiring.mul"],["Var","dictSemiring"]],["App",["App",["App",["Var","Data.Semiring.mul"],["Var","dictSemiring"]],["Var","pinv"]],["Var","pa"]]],["Var","ainvn"]]]]]]]},{"mstep":["Abs","dictSemiring",["Abs","dictRing",["Abs","dictDivisionRing",["Abs","a",["Abs","p",["Abs","ainvn",["App",["App",["App",["App",["Var","Algos.mstep'"],["Var","dictSemiring"]],["App",["App",["App",["Var","Data.Ring.sub"],["Var","dictRing"]],["Var","p"]],["Var","a"]]],["App",["App",["Var","Data.DivisionRing.recip"],["Var","dictDivisionRing"]],["Var","p"]]],["Var","ainvn"]]]]]]]]},{"divExpr":["App",["App",["Var","Data.DivisionRing.DivisionRing"],["Abs","__unused",["Var","Algos.ringExpr"]]],["Abs","x",["App",["Var","Algos.Inv"],["Var","x"]]]]}],"foreign":[]}}




It is lisp-like.

App - application of function

Var - named variable

Abs - abstraction - creating a function with a variable name



Decls are most of the juice




