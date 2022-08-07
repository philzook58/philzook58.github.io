---
date: 2022-07-13
layout: post
title: "Lambda Normalization for Souffle Datalog"
description: Another step towards Lambda Datalog
tags: datalog theorem proving
---

Step by step onward to lambda datalog.

It may seem backwards the order in which I've approached the features that lambda datalog should have.
I've talked about adding

1. [Contexts](https://www.philipzucker.com/contextual-datalog/)
2. [Metavariables](https://www.philipzucker.com/first-class-uf/)

to Souffle Datalog (an efficient datalog implemented in C++), but the very first thing we should expect Lambda Datalog to have is lambda terms as objects.

Once you accept allowing trees as objects into datalog, there isn't anything particularly weird about having lambda terms at first glance. Lambda terms are just another kind of AST.

However, there are a couple of intrinsic operations we want to perform.

1. We want to be able to deal with alpha equivalence and beta reduction somehow.
2. We want to pattern match on lambda terms in a way that respects variable scope.

In the context of Souffle, it seems desirable to always canonize our terms that are going to be stored in a relation as much as possible. Otherwise, Souffle will perform redundant work and search. This was the case for contexts, where we sorted the contexts, for metavariables, where we uniquely canonized our union find info, and it's important here.

A standard way of making an alpha canonical term is to use de Bruijn indices. There are other [options](https://jesper.sikanda.be/posts/1001-syntax-representations.html). One of particular interest is co de bruijn which can be seen in the hash cons modulo alpha paper.

A standard way of implementing beta normalization is to use the locally nameless technique. In this technique, whenever you traverse under a lambda binder, you replace it's corresponding bound de Bruijn variables with a fresh free variable name. This avoids a lot of error prone stickiness related to accidental shadowing of variables and/or de bruijn raising and lowering.

Pattern matching lambda terms properly is a less discussed topic (at least on the blog circuit). It ends up not being so bad. The key insight I think is that you should consider pattern variables to be parametrized by the bound variables they may include like `\x \y F(x)`. Then you pattern match as usual, you'll perhaps find a `F(x) = x x`. Throw a lambda on `F` and it is easy enough to go through this term and find all `x` and replace them with the new bound variable. `F = \z. z z`. Now F is a closed term. If you come across a bound variable that is not a parameter to F, fail.

I must say. Something seems off about all this. Close but no cigar.

[code of post here](https://github.com/philzook58/souffle-vector/blob/main/libterm.cpp)

# Normalization
We want to be able to normalize lambda terms. It is possible to do so purely in Souffle, but it is very painful and you're produce a lot of cruft. It is easier and better to use C++ and make functions to do it

## Generic Terms
A key idea to being able to implement lambda normalization in the context of souffle is making a generic term type. We need to know the layout and structure of terms in order to be able to write C++ external functors that perform the appropriate.

Souffle ADTs are stored in the recordTable according to the scheme described [here](https://github.com/souffle-lang/souffle/issues/2181).
```souffle
.pragma "libraries" "term"
.functor reabstract1(t : term, n : unsigned):term stateful // number because substr takes number only
.functor reabstract2(t : term, n : unsigned, n2: unsigned):term stateful // number because substr takes number only
.functor beta_norm(t:term):term stateful

 // maintain in alphabectical order
.type term = 
  App {f : term, x : term} // 0
| BVar {n : unsigned} // 1
| Lam {b : term} //2 
| Num {n : number} // 3
| Sym {s : symbol} // 4
| Var {} // 5
```

## Vector Arena
When performing normalization we will be producing intermediate terms. We need to represent them. It may be inefficient to store them in Souffle's recordTable since we don't want to save these intermediate pieces for later.

I asked online for [what people do to represent Algebraic Data Types](https://twitter.com/SandMouth/status/1546884194651066369?s=20&t=k2602aIATchLpL7vSdn1UA). It is not so obvious what is the right thing to do in C++

What construct to use to represent the tree types
1. Use Tagged unions.
2. Use std::variant.
3. Use subclasses of a base type and visitor pattern

What to use for memory management:

1. std::shared_ptr. A stock reference counter implementation. I'm not confident this plays nice with tagged unions.
2. Manual memory management calling new and delete and stuff. Yikes.
3. Vector Arena - Use vector indices as pointers and put the structures in 


In most situations, I think std::variant + std::shared_ptr seem like a good default option. I opted to not do so. I went for tagged unions + vector arena. The reason I did so was that it was the approach in which I felt the most confident I knew what it would do and when it would cleanup memory. It actually makes a lot of sense. I've seen the technique before in Egg's `RecExpr` implementation <https://docs.rs/egg/latest/src/egg/language.rs.html#368-370>. When I intern back into souffle, I can just drop the vector. and it will clean itself up. By using Tagged union, I could reuse RamDomain values instead of having to think about std::variants index type.

I am not sure that my choice is best, but it seem to be working.


```C++
struct term;

using recexpr = std::vector<term>;

union uterm
{
    recexpr::size_type body;                               // Lam
    std::pair<recexpr::size_type, recexpr::size_type> app; // App
    souffle::RamDomain ramdom;                             // Everything else.
};

#define APP 0
#define BVAR 1
#define LAM 2
#define NUM 3
#define SYM 4
#define VAR 5
#define ZFVAR 6

#define NTAGS 6

#define NIL 0

struct term
{
    souffle::RamDomain tag;
    uterm data;
};

// Helpers to make recexpr objects.
recexpr::size_type mk_bvar(recexpr &expr, souffle::RamDomain i)
{
    term t = {BVAR, 0};
    t.data.ramdom = i;
    expr.push_back(t);
    return expr.size() - 1;
}

recexpr::size_type mk_fvar(recexpr &expr, souffle::RamDomain i)
{
    term t = {ZFVAR, 0};
    t.data.ramdom = i;
    expr.push_back(t);
    return expr.size() - 1;
}

recexpr::size_type mk_lam(recexpr &expr, recexpr::size_type i)
{
    term t = {LAM, 0};
    t.data.body = i;
    expr.push_back(t);
    return expr.size() - 1;
}

recexpr::size_type mk_app(recexpr &expr, recexpr::size_type f, recexpr::size_type x)
{
    term t = {APP, 0};
    t.data.app = std::make_pair(f, x);
    expr.push_back(t);
    return expr.size() - 1;
}


// Could do better recording of already seen stuff in Map. More memoization? Isn't clear the search is worth the effort.
recexpr::size_type from_souffle(souffle::RecordTable *recordTable, souffle::RamDomain t, recexpr &expr)
{
    const souffle::RamDomain *myTuple0 = recordTable->unpack(t, 2);
    souffle::RamDomain tag = myTuple0[0];
    term myterm = {tag, 0};
    switch (tag)
    {
    case APP:
    {
        const souffle::RamDomain *f_x = recordTable->unpack(myTuple0[1], 2);
        myterm.data.app.first = from_souffle(recordTable, f_x[0], expr);
        myterm.data.app.second = from_souffle(recordTable, f_x[1], expr);
        break;
    }
    case LAM:
    {
        myterm.data.body = from_souffle(recordTable, myTuple0[1], expr);
        break;
    }
    case BVAR:
    case NUM:
    case SYM:
    case VAR:
    {
        myterm.data.ramdom = myTuple0[1];
        break;
    }
    default:
        assert(false && "Missed Case in from_souffle");
    }
    expr.push_back(myterm); // maybe we could use emplace_back?
    return expr.size() - 1;
}

souffle::RamDomain to_souffle(souffle::RecordTable *recordTable, const recexpr &expr, recexpr::size_type i)
{
    term t = expr[i];
    switch (t.tag)
    {
    case LAM:
    {
        return mk_lam(recordTable, to_souffle(recordTable, expr, t.data.body));
    }
    case APP:
    {
        recexpr::size_type f = to_souffle(recordTable, expr, t.data.app.first);
        recexpr::size_type x = to_souffle(recordTable, expr, t.data.app.second);
        return mk_app(recordTable, f, x);
    }
    case NUM:
    case SYM:
    case VAR:
    case BVAR:
    {
        const souffle::RamDomain myTuple[2] = {t.tag, t.data.ramdom};
        return recordTable->pack(myTuple, 2);
    }
    default:
        assert(false && "Missing case in varopen");
    }
}
```


## Locally Nameless
I had made a previous prototype of pieces of Lambda Datalog in Ocaml, so I translated them somewhat faithfully.

de Bruijn indices label variables by the number of binders you have to cross to get the defining binder. It is an alpha canonical representation.

Locally nameless replaces de Bruijn indices with free variables whenever you traverse inside a binder to do anything.

There are two operations, opening and closing. Opening replaces a de bruijn variable and replaces it
Closing takes a free variable and turns it into a de Bruijn variable. This combo is power and sufficient to implement beta normalization correctly.

For fresh variables I used a reference to a mutable counter.

- [The Locally Nameless Representation - Chargueraud](https://chargueraud.org/research/2009/ln/main.pdf)
- [I am not a number, I'm a free variable!](http://www.cs.ru.nl/~james/RESEARCH/haskell2004.pdf)
- [Cody on Stackexchange - Locally-nameless normalization](https://cstheory.stackexchange.com/questions/39089/locally-nameless-normalization) 

```C++
/*

Varopen takes a level and an expression id and replaces bvar(level) with that expression id. 
This is performing substitution basically.
Traversing a lambda binder increases the level

let rec varopen k e (t : ln) =
  match t with
  | FVar _ -> t
  | FVarI _ -> t
  | BVar i -> if Int.(i = k) then e else t
  | App (f, y) -> App (varopen k e f, varopen k e y)
  | Lam body -> Lam { scope = varopen (k + 1) e body.scope }

let instantiate (e : ln) (t : scope) : ln = varopen 0 e t.scope
*/

recexpr::size_type varopen(recexpr &expr, souffle::RamDomain level, recexpr::size_type e, recexpr::size_type i)
{
    term t = expr[i];
    switch (t.tag)
    {
    case BVAR:
    {
        if (t.data.ramdom == level)
        {
            return e;
        }
        else
        {
            return i;
        }
    }
    case LAM:
    {
        return mk_lam(expr, varopen(expr, level + 1, e, t.data.body));
    }
    case APP:
    {
        recexpr::size_type f = varopen(expr, level, e, t.data.app.first);
        recexpr::size_type x = varopen(expr, level, e, t.data.app.second);
        return mk_app(expr, f, x);
    }
    case NUM:
    case SYM:
    case VAR:
    case ZFVAR:
        return i;
    default:
        assert(false && "Missing case in varopen");
    }
}

/*
varclose takes a free variable identifier and replaces it with bvar(level).
Traversing a lambda binder increases the level

let rec varclose k x (t : ln) : ln =
  match t with
  | FVar x' -> if String.(x = x') then BVar k else t
  | FVarI _ -> t
  | BVar _ -> t
  | App (f, y) -> App (varclose k x f, varclose k x y)
  | Lam body -> Lam { scope = varclose (k + 1) x body.scope }

let abstract (x : string) (t : ln) : scope = { scope = varclose 0 x t }
*/

recexpr::size_type varclose(recexpr &expr, souffle::RamDomain level, souffle::RamDomain fv, recexpr::size_type i)
{
    term t = expr[i];
    switch (t.tag)
    {
    case ZFVAR:
    {
        if (t.data.ramdom == fv)
        {
            return mk_bvar(expr, level);
        }
        else
        {
            return i;
        }
    }
    case LAM:
    {
        return mk_lam(expr, varclose(expr, level + 1, fv, t.data.body));
    }
    case APP:
    {
        recexpr::size_type f = varclose(expr, level, fv, t.data.app.first);
        recexpr::size_type x = varclose(expr, level, fv, t.data.app.second);
        return mk_app(expr, f, x);
    }
    case NUM:
    case SYM:
    case VAR:
    case BVAR:
        return i;
    default:
        assert(false && "Missing case in varclose");
    }
}


/*
beta_norm traverses and looks for shapes app(f,x). It normalizes f and x, if f is of the shape lam(b) then it performs
substitution [x/bvar(0)] b via varopen.
Whenever you go into a lambda, you need to replace that bvar(0) with a fresh variable. This is smart because substitution
messes with de bruijn indices.

let rec norm (t : ln) : ln =
  match t with
  | Lam t' ->
      let v = fresh () in
      let t'' = instantiate (FVarI v) t' in
      Lam (abstract' v (norm t''))
  | App (t, u) -> (
      let t' = norm t in
      let u' = norm u in
      match t' with Lam t'' -> norm (instantiate u' t'') | _ -> App (t', u'))
  | _ -> t
*/

recexpr::size_type beta_norm(recexpr &expr, souffle::RamDomain &fresh, recexpr::size_type i)
{
    term t = expr[i];
    switch (t.tag)
    {
    case LAM:
    {
        souffle::RamDomain curfresh = fresh;
        recexpr::size_type b = varopen(expr, 0, mk_fvar(expr, curfresh), t.data.body);
        fresh++;
        return mk_lam(expr, varclose(expr, 0, curfresh, beta_norm(expr, fresh, b)));
    }
    case APP:
    {
        recexpr::size_type f = beta_norm(expr, fresh, t.data.app.first);
        recexpr::size_type x = beta_norm(expr, fresh, t.data.app.second);
        if (expr[f].tag == LAM)
        {
            recexpr::size_type fx = varopen(expr, 0, x, expr[f].data.body);
            return beta_norm(expr, fresh, fx);
        }
        else
        {
            return mk_app(expr, f, x);
        }
    }
    case NUM:
    case SYM:
    case VAR:
    case BVAR:
    case ZFVAR:
        return i;
    default:
        assert(false && "Missing case in beta_norm");
    }
}

extern "C"
{

    souffle::RamDomain beta_norm(
        souffle::SymbolTable *symbolTable, souffle::RecordTable *recordTable, souffle::RamDomain arg)
    {
        recexpr expr;
        recexpr::size_type t = from_souffle(recordTable, arg, expr);
        souffle::RamDomain fresh = 0;
        recexpr::size_type t1 = beta_norm(expr, fresh, t);
        return to_souffle(recordTable, expr, t1);
    }
}
```


# Miller Matching


I was cowed by Higher Order Unification. Higher Order Pattern matching is a simpler problem and turns out to be fairly simple.

Unification is taking two terms with variables and figuring out if the variables can be instantiated with something to make the terms syntactically equal.
Pattern matching is taking a term with variables and one term with no variables and figuring out if the . Pattern matching is one way unification or Unification is two way pattern matching. Unification is a bit harder to understand and describe.

There is also a plethora of unification/pattern matching modulo X, where X may be equalities, assocativity, commutativity, alpha or beta equivalence and others. 

Unification of terms with lambdas in them is called higher order unification. It's a natural thing to consider if you are trying to generalize some things that worked in first order logic (resolution theorem proving, prolog) to higher order logic. It turns out that unification modulo beta reduction is undecidable and a hard problem. Not something you obviously want persay to be a small step in your deduction system.

There is a restriction from full beta reduction that is decidable. This fragment is sometimes called Miller Unification.

Datalog has pattern matching where prolog has unification. So perhaps we need to only consider Miller pattern matching.

It's actually surprisingly fairly simple.

Miller pattern matching is kind of the minimal of what is necessary for scopes to play nice with pattern variables.

Suppose I had the problem  `\x. F = \x. x`. What is a good answer for `F`? `x` you say? What the hell is `x`? The thing is that `F` is actually implicitly bound and it's implicitly bound _outside_ of the lambda because we're going to take the solution to F and use it somewhere else, again outside of the lambda. Explicitly we might write `exists F, \x. F = \x. x`. F therefore cannot refer to the variable. It would then have escaped it's scope.

If instead we have the problem `\x. F x = \x. x` we can solve this as `F = \y. y`. How did we do this? Well, really `F(x)` should be considered as a monolithic thing. Application of pattern variables should be considered distinct from regular application. The things that F is applied to are the bound quantities to which F may refer, smuggled in via a lambda in F itself.

So here is the basic procedure: Traverse down the pattern and term making sure things match as you go along. When you hit a `F(x,y,z,...)` in the pattern, it will match some term `t` in the matchee. If the only bound variables `t` contained are `x,y,z,...`, then `F` is `\x \y \z t`. If `t` contains a bound variable not in `F`'s application list, the pattern match fails. Essentially, we need to "reabstract" the bound pieces in the term `t` and the variables `F` is applied to in the pattern tell us what pieces we're allowed to "reabstract".

We could also consider allowing `F` to be applied to non bound things like `F(42)`. While we can "reabstract" `42`, this is not a great idea because pattern matching becomes nondeterministic again. Consider `F(42) = 42 + 42 + 42`. This has many solutions. `F = \x. 42 + 42 + 42`,  `F = \x. x + 42 + 42`,  `F = \x. 42 + x + 42`,  `F = \x. 42 + x + x`,  `F = \x. x + x + x` and so on. Maaaaybe you could say the first or last are "better" in some sense, but I'm skeptical.

So there you have it. In the Miller fragment, you annotate pattern variables explicitly with the bound variables you are allowing `F` to reabstract. This can be seen as only applying `F` to bound variables, but I prefer to thing of pattern application and regular application as distinct.

In the context of souffle, what we need to do is take the ordinary souffle pattern variables and reabstract them to be properly scoped (or fail). Any de Bruijn variable that is poorly scoped needs to be re asbtracted

In usage, reabstraction looks like this:

```
.decl named_term(name : symbol, t : term)
named_term("t1", $Lam($Lam($App($BVar(0), $BVar(1))))).

test_term("Testing out pattern use case") :- 
   named_term("t1", t), t = $Lam($Lam($App($BVar(0), F))), @reabstract1(F,1) != $Lam($BVar(0)). 

test_term("Testing out pattern use case. Should fail. Abstracting wrong variable. ") :- 
   named_term("t1", t), t = $Lam($Lam($App($BVar(0), F))), NONNIL(@reabstract1(F,0)). 
```

We are binding `F` to a poorly scope term. We reabstract it to produce a well scoped closed term. `F2 = @reabstract1(F,1)` is saying that `F = app(F2, bvar(1))` modulo beta normalization. It only accepts de bruijn indices, so we can see that it is is in the Miller pattern matching fragment. I should probably be checking that the indices given to reabstract1 are distinct just for sanities sake.

The interface is not ideal. We may need a very serious sugaring phase.


Here's the implementation. It's very straightforward in the end of the day. We don't even need to translate into the `recexpr` representation. There isn't any normalization happening here.

```C++
extern "C" 
{
    // Returns nil if failure to reabstract
    // Check for that on souffle side.
    // beta_zero?

    // The args are speicifed by the site at which the pattern occurs.
    souffle::RamDomain reabstract(
        souffle::RecordTable *recordTable,
        souffle::RamDomain term,
        int level,
        const std::vector<souffle::RamDomain> &args)
    {
        assert(recordTable && "NULL record table");
        assert(term != 0 && "reabstract of nil");

        const souffle::RamDomain *myTuple0 = recordTable->unpack(term, 2);
        souffle::RamDomain tag = myTuple0[0];
        assert(tag <= 3 && "Unexpected Tag in count_var");
        switch (tag)
        {
        case APP:
        {
            const souffle::RamDomain *f_x = recordTable->unpack(myTuple0[1], 2);
            const souffle::RamDomain f = reabstract(recordTable, f_x[0], level, args);
            // TODO early fail
            if (f == NIL)
            {
                return NIL;
            }
            const souffle::RamDomain x = reabstract(recordTable, f_x[1], level, args);
            if (x == NIL)
            {
                return NIL;
            }
            return mk_app(recordTable, f, x);
        }
        case BVAR: // reabstract var in in known
        {
            souffle::RamDomain i = myTuple0[1];
            if (i < level)
            {
                return term;
            }
            auto varind = std::find(args.begin(), args.end(), i - level); // search for bvar minus the extra lambdas we've traversed
            if (varind != args.end())                                     // Found bvar
            {
                return mk_bvar(recordTable, level + static_cast<souffle::RamDomain>(varind - args.begin()));
            }
            else
            {
                // std::cout << "did not find bvar" << i << level << i - level;
                //  Maybe I should just throw an exception to be caught. Eh.
                return NIL;
            }
        }
        case LAM:
        {
            // shift args? No. Reabstract is written in terms of the original position.
            // raise current level.
            const souffle::RamDomain b = reabstract(recordTable, myTuple0[1], level + 1, args);
            if (b == NIL)
            {
                return NIL;
            }
            return mk_lam(recordTable, b);
        }
        case NUM:
        case SYM:
        case VAR:
            return term;
        default:
            assert(false && "Missed Case in reabstract");
        }
    }

    souffle::RamDomain reabstract1(
        souffle::SymbolTable *symbolTable, souffle::RecordTable *recordTable,
        souffle::RamDomain term,
        souffle::RamDomain x0)
    {
        std::vector<souffle::RamDomain> args{x0};
        souffle::RamDomain res = reabstract(recordTable, term, 0, args);
        if (res != NIL)
        {
            return mk_lam(recordTable, res);
        }
        else
        {
            return NIL;
        }
    }

    souffle::RamDomain reabstract2(
        souffle::SymbolTable *symbolTable, souffle::RecordTable *recordTable,
        souffle::RamDomain term,
        souffle::RamDomain x0, souffle::RamDomain x1)
    {
        std::vector<souffle::RamDomain> args{x0, x1};
        souffle::RamDomain res = reabstract(recordTable, term, 0, args);
        if (res != NIL)
        {
            return mk_lam(recordTable, mk_lam(recordTable, res));
        }
        else
        {
            return NIL;
        }
    }
}
```

# Bits and Bobbles
Don't write patterns that can be beta reduced. Nothing goes into the database un beta reduced.

When I throw metavariables back in, do I need higher order unification? Yikes.

I've gone way too far without a concrete example. But you basically need all 3 capabilities to do anything. To traverse into lambdas, you want to generate metavariables.

Something is off about traversing these terms in C++ only to then traverse them a different way in datalog. Hmm. Am I again not respecting the ethos of bottom up enough? Maybe slapping normalization on datalog isn't the right thing to do at all.

Is what I really want is to directly expose varopen and varclose to datalog? I've been wrong every step of the way. I thought I wanted fresh vars, I wanted unification vars. I thought I wanted implication, I wanted contexts.

Do beta normalization and free var normalization in same pass.

It does seem possible to be more type safe from the souffle side. Require nil checking via giving back a wrapped answer. Have two related types closed_term and term to insist that you reabstract and avoid ruining scope.

It's tempting to have preorder traversed freevars labels. But then how to have them in a context? Just accept the context as ordered? :(



# Addendum
7/16/22

I tried just exposing abstract and instantiate. Somehow this feels more right. Still very clunky. Needs sugar?

```souffle
.pragma "libraries" "term"
// max_var and shift let us combine two terms of distinct free vars.

.functor max_var(t : term):number stateful
.functor shift_term(t : term, n : number):term stateful
.functor abstract(n : freevar, t:term):scope stateful
.functor instantiate(e:term, t:scope):term stateful
.functor norm(t: term):term stateful // norm_term
// unify via abstract?

.type freevar <: number
.type db_index <:  number
.type scope <:  number

.type term = 
  BVar {n : db_index} // 0 // What. Why?
| Bind {b : scope}  // 1
| FVar {n : freevar} // 2
| Num {n : number} // 3
| Sym {s : symbol} // 4
| T2 {f : term, x : term} // 5

// .type norm_term <: term // Hmm. No go?

#define MKBIND(b) $Bind(as(b, scope))
```

```C++
#include <cstdint>
#include "souffle/SouffleFunctor.h"
#include <cassert>
#include <vector>
#include <algorithm>
#include <unordered_map>
#if RAM_DOMAIN_SIZE == 64
using FF_int = int64_t;
using FF_uint = uint64_t;
using FF_float = double;
#else
using FF_int = int32_t;
using FF_uint = uint32_t;
using FF_float = float;
#endif

/*
.type term =
| Bind {b : scope} // 0
| BVar {n : db_index} // 1
| FVar {n : freevar} // 2
| Num {n : number} // 3
| Sym {s : symbol} // 4
| T2 {f : term, x : term} // 5
*/

#define BIND 1
#define BVAR 0
#define FVAR 2
#define NUM 3
#define SYM 4
#define T2 5

#define NTAGS 5

#define NIL 0

// Helpers to make souffle ADTs
inline souffle::RamDomain mk_t2(souffle::RecordTable *recordTable, souffle::RamDomain f, souffle::RamDomain x)
{
    souffle::RamDomain myTuple1[2] = {f, x};
    const souffle::RamDomain f_x0 = recordTable->pack(myTuple1, 2);
    souffle::RamDomain myTuple2[2] = {T2, f_x0};
    return recordTable->pack(myTuple2, 2);
}

inline souffle::RamDomain mk_bind(souffle::RecordTable *recordTable, souffle::RamDomain b)
{
    souffle::RamDomain myTuple2[2] = {BIND, b};
    return recordTable->pack(myTuple2, 2);
}

inline souffle::RamDomain mk_bvar(souffle::RecordTable *recordTable, souffle::RamDomain i)
{
    souffle::RamDomain myTuple2[2] = {BVAR, i};
    return recordTable->pack(myTuple2, 2);
}

inline souffle::RamDomain mk_fvar(souffle::RecordTable *recordTable, souffle::RamDomain i)
{
    souffle::RamDomain myTuple2[2] = {FVAR, i};
    return recordTable->pack(myTuple2, 2);
}

/*

Varopen takes a level and an expression id and replaces bvar(level) with that expression id.
This is performing substitution basically.
Traversing a lambda binder increases the level

let rec varopen k e (t : ln) =
  match t with
  | FVar _ -> t
  | FVarI _ -> t
  | BVar i -> if Int.(i = k) then e else t
  | App (f, y) -> App (varopen k e f, varopen k e y)
  | Lam body -> Lam { scope = varopen (k + 1) e body.scope }

let instantiate (e : ln) (t : scope) : ln = varopen 0 e t.scope
*/

souffle::RamDomain varopen(souffle::RecordTable *recordTable, souffle::RamDomain level, souffle::RamDomain e, souffle::RamDomain i)
{
    const souffle::RamDomain *myTuple0 = recordTable->unpack(i, 2);
    souffle::RamDomain tag = myTuple0[0];
    switch (tag)
    {
    case T2:
    {
        const souffle::RamDomain *f_x = recordTable->unpack(myTuple0[1], 2);
        const souffle::RamDomain f = varopen(recordTable, level, e, f_x[0]);
        const souffle::RamDomain x = varopen(recordTable, level, e, f_x[1]);
        return mk_t2(recordTable, f, x);
    }
    case BVAR:
    {
        if (myTuple0[1] == level)
        {
            return e;
        }
        else
        {
            return i;
        }
    }
    case BIND:
    {
        // could short circuit repacking here.
        return mk_bind(recordTable, varopen(recordTable, level + 1, e, myTuple0[1]));
    }
    case NUM:
    case SYM:
    case FVAR:
        return i;
    default:
        assert(false && "Missing case in varopen");
    }
}

/*
varclose takes a free variable identifier and replaces it with bvar(level).
Traversing a lambda binder increases the level

let rec varclose k x (t : ln) : ln =
  match t with
  | FVar x' -> if String.(x = x') then BVar k else t
  | FVarI _ -> t
  | BVar _ -> t
  | App (f, y) -> App (varclose k x f, varclose k x y)
  | Lam body -> Lam { scope = varclose (k + 1) x body.scope }

let abstract (x : string) (t : ln) : scope = { scope = varclose 0 x t }
*/

souffle::RamDomain varclose(souffle::RecordTable *recordTable, souffle::RamDomain level, souffle::RamDomain fv, souffle::RamDomain i)
{
    const souffle::RamDomain *myTuple0 = recordTable->unpack(i, 2);
    souffle::RamDomain tag = myTuple0[0];
    switch (tag)
    {
    case FVAR:
    {
        if (myTuple0[1] == fv)
        {
            return mk_bvar(recordTable, level);
        }
        else
        {
            return i;
        }
    }
    case BIND:
    {
        return mk_bind(recordTable, varclose(recordTable, level + 1, fv, myTuple0[1]));
    }
    case T2:
    {
        const souffle::RamDomain *f_x = recordTable->unpack(myTuple0[1], 2);
        souffle::RamDomain f = varclose(recordTable, level, fv, f_x[0]);
        souffle::RamDomain x = varclose(recordTable, level, fv, f_x[1]);
        return mk_t2(recordTable, f, x);
    }
    case NUM:
    case SYM:
    case BVAR:
        return i;
    default:
        assert(false && "Missing case in varclose");
    }
}

souffle::RamDomain norm_help(souffle::RecordTable *recordTable, std::unordered_map<souffle::RamDomain, souffle::RamDomain> &freemap, souffle::RamDomain t)
{
    const souffle::RamDomain *myTuple0 = recordTable->unpack(t, 2);
    souffle::RamDomain tag = myTuple0[0];
    switch (tag)
    {
    case FVAR:
    {

        auto elem = freemap.find(myTuple0[1]);
        if (elem != freemap.end()) // if already seen freevar
        {
            return elem->second;
        }
        else
        {
            souffle::RamDomain nfvar = freemap.size();
            souffle::RamDomain fvar = mk_fvar(recordTable, nfvar);
            freemap[myTuple0[1]] = fvar;
            return fvar;
        }
    }
    case BIND:
    {
        return mk_bind(recordTable, norm_help(recordTable, freemap, myTuple0[1]));
    }
    case T2:
    {
        const souffle::RamDomain *f_x = recordTable->unpack(myTuple0[1], 2);
        souffle::RamDomain f = norm_help(recordTable, freemap, f_x[0]);
        souffle::RamDomain x = norm_help(recordTable, freemap, f_x[1]);
        return mk_t2(recordTable, f, x);
    }
    case NUM:
    case SYM:
    case BVAR:
        return t;
    default:
        assert(false && "Missing case in varclose");
    }
}

// Examples of functor usage:
// https://github.com/souffle-lang/souffle/blob/master/tests/interface/functors/functors.cpp
extern "C"
{

    souffle::RamDomain norm(
        souffle::SymbolTable *symbolTable, souffle::RecordTable *recordTable, souffle::RamDomain term)
    {
        std::unordered_map<souffle::RamDomain, souffle::RamDomain> freemap;
        return norm_help(recordTable, freemap, term);
    }

    souffle::RamDomain abstract(
        souffle::SymbolTable *symbolTable, souffle::RecordTable *recordTable, souffle::RamDomain fv, souffle::RamDomain term)
    {
        assert(recordTable && "NULL record table");
        return varclose(recordTable, 0, fv, term);
    }

    souffle::RamDomain instantiate(
        souffle::SymbolTable *symbolTable, souffle::RecordTable *recordTable, souffle::RamDomain e, souffle::RamDomain term)
    {
        assert(recordTable && "NULL record table");
        return varopen(recordTable, 0, e, term);
    }

    souffle::RamDomain max_var(souffle::RecordTable *recordTable, souffle::RamDomain i)
    {
        const souffle::RamDomain *myTuple0 = recordTable->unpack(i, 2);
        souffle::RamDomain tag = myTuple0[0];
        switch (tag)
        {
        case FVAR:
        {
            return myTuple0[1];
        }
        case BIND:
        {
            return max_var(recordTable, myTuple0[1]);
        }
        case T2:
        {
            const souffle::RamDomain *f_x = recordTable->unpack(myTuple0[1], 2);
            souffle::RamDomain f = max_var(recordTable, f_x[0]);
            souffle::RamDomain x = max_var(recordTable, f_x[1]);
            return std::max(f, x);
        }
        case NUM:
        case SYM:
        case BVAR:
            return -100000;
        default:
            assert(false && "Missing case in max_var");
        }
    }
}
```
