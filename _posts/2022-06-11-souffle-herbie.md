---
date: 2022-07-03
layout: post
title: "Souffle Herbie: Hacking Rationals into Datalog to Estimate Float Errors"
description: Rewriting float expressions and picking best one in datalog
tags: datalog floats
---

[Herbie](https://herbie.uwplse.org/) is a system to automatically improve the accuracy and or speed of floating point calculations.

An interesting idea was suggested by Zach Tatlock about emulating a very, very tiny subset of Herbie in datalog by using exact rationals.

[code here](https://github.com/philzook58/souffle-herbie)

# Calculating Errors

Different mathematically equivalent ways of calculating a quantity give slightly (or vastly) different answers when computed using floating point.

Even if you take as a given that library authors and hardware implementors implemented things like `sin`, `cos`, `+` accurately (not at all a given btw), that does not guarantee that compositions of the building blocks are accurate.

For example, mathematically the two following expressions are the same:
`(1e30 - 1e30) + 1 =  (1e30 + 1) - 1e30`
However in the latter, adding 1 to such a huge number does not change the floating point representation. It gets swamped in the finite precision of the floating point, so if you put these expressions into python you get pretty different answers `1.0 = 0.0`. Not so good.

How can we tell how accurate a calculation is?

1. Manual mathematical analysis
2. In some cases, the answer can be computed exactly. Rational and [algebraic](https://en.wikipedia.org/wiki/Algebraic_number) numbers
3. Interval arithmetic and exact real libraries deliver error bounds with the calculation.

I'll note a simple heuristic (but not foolproof) method is to calculate in a lower and higher accuracy (say 32 and 64 bit floats) and see if things look fishy.

However, we don't want to calculate just a single number, we want a good representation for _functions_ that are accurate for many values of a variable `x`. Again, you can 

1. Use sophisticated pen and paper mathematical analysis
2. Interval arithmetic (using this simplistically will give you a very large over approximation of the error). You can tile or pave the domain to shrink this error. See also taylor models and [tubes](http://www.codac.io/tutorial/05-tubes/index.html)

A good heuristic is you can just sample points and see how they do using one of the point error methods.

There are two halves to the Herbie solution: generating equivalent mathematical expressions, and evaluating their accuracy to pick the best ones.

To generate candidates we can use equational rewrite rules. These rewrite rules might encode clever gleaned tricks from the numerical computing literature, significant domain knowledge. A big part of the special sauce is figuring out what rewrite rules to have.

We want to maintain a collection of equivalent expressions, so destructive rewriting is not ideal. E-graphs are a efficient compact data structure for storing many expressions and equivalences between them. I'm not there yet.

Given these candidate expressions we have a reasonable means to estimate their relative accuracy: Calculate "true" answer in rationals and sample domain points.

## Rationals
How can we inject GNU multiprecision rationals into Souffle? The interface presented to the user of the library is opaque pointer types. I have toyed with just storing pointer values in 64bit souffle when I was binding Z3. Scary stuff. It doesn't really work here.

Part of datalog's thing is it needs to know when two things are equal. If I put `7/4` into the relation `foo` multiple times, that should reduce to only one entry. Z3 internally hashconses expressions. GMP does not. We could perhaps use the pointers of the returned gmp values if we could overload hashing and equality. Actually, I could subsume possibly to remove duplicates. But then we'd also have a memory leak.

As an inefficient but simple cheat, we can hash cons these numbers by serializing to and from souffle's built in symbol datatype, which is basically a string. Strings are the ultimate universal type and serialization/deserialization is packing and unpacking to this type. GMP uniquely normalizes and prints rationals.

Here are the souffle side stubs for dealing with `mpq`. It is a subtype of symbol, which is sent over FFI to C++ as a string. We also need some convenience functions for converting to and from souffle floats.

```souffle
.pragma "libraries" "gmpstubs"
.type mpq <: symbol

.functor float_of_mpqs(mpq):float
.functor mpqs_neg(mpq):mpq
.functor mpqs_abs(mpq):mpq
.functor mpqs_inv(mpq):mpq
.functor mpqs_add(mpq, mpq):mpq
.functor mpqs_sub(mpq, mpq):mpq
.functor mpqs_mul(mpq, mpq):mpq
.functor mpqs_div(mpq, mpq):mpq
.functor mpqs_cmp(mpq, mpq):number
#if RAM_DOMAIN_SIZE == 32
    .functor mpqs_of_float(float):mpq
    #define Q(x) @mpqs_of_float(x)
#elif RAM_DOMAIN_SIZE == 64
    .functor mpqs_of_double(float):mpq
    #define Q(x) @mpqs_of_double(x)
#else
    #error Unsupported RAM_DOMAIN_SIZE
#endif


#define QGT(x,y) (@mpqs_cmp(x,y) > 0)
#define QGTE(x,y) (@mpqs_cmp(x,y) >= 0)
#define QLT(x,y) (@mpqs_cmp(x,y) < 0)
#define QLTE(x,y) (@mpqs_cmp(x,y) <= 0)
// but actually regular = will work
#define QEQ(x,y) (@mpqs_cmp(x,y) == 0)
```

Here is one of the example stubs for addition. We need to 
1. Make some GMP objects
2. Deserialize them from strings
3. Compute the actual addition
4. Serialize the result to string
5. Cleanup memory allocation

```C++
    const char* mpqs_add(const char* x, const char* y){
        mpq_t x1, y1, z1;
        mpq_init(x1);
        mpq_init(y1);
        mpq_init(z1);
        mpq_set_str(x1,x,10);
        mpq_set_str(y1,y,10);

        mpq_add(z1, x1, y1);

        char* res = mpq_get_str(NULL,10,z1);
        mpq_clear(x1);
        mpq_clear(y1);
        mpq_clear(z1);
        return res;
    }
```


# Souffle Herbie

Nothing too clever is happening here yet since I am not yet using an egraph. I am doing simple term rewriting using Souffle adts. It is mostly an exercise in encoding concepts to datalog. The idiom of making a relation of all subexpressions is one I've encountered before. It is a relative of the magic set transformation, like many things. I'm not sure it is worth pursuing this here further as I need to be putting less effort into horrible souffle encodings and more effort into pushing towards a shared goal.

```souffle

#include "gmp.dl"
.type Expr = Lit {n : float} | Add {x : Expr, y : Expr} | X {} | Mul {x : Expr, y : Expr} // Div {x : expr, y : expr}

// Top level expression to rewrite
.decl top(x : Expr)

// Built table of all subexpressions
.decl term(x : Expr)
term(x) :- top(x).
term(x),term(y) :- term($Add(x,y)).
term(x),term(y) :- term($Mul(x,y)).

// An explicit equality relation over terms
// eqrel helps a little compared to n^2 naive
.decl eq(x : Expr, y : Expr) eqrel
term(x) :- eq(x,_).
eq(x,x) :- term(x).

// Associativity
eq(t, $Add(x,$Add(y,z))) :- term(t), t = $Add($Add(x,y),z).
eq(t, $Add($Add(x,y),z)) :- term(t), t = $Add(x,$Add(y,z)).

// Commutativity
eq(t, $Add(y,x)) :- term(t), t = $Add(x,y).
eq(t, x) :- term(t), t = $Add($Lit(0),x).

// Literal Combination. Should these be mpq not float?
eq(t, $Lit(m + n)) :- term(t), t = $Add($Lit(n),$Lit(m)).

// Associativity
eq(t, $Mul(x,$Mul(y,z))) :- term(t), t = $Mul($Mul(x,y),z).
eq(t, $Mul($Mul(x,y),z)) :- term(t), t = $Mul(x,$Mul(y,z)).
// Commutativity
eq(t, $Mul(y,x)) :- term(t), t = $Mul(x,y).

// identity absorption
eq(t, x) :- term(t), t = $Mul($Lit(1),x).

// Distributivity
eq(t, $Add($Mul(x,y), $Mul(x,z))) :- term(t), t = $Mul(x,$Add(y,z)).
eq(t, $Mul(x,$Add(y,z))) :- term(t), t = $Add($Mul(x,y), $Mul(x,z)).


// Simple sampling [0,1]
#define NSAMP 10
.decl sample(samp : unsigned, x : float)
sample(s, to_float(s)/NSAMP) :- s = range(0,NSAMP).

// Evaluate float expressions a sample points
.decl eval(samp : unsigned, t : Expr, n : float)
eval(s, t, n) :- term(t), t = $Lit(n), sample(s, _).
eval(s, t, x) :- term(t), t = $X(), sample(s, x).
eval(s, t, nx + ny) :- term(t), t = $Add(x,y), eval(s,x,nx), eval(s,y,ny).

// Evaluate exact expressions at sample point
.decl exact(samp : unsigned, t : Expr, n : mpq)
exact(s,t,Q(n)) :- term(t), t = $Lit(n), sample(s,_).
exact(s,t,Q(x)) :- term(t), t = $X(), sample(s,x).
exact(s,t,@mpqs_add(nx,ny)) :- term(t), t = $Add(x,y), exact(s,x,nx), exact(s,y,ny).

// Calculate error
.decl err(samp : unsigned, t : Expr, err : float) // should error be mpq? probably but it makes minimum kind of annoying
err(s, t, @float_of_mpqs(e)) :- eval(s,t,x1), exact(s,t,x2), e = @mpqs_abs(@mpqs_sub(Q(x1), x2)).

// Choice-domain let's us pick a unique best even when there are multiple of equivalent error
.decl best(samp : unsigned, t : Expr, best_t : Expr, val : float, err : float) choice-domain (samp, t)
best(s, t, t1, val, be) :- top(t), s = range(0,NSAMP), be = min e: {err(s, t2, e), eq(t,t2)}, eq(t,t1), err(s,t1,be), eval(s,t1,val).


//top($Add($Add($Lit(1),$X()),$Lit(10000))).
//top($Add($Add($Lit(100000000.349023490324),$X()),$Lit(-100000000.0932384239))).
top($Add($Add($Lit(1000000000000000000),$Lit(1)),$Lit(-1000000000000000000))).
top($Add($Add($Lit(1000000000000000000),$X()),$Lit(-1000000000000000000))).

.output sample(IO=stdout)
.output exact(IO=stdout)
.output err(IO=stdout)
.output best(IO=stdout)

```

# C++ Code

The GMP bindings
```C++
#include <gmp.h>
#include <iostream>




extern "C" {

    // We're probably leaking memory associated with the strings.
    const char* mpqs_of_float(float x){
        mpq_t y;
        mpq_init(y);
        mpq_set_d(y, x);
        char* res = mpq_get_str(NULL,10,y);
        mpq_clear(y);
        if(res == NULL){
            return "NULL";
        }
        return res;
    }
    float float_of_mpqs(const char* x){
        mpq_t x1;
        mpq_init(x1);
        mpq_set_str(x1,x,10);
        double z = mpq_get_d(x1);
        mpq_clear(x1);
        return (float) z;
    }

    const char* mpqs_of_double(double x){
        mpq_t y;
        mpq_init(y);
        mpq_set_d(y, x);
        char* res = mpq_get_str(NULL,10,y);
        mpq_clear(y);
        if(res == NULL){
            return "NULL";
        }
        return res;
    }
    float double_of_mpqs(const char* x){
        mpq_t x1;
        mpq_init(x1);
        mpq_set_str(x1,x,10);
        double z = mpq_get_d(x1);
        mpq_clear(x1);
        return z;
    }
    const char* mpqs_add(const char* x, const char* y){
        mpq_t x1, y1, z1;
        mpq_init(x1);
        mpq_init(y1);
        mpq_init(z1);
        mpq_set_str(x1,x,10);
        mpq_set_str(y1,y,10);

        mpq_add(z1, x1, y1);

        char* res = mpq_get_str(NULL,10,z1);
        mpq_clear(x1);
        mpq_clear(y1);
        mpq_clear(z1);
        return res;
    }

        const char* mpqs_sub(const char* x, const char* y){
        mpq_t x1, y1, z1;
        mpq_init(x1);
        mpq_init(y1);
        mpq_init(z1);
        mpq_set_str(x1,x,10);
        mpq_set_str(y1,y,10);

        mpq_sub(z1, x1, y1);

        char* res = mpq_get_str(NULL,10,z1);
        mpq_clear(x1);
        mpq_clear(y1);
        mpq_clear(z1);
        return res;
    }

    const char* mpqs_mul(const char* x, const char* y){
        mpq_t x1, y1, z1;
        mpq_init(x1);
        mpq_init(y1);
        mpq_init(z1);
        mpq_set_str(x1,x,10);
        mpq_set_str(y1,y,10);

        mpq_mul(z1, x1, y1);

        char* res = mpq_get_str(NULL,10,z1);
        mpq_clear(x1);
        mpq_clear(y1);
        mpq_clear(z1);
        return res;
    }
    const char* mpqs_div(const char* x, const char* y){
        mpq_t x1, y1, z1;
        mpq_init(x1);
        mpq_init(y1);
        mpq_init(z1);
        mpq_set_str(x1,x,10);
        mpq_set_str(y1,y,10);

        mpq_mul(z1, x1, y1);

        char* res = mpq_get_str(NULL,10,z1);
        mpq_clear(x1);
        mpq_clear(y1);
        mpq_clear(z1);
        return res;
    }
    const char* mpqs_abs(const char* x){
        mpq_t x1, z1;
        mpq_init(x1);
        mpq_init(z1);
        mpq_set_str(x1,x,10);

        mpq_abs(z1, x1);

        char* res = mpq_get_str(NULL,10,z1);
        mpq_clear(x1);
        mpq_clear(z1);
        return res;
    }
    const char* mpqs_neg(const char* x){
        mpq_t x1, z1;
        mpq_init(x1);
        mpq_init(z1);
        mpq_set_str(x1,x,10);

        mpq_abs(z1, x1);

        char* res = mpq_get_str(NULL,10,z1);
        mpq_clear(x1);
        mpq_clear(z1);
        return res;
    }

    const char* mpqs_inv(const char* x){
        mpq_t x1, z1;
        mpq_init(x1);
        mpq_init(z1);
        mpq_set_str(x1,x,10);

        mpq_abs(z1, x1);

        char* res = mpq_get_str(NULL,10,z1);
        mpq_clear(x1);
        mpq_clear(z1);
        return res;
    }


    int32_t mpqs_cmp(const char* x, const char* y){
        mpq_t x1, y1;
        mpq_init(x1);
        mpq_init(y1);
        mpq_set_str(x1,x,10);
        mpq_set_str(y1,y,10);

        int z = mpq_cmp(x1, y1);

        mpq_clear(x1);
        mpq_clear(y1);
        return z;
    }

}
```
# Bits and Bobbles
This isn't totally satisfactory, but there is enough here for an interesting post and I'm kind of stalled out. I'm a big believer in low standards for blog posts.

I suspect I am not handling both 32-64 bit souffle correctly. It's like... confusing, man.

Zach showed me a good example but the photo is totally blurry.
`1/(x+1) - 1/x ---> ? `



## An Aside: Datalog Modulo X
Max has invented a fun terminology.

There is a theme in hacking things into stock datalog. Stock datalog has set semantics, where it needs to determine if an item is already in the relations. Datalog also needs to search the database. Both of these operations need to refer to a notion of equality, and possibly comparation and/or hashing. Datalog's are not parametrized (at least not in an easily user accessible way) in the mechanism by which they consider two items equal (maybe Ascent is since it uses rust traits?). Datalog + Lattices and/or subsumption are powerful enough you can kind of mimic this capability.

If you want to add in a capability of "datalog modulo X", you need to find a way to uniquely embed X into one of the datatypes the datalog supports. This means canonizing X, which is not always easy (or even possible?). Is it better to canonize X or to add a smart equality function / indexing data structures?

In a [previous post](https://www.philipzucker.com/contextual-datalog/) I discussed first class sets. The canonization of sets in that case is removing duplicates and keeping the items sorted in the vector representation of the set. More trivially, let's say I wanted to support `x mod 17` as a data type. I need to embed these items into `number`.

It is nice if the notion of comparation explained to datalog is semantically relevant. As a counterexample, consider a pretty printed string. The lexicographic order of the string is not at all necessarily related to the order of the thing that was printed. I'm painfully aware of this every time my folders get sorted the wrong way in some directory (dates or numbers where we forgot to prefix with enough 0000). Souffle supports strings by interning them to unique integers, so I don't think you can do range queries over strings easily anyway.

Egglog itself is something like "datalog modulo uninterpreted functions".

Something I'm been investigating is how to talk about bound variables. The standard methodologies for canonizing bound terms turn variables names into canonical numbers (de bruijn levels or indices). See [Hash Consing modulo Alpha](https://arxiv.org/abs/2105.02856) for more about the issues here. For the thing I've been thinking about, the variables are really implicitly top level bound, and not bound in any particular order. A theme seems to be to name them as numbers in the order they are encountered in a term traversal. In other words, the signature is a set, not a list.




