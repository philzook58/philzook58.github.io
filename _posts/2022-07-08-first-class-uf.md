---
date: 2022-07-08
layout: post
title: "Chocolate in Peanut Butter: Prolog-ish Unification in Datalog with first class union finds"
description: Another step towards Lambda Datalog
tags: datalog theorem proving
---

I've been knocking my brains trying to figure out what is the difference between [datalog](https://www.philipzucker.com/notes/Languages/datalog/) and [prolog](https://www.philipzucker.com/notes/Languages/prolog/), what is "Lambda Datalog" in analogy to [lambda prolog](https://www.lix.polytechnique.fr/~dale/lProlog/), and how to support lambdas in egraphs. This blog post is hints in those directions.

I think an important concept along the way is first class union finds, so I built a prototype for [Souffle datalog](https://souffle-lang.github.io/). My code for this post is tucked away [here](https://github.com/philzook58/souffle-vector)

This post is independent but very much connected to [my previous post](https://www.philipzucker.com/contextual-datalog/), in which I discussed how to add contextual/hypothetical facts to souffle datalog using first class sets.

# Datalog vs Prolog

The relationship between datalog and prolog has been puzzling to me for a while. Like many questions, there are layers of sophistication in how one approaches it.

At the initial layer, one describes what datalog is. It is prolog with no compound terms (`a` but not `cons(x,cons(y,z)))`. It is bottom up executed and can be implemented using database query techniques. Datalog has superior termination properties and is more declarative in this sense than prolog.

At the next level of sophistication, we should point out there is a bit more to all of this. 
- Datalog has only ground terms in it's database. Datalog queries are _pattern matching_ really and not prolog's unification. This is a subtle point.
- Datalog with terms is a valid and useful topic. Datalog with terms has different but still painful termination problems compared to prolog. Datalog is a breadth first fair search though, so there is still some superior declarative character compared to prolog's SLD resolution.

Strictly speaking top down vs bottom up is not obviously the distinction between datalog and prolog
- [Top down datalog](https://dl.acm.org/doi/10.1145/73721.73736) is a thing. It strikes me as more complex to implement. Bottom up is beautifully simple.
- Magic Set transformations can lend top down character to datalog.
- [Tabled prolog](https://www.philipzucker.com/notes/Languages/prolog/#tabling). Tabled prolog builds a database is a query driven manner and restores many of the termination and declarative benefits that datalog has. Tabled prolog does not typically have the restriction that the database must be ground. A goal has both a query and answers associated with it. These syntactically are occurring in the same locations, but operationally they are rather different. They are analogous to calling into vs returning from a function. Datalog in some sense feels like only the answer half of tabling. Magic set is emulating the query half of tabling.

### Egglog

The big elephant in my mind has been: [Egglog](https://www.philipzucker.com/egglog/) (in whatever variation) is a datalog with a union find. Is it prolog? Why or why not?

I think the answer is it is not. It is a different thing (which is cool!).

Egglog has a union find but it is a global union find. Prolog has a branch local, backtrackable union find.
Via the datalog to tabling bridge, the analog of egglog's union find would be in a tabled equivalence relation backed by a union find. Discussions with Eddie Jones led to this standpoint (talking with him and Steven Ramsay was one of the highlights of my week at PLDI).

I think what is necessary to bring datalog up to snuff with prolog is to have a first class notion of union find as an object. The mantra of datalog is that you only have what you carry with you in a relation. Prolog has a secret stack that stores info (like the union find). You need to reify as much of this stack stuff as you need if you want to do the same in datalog.

# Foralls, Exists, and Metavariables
I am interested in how to extend datalog with `forall` and `exists` in a style similar to how lambda prolog does it for prolog. This post is another step towards Lambda Datalog.

The systems I have interacted with the most (Coq, prolog, lambda prolog) perform top down / backward reasoning. I think this have given me bad intuition about how things should naturally work in a forward reasoning system like Datalog.

In Coq, you start with a goal theorem to prove. You introduce forall bound variables using `intros` which puts a fresh variable in your context and removes the `forall x,` from the goal. When you encounter an `exists x,` in the goal, you can call the tactic `eexists` which will create a metavariable to be figured out later.

Lambda prolog does a very similar thing (lambda prolog is performing backwards proof search). Upon encountering a `pi`, lambda prolog generates a fresh identifier that may not unify with an unification variables previously constructed. `exists` is another way in lambda prolog of generating a new unification variable.

Datalog however is bottom up / forward reasoning. The intuition is actually reversed. `exists` in the heads of rules should be skolemized. `exists` in the body should be searched over the known database.

How do we deal with `forall` in datalog? A direction I went down is trying to adapt the lambda prolog approach. If I need to assure myself of `forall x, foo(x)` I could perhaps generate fresh variables `_foo_x` and see if I can prove `foo(_foo_x)` without any other assumptions about the properties of `_foo_x`.

I now think this is a wrong fit for pure datalog. I suspect this is a partial "magic setting" of some more natural mechanism.

In a forward reasoning system, it is usually the case that free variables are implicitly universally quantified. You may freely substitute the free variable in any proven theorem with any term and receive another theorem. I have seen things in Isabelle and HOLs that have more of this flavor

Long story short, to support universal quantification considering datalog as a theorem prover, I think you need a notion of first class union find.

This is what an inference rule replacing a free variable with a de bruijn bound forall variable would look like. This is a way to build more logical connectives into datalog in the style of my [previous blog post](https://www.philipzucker.com/contextual-datalog/), where I discussed the analogous construction for implication. `forall` is a kind of reification of the notion of metavariable like how implication `hyp => foo)` was a reification of the notion of context `hyp |- foo`.

```
/*
foo(V)
------------------forall intro
forall, foo(bvar(0))
*/

// datalog version
forall_foo($BVar(0)) :- foo($Var()).
```

How do we support metavariables in datalog? That brings us to terms.

# Terms
We need to reexamine the terms and data objects offered by default by souffle datalog. We need to have enough room in them to discuss metavariables (non grounded things).

This quickly brings us to start reading up on term indexing.

##  Term Indexing
Term indexing is an old problem. Tabled prolog and resolution provers need to be able to search over very large sets of terms.

See Chapter 18 of the Handbook of Automated Reasoning for an extremely in depth article on term indexing

The terms may be ground (no variables) vs non-ground (has variables). The query may be exact identity of terms, or looking for unifiable or matchable terms.
There are a variety of encodings and data structures that people have invented for this task.

You may try to do perfect or approximate indexing. In perfect indexing, you get back exactly what you asked for. In approximate indexing, you get back a superset of the terms you were asking for, which you may then need to filer using a linear search. If perfect indexing is expensive and approximate indexing is cheap and isn't returning too many false positives, it is desirable.

An approach of attack is to ask how to canonically represent terms.

An important question is how to store or index terms with variables in them. Giving variables explicit names like `foo(X,Y,X)` is bad because it is the same thing as `foo(A,B,A)`, but now your index will miss that. This is the alpha equivalence / dummy index problem.

There are at least two mechanisms by which to approach this.

- You can over approximate with an imperfect "shape index". `foo(A,B,A)` can be over approximated by the shape `foo(VAR,VAR,VAR)`, but so can `foo(A,B,B)` or `foo(A,B,C)`. 
- You can uniquely number variables in some traversal order. This canonicalizes variables names. For example a preorder traversal. Both `foo(A,B,A)`, `foo(X,Y,X)` becomes `foo(Var(0),Var(1),Var(0))`. This is not information losing.

Bundling the term shape `foo(VAR,VAR,VAR)` next to the vector `[0,1,0]` ia an alternative factoring of this information. This is what I chose to go with. It is not the unique solution to the problem.

#### Notes
This shape abstraction form is also very reminiscent of "co de bruijn" syntax [ Do be do be do.](https://arxiv.org/abs/1611.09259) [hash cons modulo alpha](https://arxiv.org/abs/2105.02856) where they enhance binding sites with maps. We are not yet really talking about binding sites, but we will.

It is also possible to bundle the tags at some intermediate location. 
This feels a little bit like we have a special kind of implicit binder out front of the term. Note One could also implement lambda terms in the preorder traversal style. It is a different style of canonical naming from de Bruijn indices. De Bruijn indices seem most related to path indexing, whereas this style is related to discrimination trees.

I kind of think maybe the first style and defining a `norm_term1(t)` `norm_term2(t,t2)` functors ... might have been nice. There is something pleasing about making the union find appear in the same place as the context of the previous post.


## Generic Souffle Terms

As part of this, I really need to be able to count the number of variables in subterms to be able to manipulate the union find.

I need my terms to support `$Var` constructors. I could ask a user (me) to do add this for every datatype of interest, but this is difficult/impossible to do in a generic way with the current state of Souffle foreign functors. It is hard to know which constructor is which from the C++ side. Perhaps an interface to request this information might help. There is an issue for it on the souffle github.

Instead what I chose to do is build a generic boxed `term` type. It supports everything expressible in souffle at the cost of a boxing. It would be possible to lower this cost for primitive types by using bit tagging tricks (reserving some bits of RamDomain to tell me if something is a symbol vs number vs unsigned), but I didn't do that for the moment.

There are other benefits. 
- `$App` style enables "first order, higher order" things. You can manipulate things that are akin to higher order objects with the caveat they must be named. This is related to defunctionalization and the theory of arrays.
- Can freely add in existentials
- Can build generic FFI C++ helper functions

The downside is
- Extra boxing is slow
- Bad type safety
- Awkward syntax. CPP macros can take the sting out of this.

### Code
These are the souffle FFI bindings and type definitions. 
I'm a bit split on `count_vars` functor vs `nvars` table. It would be nice (more efficient) to memoize this data with `nvars`, but it is a pain to program in this style.


```
.pragma "libraries" "term"
.functor count_var(t : term):number stateful // number because substr takes number only

// NOTE!!!!! maintained in alphabectical order for FFI
.type term = 
  App {f : term, x : term} // 0
| Num {n : number} // 1
| Sym {s : symbol} // 2
| Var {} // 3

#define NIL $Sym("nil")
#define T1(f,a) $App(f,a)
#define T2(f,a,b) $App($App(f,a),b)
#define CONS(x,xs) T2($Sym("cons"), x, xs)
 
.decl terms(t : term)
terms(f), terms(x) :- terms($App(f, x)). 

.decl nvars(t : term, n : unsigned)
nvars($Var(), 1).
nvars(t, 0) :- terms(t), (t = $Sym(_s) ; t = $Num(_n)).
nvars(t, nf + nx) :- terms(t), t = $App(f,x), nvars(f,nf), nvars(x,nx).

#define GROUND(t) nvars(t,0)
```

Here is the implementation of `count_var`. Note this very useful description <https://github.com/souffle-lang/souffle/issues/2181> of the low level format of ADTs.

Non-enum ADTs are built as 2-tuples. The first piece is a tag. They are tagged by integers in alphabetical order of the constructors. The second piece is just the value held by the constructor if the value is a single word. If it is a compound value, it holds the index of a record of that actual values.

Here I recursively traverse the ADT. It would be more efficient probably to convert this to a loop.

```C++
#include <cstdint>
#include "souffle/SouffleFunctor.h"
#include <cassert>
#include <vector>
#if RAM_DOMAIN_SIZE == 64
using FF_int = int64_t;
using FF_uint = uint64_t;
using FF_float = double;
#else
using FF_int = int32_t;
using FF_uint = uint32_t;
using FF_float = float;
#endif

#define VAR 3
#define SYM 2
#define APP 0
#define NUM 1

// https://github.com/souffle-lang/souffle/blob/master/tests/interface/functors/functors.cpp
extern "C"
{
souffle::RamDomain count_var(
        souffle::SymbolTable* symbolTable, souffle::RecordTable* recordTable, souffle::RamDomain arg) {
    assert(symbolTable && "NULL symbol table");
    assert(recordTable && "NULL record table");
 
    if (arg == 0) {
        return 0;
    } else {
        const souffle::RamDomain* myTuple0 = recordTable->unpack(arg, 2);
        souffle::RamDomain tag = myTuple0[0];
        assert(tag <= 3 && "Unexpected Tag in count_var");
        if(tag == VAR){
            return 1;
        } else if (tag == APP){
            const souffle::RamDomain* fargs = recordTable->unpack(myTuple0[1], 2);
            // Could do something smarter than recursion here.
            return count_var(symbolTable, recordTable, fargs[0]) + count_var(symbolTable, recordTable, fargs[1]);
        } else {
            return 0;
        }
    }
}

}
```

# Equivalence Relations and Union Finds
Increasingly nuanced understanding of equivalence relations and union finds seems to be useful.

Union finds are also called disjoint set datastructures.

Mathematically speaking, these things are trying to represent equivalence relations, which can be thought of as isomorphic to partitions of sets.

In particular, I think that _partial_ equivalence relations are a nice fit for the realities of the union find. Implicitly a int based union find is a partial equivalence relation over the integers. Anything not in the union find at all can be considered in it's own personal equivalence class or equivalently not in the partial relation.

The typical union find is the equivalence kernel of a function implicitly defined as the the fixpoint of a contracting map. As you are finding these fixpoint values, you can mutate to a map with the same equivalence kernel that is more more rapidly contracting.

- A union find can be using integer ids, or arbitrary datatypes. You can turn a union find over int ids into one over abitrary datatypes via maintaing isomophism dictionaries.
- Reference based union finds - Prolog unification variables are implemented in the reference style. A root variables is represented by a pointer to itself. I don't think prolog variables implement 
- Array based union finds. It is a general statement that you can convert any pointer based algorithm into one working over an array (or dictionary), with indices into the array acting as pointers. Depending on the specifics, you may lose performance (or even asymptotic performance for dictionaries).
- Path Compress or don't. Path compression is confusing. How essential is path compression? It is the thing that gets you that inverse ackermann complexity. It requires mutation so far as I know. Is the inverse acckerman complxity a requirement for anything I might call a union find? I don't think so.
- Keep depth information or don't. You want to avoid making the parent chain deep
- Equivalence kernel https://en.wikipedia.org/wiki/Kernel_(set_theory) https://en.wikipedia.org/wiki/Equivalence_relation#Equivalence_kernel A way of constructing disjoint sets is to note that preimages of any map form disjoint sets.
- Normalization. If you don't need online behavior of the union find, you can have a normalization pass. A fully normalized union find does not need a loop to lookup roots. It is a direct map to the root of the eq class
- Deterministic union finds. Instead of having online rules to compute which is the parent and which is the child when unioning two eqclasses, we can choose a deterministic tie breaking rule. Under this, we can parallelize more easily and we can guarantee a unique normalized union find instead of the specific of it depending on the order of unions.
- Scoped Union Finds, more on this another day.

### First Class UF in Souffle
My choice was to unbundle the union find from the term structure and make it exist in the "context" of the relation in question.
I initially was thinking I'd need to use the souffle vector type from my previous post, but it turned out to be very convenient to use souffle symbols as my union find type.
Souffle symbols are interned strings. You can ask for the string in the C++ interface. Strings are null terminated char arrays. In other words, this is already a kind of vector supported by Souffle natively.

For manipulating these union finds, souffle has the built in functors `cat(a,b)`, `subst(str, ind, length)` and `strlen(a)`.

In addition to these capabilities, I need to be able to normalize the string into a canonical form when it is being considered as a union find, and I need to be able to call `union` on elements of the union find.

The canonical form I choose is to label the eq classes by ascii characters starting from '0' traversing the uf structure from left to right.

In other words, the string "bcaabc" normalizes to "012201".

The is the equivalence kernel formulation, not the typcial contracting map formulation of an equivalence relation. The domain of the map I am represent is the integer index of the string. The codomain is the characters [0-z]. 

```souffle
.type str_uf <: symbol

.functor norm_str_uf(s : symbol):str_uf stateful
.functor str_union(s : symbol, i : unsigned, j : unsigned):symbol stateful
.functor str_uf_sub(s : str_uf, t : str_uf):unsigned stateful

#define FRESH0 "!"
#define FRESH1 "\""
#define FRESH2 "#"
#define FRESH3 "%"
#define FRESH5 "&"
#define FRESH6 "'"
#define FRESH7 "("
#define FRESH8 ")"

#define FIND(uf,i) substr(uf,i,1)
```

Because the normalization starts the symbols at [ascii](https://www.asciitable.com/) '0' = 0x30, any characters that come before that can be used a "fresh" eclasses.

The subtyping relation between `str_uf` and `symbol` does prevent you from accidentally forgetting to call `norm_str_uf` as it produces a type error if you try to insert an ordinary `symbol` into a field of type `str_uf`.


```C++
    souffle::RamDomain norm_str_uf(souffle::SymbolTable *symbolTable, souffle::RecordTable *recordTable,
                                   souffle::RamDomain uf_id)
    {
        assert(symbolTable && "NULL symbol table");
        assert(recordTable && "NULL record table");
        const std::string &uf = symbolTable->decode(uf_id);
        int cmap[256];
        memset(cmap, -1, sizeof(cmap)); // careful here. Does not generalize
        std::string uf2;
        char fresh = '0';
        for (int i = 0; uf[i] != '\0'; i++)
        {
            int normed = cmap[uf[i]];
            if (normed < 0)
            { // This value has not been seen yet.
                assert(fresh <= 'z' && "You are using a scary size of local union find");
                // std::cout << "fresh" << fresh << std::endl;
                cmap[uf[i]] = fresh;
                uf2.push_back(fresh);
                fresh++;
            }
            else
            {
                // std::cout << "not fresh \n";
                uf2.push_back(static_cast<char>(normed));
            }
        }
        return symbolTable->encode(uf2);
    }
```
It keeps a running counter of what is the next "fresh" character and maintains a mapping `cmap` from characters in the original to normalized characters.


# Append Example
Append in prolog can work on non ground lists.

```prolog
append([],Y,Y).
append([X|Xs], Ys, [X |Zs]) :- append(Xs,Ys,Zs). 
```

It should be able to generate a sequence of lists of increasing size with variable contents.

```prolog
?- append(X,Y,Z).
X = [],
Y = Z ;
X = [_A],
Z = [_A|Y] ;
X = [_A, _B],
Z = [_A, _B|Y] ;
X = [_A, _B, _C],
Z = [_A, _B, _C|Y] ;
X = [_A, _B, _C, _D],
Z = [_A, _B, _C, _D|Y] ;
```

These are non ground results. Stock datalog does not even have a way to represent these really.

With first class union finds, this datalog program emulates this behavior in some respects. You can see how painful and error prone the explicit unionfind manipulation. With metaprogramming or deeper datalog compiler introspection, this is automatable. There is a mismatch between datalog's notion of variable and the term notion of variable.


```souffle
#include "term.dl"
#include "uf.dl"

.decl append(x : term, y : term, z : term, uf : str_uf)

append(NIL, $Var(), $Var(), "00").
append(CONS($Var(), x),   y,   CONS($Var(), z),   @norm_str_uf(ufres)) :- 
        append(x, y, z, uf),
        nx = @count_var(x), ny = @count_var(y), nz = @count_var(z),
        fresh = FRESH0,
        ufx = substr(uf,0,nx),
        ufy = substr(uf,nx,ny),
        ufz = substr(uf,nx+ny,nz),
        ufres = cat(fresh, cat(ufx, cat(ufy, cat(fresh, ufz)))).

.limitsize append(n=5)

.output append(IO=stdout)

/*
---------------
append
===============
$Sym(nil)       $Var    $Var    00
$App($App($Sym(cons), $Var), $Sym(nil)) $Var    $App($App($Sym(cons), $Var), $Var)      0101
$App($App($Sym(cons), $Var), $App($App($Sym(cons), $Var), $Sym(nil)))   $Var    $App($App($Sym(cons), $Var), $App($App($Sym(cons), $Var), $Var))  012012
$App($App($Sym(cons), $Var), $App($App($Sym(cons), $Var), $App($App($Sym(cons), $Var), $Sym(nil))))     $Var    $App($App($Sym(cons), $Var), $App($App($Sym(cons), $Var), $App($App($Sym(cons), $Var), $Var)))    01230123
$App($App($Sym(cons), $Var), $App($App($Sym(cons), $Var), $App($App($Sym(cons), $Var), $App($App($Sym(cons), $Var), $Sym(nil)))))       $Var      $App($App($Sym(cons), $Var), $App($App($Sym(cons), $Var), $App($App($Sym(cons), $Var), $App($App($Sym(cons), $Var), $Var))))    0123401234
===============
*/
```

# Bits and Bobbles
We can support something similar to subsumptive tabling via souffle subsumption. Go figure. See below for the implementation of the uf comparison operator `str_uf_sub`.
```
// Variant tabling
// vs
// Subsumptive tabling

append(a,b,c,coarse) <= append(a,b,c,fine) :- 1 = @str_uf_sub(fine, coarse).
```

Having a global union find and small local canonicalized union finds may be a good trade off.

We could also try to encode the local union finds with shared substructure. That might be good.

Scoped Union Finds.

# More C++ Code

Implementation of calling union
```C++
    souffle::RamDomain str_union(
        souffle::SymbolTable *symbolTable, souffle::RecordTable *recordTable, souffle::RamDomain uf_id, souffle::RamDomain i, souffle::RamDomain j)
    {
        assert(symbolTable && "NULL symbol table");
        assert(recordTable && "NULL record table");

        const std::string &uf = symbolTable->decode(uf_id);
        assert(i < uf.length() && j < uf.length() && "Out of bound union index.");
        if (uf[i] == uf[j])
        { // already in same eqclass
            return uf_id;
        }
        std::string uf2;
        souffle::RamDomain pmin = std::min(uf[i], uf[j]); // pi <= i
        souffle::RamDomain pmax = std::max(uf[i], uf[j]); //  pj <= j
        for (auto &ch : uf)
        {
            if (ch == pmax)
            {
                uf2.push_back(pmin);
            }
            else
            {
                uf2.push_back(ch);
            }
        }
        return symbolTable->encode(uf2);
    }

    // uf_union
    // uf_inter

    // uf_sub doesn't need normalization persay
    // but we need to know which keys have been seen and which haven't
    // https://en.wikipedia.org/wiki/Partition_of_a_set#Refinement_of_partitions
    souffle::RamDomain str_uf_sub(
        souffle::SymbolTable *symbolTable, souffle::RecordTable *recordTable, souffle::RamDomain uf_id1, souffle::RamDomain uf_id2)
    {
        assert(symbolTable && "NULL symbol table");
        assert(recordTable && "NULL record table");

        if (uf_id1 == uf_id2)
        { // Same ufs. Equality
            return 1;
        }

        const std::string &uf1 = symbolTable->decode(uf_id1);
        const std::string &uf2 = symbolTable->decode(uf_id2);
        assert(uf1.length() == uf2.length() && "I'm not sure you should be comparing unequal length union finds");
        if (uf1.length() != uf2.length())
        {
            return 0; // maybe. is 0123 different from 012?
        }

        char cmap[256]; // map from character in uf1 to uf2
        // 012 <= 000 is ok.  000 <= 012 is not.
        // ids in lesser should uniquely match to ids in the latter
        //char seen = '0' - 1;
        bool seen[256] = {false}; // This seems to be ok?
        //memset(cmap, false, sizeof(cmap)); 
        for (int i = 0; i < uf1.length(); i++)
        {
            if (!seen[uf1[i]]) // uf1[i] > seen) // first time seeing this id. hence cmap is not initialized yet at this position
            {
                //seen = uf1[i];
                seen[uf1[i]] = true;
                cmap[uf1[i]] = uf2[i]; // fill in cmap at this position
            }
            else
            {
                if (cmap[uf1[i]] != uf2[i]) // If two elements from 1 point to different elements from 2, not a finer relation.
                {
                    return 0;
                }
            }
        }
        return 1;
    }
```