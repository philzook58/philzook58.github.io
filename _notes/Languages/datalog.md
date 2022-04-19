---
layout: post
title: Datalog
---
- [What is datalog?](#what-is-datalog)
- [What can you do with datalog?](#what-can-you-do-with-datalog)
- [Implementations](#implementations)
  - [Rel](#rel)
  - [DDlog](#ddlog)
  - [IncA](#inca)
  - [Formulog](#formulog)
  - [Datafrog](#datafrog)
  - [Flix](#flix)
  - [dr lojekyl](#dr-lojekyl)
- [Souffle](#souffle)
  - [intrinsic functors](#intrinsic-functors)
  - [Souffle proofs](#souffle-proofs)
  - [Emulating Prolog](#emulating-prolog)
    - [Need Sets](#need-sets)
    - [Magic Set](#magic-set)
  - [Examples](#examples)
  - [User Defined Functors](#user-defined-functors)
  - [ADTs](#adts)
    - [Contexts are King](#contexts-are-king)
    - [field accessors](#field-accessors)
    - [Vectors](#vectors)
    - [Use ADT instead of autoinc()](#use-adt-instead-of-autoinc)
    - [Record Packing](#record-packing)
  - [Macros](#macros)
  - [Components](#components)
  - [Subsumption](#subsumption)
    - [Lattices](#lattices)
      - [Min/max lattice](#minmax-lattice)
      - [Maybe/Option lattice](#maybeoption-lattice)
      - [Intervals](#intervals)
    - [Subsumption as a master feature](#subsumption-as-a-master-feature)
      - [Provenance](#provenance)
      - [max min](#max-min)
      - [Equivalence relations](#equivalence-relations)
      - [Negation](#negation)
      - [Choice domain](#choice-domain)
  - [Choice Domain](#choice-domain-1)
  - [Negation](#negation-1)
  - [Souffle source](#souffle-source)
- [Examples](#examples-1)
  - [Program Analysis](#program-analysis)
    - [Available Expressions](#available-expressions)
    - [Very Busy Expressions](#very-busy-expressions)
    - [Reaching Definitions](#reaching-definitions)
    - [Liveness](#liveness)
    - [Zippers For Program Points](#zippers-for-program-points)
  - [Reflection](#reflection)
    - [BitSets](#bitsets)
      - [Bitset reflection](#bitset-reflection)
    - [Patricia Tries](#patricia-tries)
    - [BDDs](#bdds)
  - [BogoSort](#bogosort)
  - [Dynamic Programming](#dynamic-programming)
    - [Q learning](#q-learning)
  - [CHR](#chr)
  - [Lambda representation](#lambda-representation)
  - [Parsing](#parsing)
  - [Hilog](#hilog)
  - [meta circular interpreter](#meta-circular-interpreter)
  - [Equality Saturation](#equality-saturation)
  - [Term Rewriting](#term-rewriting)
  - [Graph Algorithms](#graph-algorithms)
  - [Translating Imperative Programs](#translating-imperative-programs)
  - [Translating functional programs](#translating-functional-programs)
  - [Model Checking](#model-checking)
  - [Timestamping](#timestamping)
  - [Theorem Proving](#theorem-proving)
    - [Skolemization for Existential Heads](#skolemization-for-existential-heads)
    - [Goals / Queries](#goals--queries)
    - [Uncurrying](#uncurrying)
    - [Higher Order Clauses](#higher-order-clauses)
    - [Universal Quantifier](#universal-quantifier)
    - [Categorical Example](#categorical-example)
  - [Typeclass resolution.](#typeclass-resolution)
  - [Borrow Checker](#borrow-checker)
  - [Type checking / inferring](#type-checking--inferring)
  - [Datalog Decompilers](#datalog-decompilers)
  - [CRDTs](#crdts)
  - [MultiSet Semantics](#multiset-semantics)
  - [Access Control Policies](#access-control-policies)
  - [Make](#make)
- [Topics](#topics)
  - [Provenance](#provenance-1)
  - [Semi Naive Eavluation](#semi-naive-eavluation)
  - [Datalog+- and the chase](#datalog--and-the-chase)
  - [Tabling](#tabling)
  - [Descriptive Complexity and Least Fiexed Point Logic](#descriptive-complexity-and-least-fiexed-point-logic)
  - [Push based Datalog](#push-based-datalog)
  - [Incremental / Differential Datalog](#incremental--differential-datalog)
- [Resources](#resources)
- [class(slotname : f(x,y) , ) :-](#classslotname--fxy----)
  - [building souffle emscripten](#building-souffle-emscripten)

# What is datalog?
When I say datalog, I might mean a couple intertwined different things. I might be referring to bottom up execution of logic programs.
Or I might be concentrating on 


Maybe part of what I like about datalog compared to prolog is
1. complete search strategy
2. logically pure. Kind of like Haskell's laziness kept it pure, Datalog's operation ordering is not obvious after compilation. This means extralogical stuff doesn't fly. 
3. simple execution semantics. Pattern match over database

# What can you do with datalog?
Well, just about anything you can do with ordinary database queries. What do you do with those? I dunno. Search for patterns?

But then on top of that you can use recursive queries. And that is where things get more interesting.
Program analysis.

Maybe just jump on down the the examples section. Or I should move them up here?




# Implementations
- Souffle
- Flix
- Rel
- IncA, [LADDDER](https://www.pl.informatik.uni-mainz.de/files/2021/04/inca-whole-program.pdf) differential dataflow sequel to Inca
- [Datafun](http://www.rntz.net/datafun/). lambda calculus with type system for tracking lattice monotonicity. and built in set type with comprehensions.
- [differential datalog](https://github.com/vmware/differential-datalog) DDlog
- dr lojekyll
- formulog
- [datafrog](https://github.com/rust-lang/datafrog) - kind of a manual datalog library in rust. Powers polonius, the experimental rust borrow checker
- ascent https://dl.acm.org/doi/pdf/10.1145/3497776.3517779 <https://docs.rs/ascent/latest/ascent/> Rust macro based datalog.
- uZ3 (mu z3) built into z3
- logicblox
- [flora2](http://flora.sourceforge.net/) ergo lite. Is this a datalog?
- [dynamic datalog](https://github.com/frankmcsherry/dynamic-datalog)

- yedalog
- EVE
- datomic

- bigdatalog - some kind of big data datalog. 
- [XTDB](https://xtdb.com/) XTDB is a general-purpose bitemporal database for SQL, Datalog & graph queries. What the hell does that mean
- percival https://percival.ink/

## Rel
[vid](https://www.youtube.com/watch?v=WRHy7M30mM4&t=136s&ab_channel=CMUDatabaseGroup)
Relational AI

## DDlog
Incremental datalog. You can assert and unassert facts.
Datalog compiler in haskell. Produces rust project. Rust project uses differential dataflow which in turn uses timely dataflow.

```ddlog
typedef UUID = bit<128>
input relation Host(id : UUID, name : string, ip : IP4)

// syntax to pick named fields
Host(.id=host_id)

"${x}" // string interpolation
// newtype wrapper / structs
typedef ip_addr_t = IPAddr{addr: bit<32>}
// match
var strs = match(value) {
    Some(s) -> string_split(s, ":")
}

//FlatMap to make generative functors.
[1,2,3] //vec litreral
["foo" -> 0] //map literals

extern functions
@ to pattern match and have name

groupby

Ref<>
Intern<> - istring. intern(), ival()

MultiSets
Streams
variants
typedef paylod = Eth1 {} | Eth2 {} | Eth3 {}

modules
```

## IncA
An incremental datalog for program analysis. Incremental can be a big deal in terms of developer interactivity. Also supports lattices


## Formulog
SMT formulas as data. Interesting distinction with CHC where smt formula are predicates.
Refinement type checker.
Symbolic Execution

## Datafrog
Engine behind polonius?
A kind of unsugared rust dsl
[Description](https://github.com/frankmcsherry/blog/blob/master/posts/2018-05-19.md)
I remember this being totally incomprehensible. I guess I must have lost my mind becaus it seems kind of nice now.


## Flix
Supports lattices.
Has a full programming language to.

[online playground](https://play.flix.dev/)
Also install as a vs code plugin. very nice.
[Fixpoints for the masses: programming with first-class Datalog constraints](https://dl.acm.org/doi/abs/10.1145/3428193)
## dr lojekyl
https://blog.trailofbits.com/2022/01/05/toward-a-best-of-both-worlds-binary-disassembler/
https://www.petergoodman.me/docs/dr-lojekyll.pdf

# Souffle

Souffle is a datalog implementation that is fast. It can be compiled to parallel C++ code. It also has a number of very intriguing datalog extensions available
- records
- algebraic data types
- subsumption
- aggregates
- choice domains



[choice domain](https://www.youtube.com/watch?v=TnLGbUqOsBc&ab_channel=ACMSIGPLAN) Functional dependencies of pieces of relation. 
eligible advisors, total order, bipartite matching, more dogs than cats, highest mark in grade.
Defined at relation level. Makes check before any insertion to see if something already defines functional dependency

`.plan` statements

`--show=initial-ram` and other options are quite interesting. The RAM is quite readable at least for small examples.


`as(a, number)` I can cast ADTs to numbers?
https://github.com/yihozhang/souffle/blob/conglog/tests/congruence/math.dl  interesting


[Examples directory](https://github.com/souffle-lang/souffle/tree/master/tests/example)
- convex hall
- anderson pointer, hmmer, java-pointsto
- dfa dataflow analysis
- edit distance
- josephus
- minesweeper
- nfsa2fsa nondet automata to det
- farmer wolf cabbage
- rewrite
- turing - turing machine implementation
- [trie](https://github.com/souffle-lang/souffle/blob/master/tests/example/sequences/sequences.dl) maybe this is what to do first.
- [palindrome](https://github.com/souffle-lang/souffle/blob/master/tests/example/palindrome/palindrome.dl)
- [matrix multipy](https://github.com/souffle-lang/souffle/blob/master/tests/example/mmult/mmult.dl)
- [early parser](https://github.com/souffle-lang/souffle/blob/master/tests/example/earley/earley.dl)
- graph domaintors
- 2sat

Convert string to relation. To avoid 
```souffle
str(s, char, i) :- range(0, len(s)) = i, char = substr(i, i+1, s) 
```

## intrinsic functors
`cat` `strlen` `substr(string,index,length)` `ord`

`lor` `land` `lxor` `band` `bxor` `bshl` `bshr` `bshru`


every non zero number is considered true.
max min + * % ^

`f(@g()) :- true` Sometimes you need to put true in the rhs position.


## Souffle proofs
Manual exploration of just dump it. Does the dump memoize?

`-t explain`
`.pragma "provenance" "explain"
```
output proof.json
format json
explain path(1,2)
exit
```

You can emulate proof production using subsumption. See below.

## Emulating Prolog
Datalog is bottom up and prolog is top down. In a sense datalog feels “push” and prolog feels “pull”. These viewpoints can be translated to some degree to each other. Prolog can gain some benefits of datalog via tabling, which is a memoization technique. Likewise datalog can become goal driven via the “magic set transformation”, The following is a simplified but intuitive presentation I believe of the vague idea.

Relations in prolog can be used in different [modes](https://www.swi-prolog.org/pldoc/man?section=modes) (this is prolog terminology btw. An interesting concept). It’s part of the beauty of prolog that relations are sometimes reversible or generative if written to be so. Sometimes prolog programs are written to only behave correctly if used as if they were essentially a function.

What is and isn't datalog?

What is and isn't function symbols? Function symbols are a subtle thing. You can encode function symbols into flat relations with different powers. Functions are a subset of relations after all. Existentials and gensyms

What is and isn't ground?

What is and isn't pattern matching vs unification. In some sense datalog is a pattern matching language, not unifying language.

### Need Sets


If you find yourself needing what is essentially a function call on a relation, you can define “need” relation for that relation that takes the arguments. Then the regular clauses producing that relation also take the need relation to push in the actually needed instantiations of the clause. Here is an example for factorial. We examine the body of fact to see that we need the recursive call evaluated in order to evaluate.

```souffle
.decl fib(n : unsigned, m : unsigned) //choice-domain n
.decl need_fib(n : unsigned)

fib(0,0).
fib(1,1).
fib(n, i + j) :- need_fib(n), fib(n-1,i), fib(n-2,j), n > 1.
need_fib(n-1), need_fib(n-2) :- need_fib(n), n > 1.

need_fib(6).
.output fib(IO=stdout)
.output need_fib(IO=stdout)
```

We have the expense of the extra table but we have gained pull based evaluation. Bottom up evaluation of fact would not terminate without an a priori bound on the argument. We could use subsumption to reduce the size of this table in this case.

Choice domain may present an optimization. It is marking the relation as functional in character, which in principle could allow soufflé to use an optimized data structure. I hope it makes things faster and doesn’t just add unnecessary checks on insert.
I a little bit suspect it will just make things slower.

Basically the idea is, you need to pick which top down modes you want to support, i.e. which of the prolog fields you expect to be grounded and which you don't. Then you can make a new relation that holds only the grounded fields. You make clauses that push down the need for every recursive call.
When you're translating typical functional algorithms, there is typically only the one functional mode required `-+`.

If you are using ADTs then perhaps one should consider the flattened version of the adt? ADTs only support some particular modes in the first place either ---+ or +++-. Give all args or give term and get args.


We could possibly subsume to reclaim need_fib? Hardly seems worth it.
```
need_fib(n) <= need_fib(m) :- fib(n,_). // doesn't do anything. Subsumption bug?
need_fib(n) <= need_fib(m) :- fib(n,_), n < m. // this one works. I don't know why n < m is required.
```

In what sense is need_set representing the call stack?

A common pattern when working with ADTs is I need a predicate of all subterms. This can be viewed as part of the need_set pattern. Recursive Functions that fold over terms are capable of sharing need sets. `terms` is really the need set of `fold`. That's interesting. So if you use combinators / recursion schemes to abstract over the recursion, you can use a `cata` need set. In some sense perhaps datalog can only express anamorphisms. `fold` is often seen a a fundamental combinator, capable of expressing anything (if you have highr order functions too).

A lot of what I'm doing is defunctionalizing a continuation

CHR also has need sets. Things that unlock computation.

### Magic Set



Specializes datalog program to a particular query / output.
Query answer transfomation

We could imagine applying dataflow analysis techniques to prolog programs. We can write dataflow analysis in a pleasant way using datalog. The languages of datalog and prolog coincide. Datalog terminates.

I suppose I identify datalog with bottom up execution, which is not necessarily the case depending on author.

In prolog SLD resolution, there are program points. We could create relations describing the store at these points. These are the supplementary 
For annotated predicates we could move the annotations as extra fields of the predicates instead of as annotations. This feels more natural when interpreting as a dataflow analysis. Annotations are a describing the binding state? (annotations are lattice? Maybe so but not in the right way)

"It is a form of partial evaluation: at query time, rewrite (specialize) the entire program to an equivalent one, then evaluate it bottom-up. A binding-time analysis identifies which predicates benefit from specialization. Sideways-information passing strategy guides the rewrite."

"I see it as a way to "hack" a bottom-up execution (from facts) into computing top-down (from queries). John Gallagher's query-answer transformation is related to that and used for program analysis https://arxiv.org/pdf/1405.3883.pdf, https://bishoksan.github.io/papers/scp18.pdf"



Emulating clp evaluation of prolog. The constraint store. Dif constraint into egglog.
What matters in a prolog context.
Order of goals hypothetically doesn’t matter? We want to hash cons to unique representatives of stuff that doesn't matter.
Scoping of fresh vars? Maybe a list of clauses that produced fresh vars. Does that order matter in principle? It might because unification can
Dif kind of lets us do a piece of scope escape prevention. Doesn’t contain.
What causes unification vars to exists? Presence fresh in a rule.
De bruin as cause. The binders cause variables to exist. Hence de bruin is close to a canonical rep.
Varmap says usage sites cause to exist?
Existential var in body. We can choose to ignore in datalog. Or we can say it would have been grounded eventually by some grounding site. (Or terminated on a ground fact.) yeah. A non ground fact could be seen as a new kind of constant?

[magic set slides](http://users.informatik.uni-halle.de/~brass/lp07/c7_magic.pdf)
- tail recursion is more efficient in sld resolution.
- metainterpeter. partial evaluation of metainterpeter with respect ot program and query, but not database. "sldmagic"

[A Framework for Bottom-Up Simulation of SLD-Resolution](https://users.informatik.uni-halle.de/~brass/push/publ/iclp14.pdf) bottom up metainterpeters
SLDMagic
"Sniped! I have never understood it but have wanted to. The output has always looked to me like constprop (bottom-up) and specialization (top-down), repeating." - Goodman
Resprenting sets of goals.


binding patterns using Option. Could also allow options in fields of adts.
```
.comp Option<T> {
  .type t = None {} | Some {x : t} 
}

fib()
```
What about `foo(X,X,1)`? `foo(None, None, Some(1))` is an over approximation of this case, losing the equivalence info. Well, therse constraints are also probably finitely enumerable.


sideways information passing strategy - SIPS. I think this is kind of picking an equivalent prolog evaluation order

[Efficient bottom-up computation of queries on stratified databases 1991](https://www.sciencedirect.com/science/article/pii/074310669190030S)

[Query evaluation in recursive databases: bottom-up and top-down reconciled bry](https://www.sciencedirect.com/science/article/abs/pii/0169023X90900178)


[Abstract Interpretation of Logic Programs Using Magic Transformations](https://www2.cs.arizona.edu/~debray/Publications/magic.pdf)

[Demand transformation](https://arxiv.org/pdf/1909.08246.pdf)
Is this he proper term for "need set"?
[More Efficient Datalog Queries: Subsumptive Tabling Beats Magic Sets∗](http://epilog.stanford.edu/logicprogramming/readings/tekle.pdf)
Is this saying need_sets may transfer to each other? Or subsume each other?
Can't even express this i don't think
p(x,y) <= p(x) :- 
Unless you use the $Var | $Lit wrapper
But this isn't even right.
p($Var(), $Var()) <= p($Lit(), $Lit())


KT Tekle
Liu


```souffle
.type UList = UL {n : number} | Cons {a : symbol, b : UList} | Nil {}
.type UNum = UL {n : symbol} | Lit {n : number}

// append([],A,A). 
// append([A | X], Y, Z) :- append(X,Y,Z1), Z = [A | Z1].

.decl append(x : UList, y : UList, z : UList)
.decl d_append(x : UList, y : UList, z : UList) // demand. Flow down.
append($Nil(), $UL(n), $UL(n) ) :- d_append($Nil(), $UL(n), $UL(_)). // or pick max?
append($Nil(), x, x ) :- d_append($Nil(), $UL(_), x).
append($Nil(), x, x ) :- d_append($Nil(), x, $UL(_)).

d_append(x,y,z) :- d_append($Cons(_,x), y, z).

// We need a pattern matching case? What if two UL alias?
d_append($Nil(), y,z) :- d_append($UL(m),y,z). // d_append($Nil(), y,z) should be another case. This isn't even right anyway


append($Cons(a,x), y, z) :- d_append($Cons(a,x), y, z), append(x,y,z1), z = $Cons(a,z1).

d_append($UL(0), $UL(1), $Cons("a", $Nil())).

.output append
```

Do immediate unification ahead of time?
Alternatively use explicit eq

```souffle
.type UList = UL {n : number} | Cons { }
.type UNum = U {n : symbol}

// append([],A,A). 
// append([A | X], Y, Z) :- append(X,Y,Z1), Z = [A | Z1].

.decl append(x : UList, y : UList, z : UList)
eq(y,z) :- append($Nil(), y, z), (y = $UL(_) ; z = $UL(_)).
// structural unification
eq(a,a1), eq(b,b1):- eq( $Cons(a,b), $Cons(a1,b1)).

// how do we have eq handle the two branching cases.


```

Need to carry an explicit union find field to thread? Slash an explicit substition mapping (slash homomorphism which is insane terminology)

## Examples

```souffle
.type obj <: symbol // Sometimes we need constructors, like Otimes.
.type typ = Obj {} | Hom {a : obj, b : obj}
// skolem symbols go into user defined type because we need to generate them
.typ Morph = Comp {f : Morph, g : Morph} | Id {a : Obj} | Sym {s : symbol}
#define F $Sym("f")
#define G $Sym("g")

// .decl morph( , a : obj. b : obj)
.decl typ()
.decl eqm(f : Morph, g : Morph) eqrel

comp(f : Morph, g : Morph : h : Morph)
comp() :- typ(), comp



```

## User Defined Functors
What about normalization? That's intriguing
BitSets

[souffle lib](https://github.com/souffle-lang/souffle-lib)

Some experiments of mine

- [souffle-z3](https://github.com/philzook58/souffle-z3) We can use the Z3 C bindings if we make a little helper function to generate a Z3 context.
- [souffle-lua](https://github.com/philzook58/souffle-lua) We can ffi call into lua for easier more dynamic user defined functor writing. Maybe I should try using guile?

For foreign data types you need to make your own external interning table, or the cheap prototyping thing to do is use serialization / deserialization to store as strings.
In Z3 you can use pointers, but that is because Z3 is internally hash consing.
You can briefly hold pointers as unsigned inside a rule, but you should probably compile souffle in 64 bit mode.

gnu multiprecision
Nah, this won't work. I need to do allocation. Unless I can call malloc?
```
.pragma "libraries" "gmp"
.type mp_int <: unsigned
.type mp_str <: symbol
.functor mpz_get_str(unsigned,unsigned,mp_int):symbol
.functor mpz_init(mp_int) // hmm. This won't work
.functor mpz_set_str(mp_int, mp_str, ):number
```



lib_ldscript
use `whereis` if ascii `cat` the file and include the things in group
`souffle libc.dl -lm-2.31 -lmvec`


```
.pragma "libraries" "m-2.31"
.pragma "libraries" "mvec"
.functor acosf(x: float): float
.decl test1(x : float)
test1(@acosf(0.1)) :- true.
.output test1(IO=stdout)
```

Holy crap this works

```souffle
.pragma "libraries" "z3"
.functor Z3_get_full_version(): symbol
.decl test1(x : symbol)
test1(@Z3_get_full_version()) :- true.
.output test1(IO=stdout)
```

```souffle
.pragma "libraries" "z3"
.functor Z3_get_full_version(): symbol
.functor Z3_mk_config() : Z3_config // It's cute but these are almost certainly 64 bit pointers. So a helper lib is probably better.
.type Z3_config :< unsigned
.functor Z3_mk_context(Z3_config): Z3_context
.functor Z3_eval_smtlib2_string(unsigned, symbol) : symbol
#define is_sat(x) Z3_eval_smtlib2_string(ctx, )

.decl test1(x : symbol)
test1(@Z3_get_full_version()) :- true.
.output test1(IO=stdout)
```

I can't figure out how to get libc, but it is the weirdest library of all.

Formulog via linking to Z3. Do my own interning for handling int32? Or compile souffle in 64bit mode. String manipulation of smtlib? Pool of z3 ctx? This is probably good because we may want to run parallel souffle.
```souffle
#define BINOP(op,x,y) cat(cat(cat(cat(cat("(", op), ", x), " "), y), " )") 
#define AND(x,y) BINOP("and", x, y)
#define OR(x,y)  BINOP("or", x, y)
#define IMPL(x,y) BINOP("=>",x,y)
#define TRUE "true"
// but like interpolated with cat.
.type smtint <: symbol
.type smtbool <: symbol
.type smtreal :< symbol

```
Hmm But how to deal with `define-const`.

Ah. This is in a sense striaghtforward ish CLP? CLP but in datalog.

CHR constraint handling rules. Can I embed into subsumption?


Syscalls. libc might already be available?

```souffle
.pragma "library-dirs" "/usr/lib/x86_64-linux-gnu/"
.pragma "libraries" "c"
.functor puts(symbol) : number

.decl test(x : number)
test(@puts("Hellow world")) :- true.
.output test(IO=stdout)

```

You can't defined your own user-defined functors inline. Two options that get you a lot of the way there are:
1. use cpp macros `#define FOO(x,y)`
2. Use auxiliary choice-domain relations. Memoization of functions. Many functions are so cheap you don't want to memoize them though.

## ADTs

ADTs are an incredible feature. They expand the expressive succinctness of souffle by so much it is unreal. It is somewhat possible to emulate them using other souffle features.

You can flatten adts into their relational form `$Add(x,y) = z ---> add(x,y,z)`. Perhaps you can get autoinc + choice to make them uniquely constructed.

See also <https://www.philipzucker.com/souffle-functor-hack/>

It is somewhat unfortnuate that there are not accessors for ADTs? It would make macro writing more satisfying

[interesting discussion of adt storage](https://github.com/souffle-lang/souffle/issues/2181)
- simple enums = ramdomain values
Converting simple enums to numbers. unsigned or number should do the same thing until you get to 2^31 or so
```
as($A(), number)
```

- Values with single fields representable as interger become `[tag: unsigned, value : A]`
- Compound values becomes [tag : unsigned, [all the stff]]


You can access the "id" associated with a value also `as([1,2,3],number)` for devious ends

### Contexts are King
a very useful thing to note is that you should use
contexts, delimited continuations, goal stack, zippers, to implement control flow.
Datalog is bottom up. In a sense it's a giant while loop. When you bottom upify or loopify recursive algorithms, sometimes you need to reify the call stack (or whatever else you might call it). See defunctionalize the continuation talk.
These contexts are expressible as 

### field accessors
It is a pain that there isn't a good way to make trustworthy fresh variables using `mcpp` due to lack of `__COUNTER__`. Best I can figure is hacks using `__LINE__` and concatenation. Otherwise insist on variables coming from outside into macro.

```souffle
#define FST(a,r) (r = [a,_])

.type myrec = [a : number, b : number]
.decl test(x : myrec)
.decl myfst(a : number)
myfst(a) :- test(r), FST(a,r).
test([1,2]).
.output myfst(IO=stdout)
```

This does _not_ work.
```souffle
#define FST(a,r) (r = $A(a, _))

.type myadt = A {x : number, b : number} | B {}
.decl test(x : myadt)
.decl myfst(a : number)
myfst(a) :- test(r), FST(a,r).
test($A(1,2)).
.output myfst(IO=stdout)
```

We _could_ probably cast to records to get the same effect. If you dare.

### Vectors
I am in no way endorsing this. Actual representation of vectors have size field in them. Eh maybe I can't even do this. I was thinking maybe I could do a unsafe cast, but that's a pain too. Maybe this is possible with some truly horrific macro programming + unsafe casts. Yikes.
```souffle
.type vector = [size : unsigned, key : unsigned]
```

safer alternative: We can make finite sized vectors as an adt
```
.comp Vector<T>{
.type vector = V0 {} | V1 {x1 : T} | V2 {x1 : T, x2 : T} | V3 {x1 : T, x2 : T, x3 : T} | V4 {x1 : T, x2 : T, x3 : T, x4 : T}
}

```

Or we can partially unroll a linked list to avoid so much indirection cost.

```
.comp Vector<T>{
.type vector = V0 {} | V1 {x1 : T} | V2 {x1 : T, x2 : T} | V3 {x1 : T, x2 : T, x3 : T} | V4 {x1 : T, x2 : T, x3 : T, x4 : T}
     | Cons {x1 : T, x2 : T, x3 : T, x4 : T, tail : vector}  
}
```



### Use ADT instead of autoinc()
autoinc() is a generative counter. It is nice because it is efficient. However, the stratification requirements on it are gnarly. It is too imperative, not declarative enough andyou get in trouble.
ADTs are also generative though. If you makea new object with them, you can make things that didn't exist in the original dataset. They sort of track how they were made by their arguments. This helps prevent you from instantiating the same thing twice. ADTs are basically hash consed/interned.

### Record Packing
Sometimes your number of fields in the relation get crazy. Like let's say you want to describe some abstract domain like an interval. You need to carry 2 parameters everywhere when you're really talking about 1.

You may however be taking a big performance hit. There is always a indirection hit of records vs unpacked records. Here is it felt more accutely because it isn't just a memory deref, it's a whole table lookup (? how exactly are records imlepmented).

It is a bummer that souffle doesn't have record access notation. It's be nice for macros.

If you want join semantics on lattice records
```
.type Interval = [l : unsigned, u : unsigned]
.type VSA = [l, u, stride, ]

```
// default souffle has 32 unsigned. You can make your own 64 bit by combination. Taking a big perfroamcne hit
.type U64 =  [l : unsigned, u : unsigned]

## Macros
You get the C preprocessor run by default over souffle files. I find this incredibly useful. Admittedly, the need for a C preprocessor can be considered evidence of a weakness in a language (meaning many many languages are weak. C, haskell, etc.)

## Components

## Subsumption
[1995 subsumption paper](https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.28.103&rep=rep1&type=pdf)


### Lattices
See also bitset lattice above

Lattices can be sometimes encoded into finite sets. Consider the 4 valued lattice of unknonw, true, false, conflict. These are the power sets of a set of size 2. This can be represented as two tables which can be in different states of full. Because of stratified negation, it is not always possible to observe things. You shouldn't really observe anything other than filter questions anyhow though. Anf you're always above unknown.
true(a), false(a)

You often need 1 rule to combine pieces with the join of the lattice and 1 rule for subsumption. This is probably not efficient, but it is works.
It would be be nice to have a construct that did both at once efficiently. We should be immeditaly erasing a and b when we compute their join.

```souffle
rel(join(a,b)) :- rel(a), rel(b).
rel(a) <= rel(b) :- lattice_order(a, b).
```

Perhaps you could make a generic lattice compment parametrized over join

```
.comp Lattice<T> {
  .decl join(x: T, y : T, z : T) overridable
  .decl r(x:T, y:T)
  r(z) :- r(x), r(y), join(x,y,z).
  r(x) <= r(y) :- join(x,y,y).
}
```
But filling out joi will be annoying. There isn't a great way to parametrize over functors so far as I can tell.



Todo:
- vsa


#### Min/max lattice

labaeller Max lattice
I suppose in a sense this is the lattice of the function space `T -> int` defining join pointwise. If that's your bag.

```souffle
.comp Upper<T> {
   .decl upper(label: T, x : unsigned)
   upper(l,x) <= upper(l,x1) :- x <= x1.
}

.comp Lower<T> {
   .decl lower(label: T, x : unsigned)
   lower(l,x) <= lower(l,x1) :- x1 <= x.
}

.init symu = Upper<symbol>

symu.upper("x", 1).
symu.upper("x", 7).
symu.upper("y", 4).
.output symu.upper(IO=stdout)

```

If you have both, you have an interval, see below.

#### Maybe/Option lattice

```prolog

.type optionsymbol = None {} | Some {val : symbol}

.decl A(v : optionsymbol)

A($Some("foo")).
A($Some("fiz")).
A($Some("foz")).
//A($None()).

A($None()) :- A(x), A(y), x != y.
A(x) <= A($None()) :- A($None()).

.output A(IO=stdout)
```

Also you can make N max set lattice. Keep sorted. Insertion sort. Kind of a pain if you get too many

```
.type Nary = None {} | One {a : T} | Two {a : T, b : T} | Top {}
```


#### Intervals

```souffle
.type Interval = [l : float, u : float]
.type Expr = Add {a : Expr, b : Expr} | Lit { a : float} | Var {x : symbol} 

// all expressions
.decl expr(e : Expr)
expr(a), expr(b) :- expr($Add(a,b)).

expr($Add($Var("x"), $Lit(1))).

.decl iexpr(e : Expr, i : Interval)
iexpr($Lit(n), [n,n]):- expr($Lit(n)).
iexpr(e, [la + lb, ua + ub]) :- iexpr( a, [la,ua] ), iexpr(b, [lb, ub]), e = $Add(a,b), expr(e).

// also vice versa back down the tree
iexpr(b, [ l1 - ua, u1 - la]) :- iexpr($Add(a,b), [l1,u1]), iexpr(a, [la,ua]).


iexpr($Var("x"), [-1,1]).
iexpr($Var("x"), [0,1]).
iexpr($Add($Var("x"), $Var("x")), [0.5,0.75]).

// meet semantics
iexpr(e, [max(l1,l2), min(u1,u2)]) :- iexpr(e, [l1,u1]), iexpr(e, [l2,u2]).
iexpr(e, [l1,u1]) <= iexpr(e, [l2,u2]) :- l1 <= l2, u2 <= u1.  
.output iexpr(IO=stdout)
```
It may not be worth packing into a record though. This almost certainly has performance cost. Records never get deleted. So you should just unpack into a relation. 


```
// intervals getting bigger
/*
components?
We'd need to know at compile time how many possible instantations
.comp Interval<T>{
    .decl upper(x : T)
    .decl lower(x : T)
}


*/
.decl upper(t : symbol, x : float)
upper(t,x) <= upper(t, y) :- x <= y.
.decl lower(t : symbol, x : float)
lower(t,x) <= lower(t, y) :- y <= x.

.output upper(IO=stdout)
.output lower(IO=stdout)

upper("foo", 7).
upper("foo", 8).
upper("fiz", 9).

lower("foo", 8).
lower("fiz", 9).
lower("foo", -3).


.comp Interval<T>{
    .decl upper(x : T)
    upper(x) <= upper(y) :- x <= y.
    .decl lower(x : T)
    lower(x) <= lower(y) :- y <= x.
}
.init i1 = Interval<float>

i1.upper(3).
i1.upper(14).
.output i1.upper(IO=stdout)
```


[dr. disassembler](https://github.com/lifting-bits/dds) and blog post

Linear "datalog" - destructive state update
Using Sqllite - https://www.sqlite.org/lang_with.html recursive ctes seem to get you a lot. Cool examples. Mandelbrot

bottom up Dynamic programming in datalog? Rod cutting.

### Subsumption as a master feature

Subsumption is kind of the master feature. Now, you can kind of also model these just ignoring the fact you're producing way to many tuples. But subsumption let's you at least keep it kind of under control

#### Provenance
Provenance using subsumption. Provenance works by deleting longer derivations.

```souffle
.type Explain = Base {} | Trans {u : unsigned}
.decl edge(a : unsigned, b : unsigned)
edge(1,2).
edge(2,3).
edge(1,3).
edge(3,4).
.decl path(a : unsigned, b : unsigned, why : Explain, proof_depth : unsigned)
path(a,b, $Base(), 1) :- edge(a,b).
path(a, c, $Trans(b), depth + 1) :- edge(a,b), path(b,c, _, depth).
path(a,b, w1, d1) <= path(a, b, w2, d2) :- d2 <= d1.
.output path(IO=stdout)
```

#### max min
Max, min using subsumption. 
```
mymax(z) :- reltomax(z).
mymax(z) <= mymax(z2) :- z1 <= z2.
```

Can I do sum and count? Maybe not. Not without tracking what we've already used. You could do this with bitsets. Requires reflection I guess. c
Ah, I don't need to require tracking the set of already used, only count. Oh. Wait. no.
```
mysum(count : unsigned, partial_sum : unsigned)
mysum(1,n) :- foo(n).
mysum(n+1,) 
nope
```
But if I cluster them into groups, I can take approximate sums.
What if I track the current biggest element in the sum. This is tracking the state of a naive summation algorithm. We can lways necode an imperative algorithm to datalog by tracking state. This relies on summing positive numbers only
```
mysum(n,n) :- foo(n).
mysum(n, partsum + n) :- mysum(top,partsum), foo(n), top < n.
mysum(n,sum) <= mysum(n,sum') :- sum <= sum'.
```

count
```
mycount(n,1) :- foo(n).
mycount(n, partcount + 1) :- mysum(top,partcount), foo(n), top < n.
mysum(n,count) <= mysum(n,count2) :- count <= count2.
```

Could hyperloglog be relevant for approximate counts? https://en.wikipedia.org/wiki/HyperLogLog

A* search. Interesting. If you have the a bound on distance you can subsumpt away bad possible paths. Path search is a canonical datalog program. Subsumption allows shortest path search (which I showed above).


#### Equivalence relations
You can make a findParent relation to get a lot of the functionality of equivalence relations. Eq relations are already the same thing as
```souffle
eq(x,y) :- eq(y,x). //sym
eq(x,z) :- eq(x,y), eq(y,z). //trans
```

But this is more efficient. The relation is linear sized instead of quadratic in the size of the eq classes.

```souffle
#define EQ(x,y) canon(x,z), canon(y,z)
.decl canon(x : symbol, y : symbol)
.decl symbol(x : symbol)
symbol("x").
symbol("y").
symbol("z").
canon(x,x) :- symbol(x).
canon(x,z) :- canon(x,y), canon(y,z).
canon(x,y) <= canon(x,z) :- y <= z.
canon("x","y").
canon("y","z").
.output canon(IO=stdout)
```


#### Negation
Can I emulate negation using subsumption? Maybe remove negated clauses from rule, and later delete them?

Need to duplicate all clauses to negated versions?

f(a,b) <= f(dummy,dummy) :- not_f(a,b)
not_f() <= not_f() :- f(a,b).

f(a,b) :- g(a,b)
not_g(a,b) :- not_f(a,b)



But f(a,b) does damage we need to undo?

#### Choice domain

Choice using subsumption, static or dynamic notion of "better".


## Choice Domain
<https://souffle-lang.github.io/choice> picks first one to come along
Can I combine choice domain and lattice. But choice domain once you pick you're done...
well. I can recover lattice style via an explicit congruence closure. So. it doesn't matter I guess.


## Negation
Stratification

See answer set programming and stable model semantics

What about

foo(x) :- biz, !foo(z).

and making it stratified by deleting all negative atoms (an overpapproximation?) And then using the overapproximation of !.

foo1(x) :- biz.
foo(x) :- biz, !foo1(z)

What about guarded negation? For example if you turn off stratification but are able to supply an explicit `strata(n)` guard. This could be useful for 


##  Souffle source
- synthesizer - actual code printers
- include/souffle - the runtime of souffle
- ram, relational abstract machine
- 

# Examples

## Program Analysis
[Unification based pointer analysis](https://github.com/souffle-lang/souffle/pull/2231) "Steensgaard style" vs Anderson style
[hash consed points to sets](https://yuleisui.github.io/publications/sas21.pdf)

[graspan](http://web.cs.ucla.edu/~wangkai/papers/asplos17)

Points to analysis tutorial
Doop


### Available Expressions 
[Lecture notes on static analysis in datalog](https://www.cse.psu.edu/~gxt29/teaching/cse597s19/slides/06StaticaAnalysisInDatalog.pdf)
https://courses.cs.washington.edu/courses/csep501/18sp/lectures/T-dataflow.pdf

The expression is computed and/or the connection between expression and store state is not severed by subsequent write. on every path 
Not that available expressions _does not_ mean expression is available.
```
x = a + b
x = 0
```
AE says `a+b` is available at the ned of this snippet. So it's a bit subtler what AE means. It means that with a little fiddling the expression _could be_ available.


Every path means we need an intersection. Datalog does unions more naturally, so we need to work wth the inverse relation notavailable. The intersection of available is the union of notavailable

Program
```
start:
  x = readinput
  a = readinput
  b = readinput
  br x, l1, l2
l1:
  z = a + b
  br l3
l2:
  z = b + a
  br l3
l3:
  print a + b // if a + b is available we don't have to recompute
```

```souffle


.type blk <: symbol 
.type Expr  = Add {x : Expr, y : Expr}| Var {x : symbol}
.decl gen(blk : blk, e : Expr)

gen("l1" , $Add($Var("a"),$Var("b"))).
//gen("l2" , $Add($Var("a"),$Var("b"))). // uncomment to see a + b in l3 avail expr
gen("l2" , $Add($Var("b"),$Var("a"))).

.decl expr(e : Expr)
expr(e) :- gen(_,e).
expr(a), expr(b) :- expr($Add(a,b)).

.decl var(v : symbol)
var("z").
var("x").
var("b").
var("a").

.decl free(v : symbol, e : Expr)
free(x, e) :- expr(e), e = $Var(x).
free(x, e) :- expr(e), e = $Add(a,b), (free(x,a); free(x,b)).


.decl kill(b : blk, e : Expr)
kill("start",e ) :- expr(e), (free("x", e) ; free("a", e) ; free("b", e)).
kill("l1",e ) :- expr(e), free("z",e).
kill("l2",e ) :- expr(e), free("z",e).

//?x + ?y <-> ?y + ?z.
/*
gen(l,e2) :- gen(l,e1), eq(e1,e2).
but don't do the same for kill? This feels like cheating.
We can supercharge gen but we also supercharge kill. Eh?
Well maybe not.
*/


.decl next(blk1:blk, blk2:blk)
next("l1","l3").
next("l2","l3").
next("start","l1").
next("start","l2").

.decl label(b : blk)
label(l) :- next(l,_) ; next(_,l).

.decl notavail_entry(b : blk, e : Expr)
.decl notavail_exit(b : blk, e : Expr)
notavail_entry("start", e) :- expr(e).

notavail_exit(l, e) :- (notavail_entry(l, e) ; kill(l,e)), !gen(l, e).
notavail_entry(L2,e) :- notavail_exit(L1,e), next(L1,L2).

.decl avail(l : blk, e  : Expr)
avail(l,e) :- label(l), expr(e), !notavail_exit(l,e).
.output avail
```

So what do I need to do to extend this to equivalent expressions?

### Very Busy Expressions
Expressions that are needed on every path
Intersection

### Reaching Definitions


### Liveness
Variables that will be needed on at least one path
A backwards analysis
Union

### Zippers For Program Points
It is possible to generate program points from the Imp AST via using zippers

```souffle
.type Expr = Lit { x : number }
           | Var { x : symbol }
           | Add {e_1 : Expr, e_2 :Expr}
.type Stmt = Set { x : symbol, e : Expr}
           | Seq {s_1 : Stmt, s_2 : Stmt}
.type StmtHole = LSeq {s : Stmt} | RSeq {s : Stmt}
.type Zipper = Cons { hd : StmtHole , rest : Zipper} | Nil {}
.type Label =  [ctx : Zipper, stmt : Stmt] 
// Do I need this? .decl label(; : Label, ctx : Zipper, stmt : Stmt)
.decl prog(s : Stmt)

.decl stmt(ctx : Zipper, s : Stmt)
stmt($Nil(), s) :- prog(s).
stmt($Cons($LSeq(r), ctx), l), stmt($Cons($RSeq(l) , ctx), r) :- stmt(ctx, $Seq(l,r)).

.decl expr(ctx : Zipper, e : Expr)
expr(ctx, e) :- stmt(ctx, $Set(_,e)).
expr(ctx, y), expr(ctx, x) :- expr(ctx, $Add(x,y)).

.decl next(ctx : Zipper, s : Stmt, ctx2 : Zipper, s2 : Stmt)

next($Cons($LSeq(r), ctx), l, $Cons($RSeq(l), ctx), r) :- stmt(ctx, $Seq(l,r)).
next($Cons($RSeq(l), ctx), r, ctx2, s2) :- next(ctx, $Seq(l,r), ctx2, s2).

prog(
  $Seq($Set("x", $Lit(0)),
  $Seq($Set("y", $Add($Var("x"),$Lit(1))),
       $Set("x", $Var("y"))
      ))
).


.decl hasvar(e : Expr, x : symbol)
hasvar($Var(v), v) :- expr(_, $Var(v)).
hasvar($Add(x,y), v) :- expr(_,$Add(x,y)), (hasvar(x,v) ; hasvar(y,v)).
```

From another perspective, this is a relative of "need sets" and magic sets.
The zipper here represents the implicit stack of an ordinary Imp interpreter. We also may need a first class map to actually run programs precisely
The transformation foo(firstclassmap) -> foo(i), map(i, k,v) is lossy in the presence of multiple executions. From an abstract interp persepctive this is not so bad.



## Reflection
### BitSets
```souffle
.type bitset <: unsigned
// Operations
#define BOT 0x0
//assuming 32 bit
#define TOP  0xFFFFFFFF 
#define SING(x) (0x1 bshl x)
#define UNION(x,y) (x bor y)
#define ADD(x,set) UNION(SING(x), set)
#define INTER(x,y) (x band y)
#define COMP(x) (TOP bxor x)
#define DIFF(x,y) (x bxor INTER(x,y))

// Predicates
#define ISEMPTY(x) (x = 0)
#define NONEMPTY(x) (x != 0)
#define SUBSET(x,y) ISEMPTY(DIFF(x,y))
#define ELEM(x, set) NONEMPTY(INTER(SING(x), set))

.decl test(l : symbol, b : bitset)
test("ex1", SING(1)).
test("ex1", SING(2)).
test("ex2", DIFF(set, SING(2))) :- test("ex1", set).
test(l,UNION(s1,s2)) :- test(l, s1), test(l,s2).
test(l,s1) <= test(l,s2) :- SUBSET(s1,s2).

.output test(IO=stdout)

```
```
#define FLAG0 0x0
#define FLAG1 0x2
#define FLAG2 0x4
```

#### Bitset reflection
Can I use bitsets to reflect? Yes. Up to 32 entries allows.
More if we use records of bitsets, n  * 32 element sets.


```souffle
.type bitset <: unsigned
// Operations
#define SING(x) (0x1 bshl x)
#define UNION(x,y) (x bor y)
#define INTER(x,y) (x band y)
#define DIFF(x,y) (x bxor INTER(x,y))

// Predicates
#define ISEMPTY(x) (x = 0)
#define NONEMPTY(x) (x != 0)
#define SUBSET(x,y) ISEMPTY(DIFF(x,y))
#define ELEM(x, set) NONEMPTY(INTER(SING(x), set))

.type findomain = A {} | B {} | C {}
.decl foo(a : findomain)
foo($A()).
foo($C()).

// reflection
.decl refl_foo(a : bitset)
refl_foo(SING(as(x, unsigned))) :- foo(x).
refl_foo(UNION(s1,s2)) :- refl_foo(s1), refl_foo(s2).
refl_foo(s1) <= refl_foo(s2) :- SUBSET(s1,s2).

// reify
.decl reify_foo(x : findomain)
reify_foo(as(x, findomain)) :- x = range(0,3), refl_foo(s), ELEM(x,s). // could make range 32 without hurting anything
.output reify_foo(IO=stdout)
.output refl_foo(IO=stdout)
```

Could we perhaps use sparse bitsets? If there are universes of 2^n we can encode into a record with unsigned representing if we a priori know limit of sparsity.
Possibly better is to use a lattice approximate reflection. Like factored over approximation.

```
factor_reflect(sing(arg1), sing(arg2)) :- rel(arg1, arg2).
```
The cartesian product of these sets over approximates `rel`. Rather reminds me of relational division.

Speculative idea: Could have reflection as a true primitive. User defined functors? Don't really get access to relations. 
We need persitent set data structures if we want to do this. Garbage collection? We could mark them as special reflective relations `.decl foo() reflective`
`reflect("rel_foo")`
Something like this.
```
rel reflect(string name){
   program.get_relation(name)
}
```
Oh, user defined functors woould support this `store(k,v, oldmap)` or `add(v, oldset)`. It would be nice if we could somehow just make sets pointers to souffle's structure themselves, or projections thereof? I mean what can you really do in that case?


Reflection by grouping.
```
reflect(group : unsigned, bitset)
reflect(n / 32, sing(n % 32)) :- rel(n)
```
Can the process be iterated?

We could build a binary search tree ADT and reflect to that. What does that really do though? Uhhh. Yeah That makes sense. ADTs are persistent data structures. Maybe something other than binary tree is most appropriate? It would make sense to make sure we have a canonical representation of a particular set. I don't think the record table gets garbage collected. So we might build a set for every subset of the relation. Not good.

Another possibility, reflect into a bloom filter via hashing. Kind of a fun "lattice"? Yeah it is right?

Reifying back into a relation
n lg n overhead:
need to define split macro. to split set in two. Maybe it takes the upper and lower range.

```
#define split(upper,lower,bs) ((-1 << lower) & (-1 >> upper) & bs)
.decl reify(size : unsigned, offset: unsigned, set : bitset)
reify(32, 0, n) :- bitset(n).
reify(n/2, m, bs1), reify(n/2,m + n/2, bs2) :- reify(n,m, bs), n > 1, bs1 = split(m, m + n/2 bs), bs2 = split(m+n/2, m + n, bs)
done(v) :- reify(1, v, bs), NONEMPTY(b)
```

Oh, of course you could straight up unroll it
```
#REIFY(r2, r1, n) r2(1) :- r1(bs), ELEM(n,bs)
// done(1) :- bitset(bs), ELEM(1,bs). 
REIFY(done,bitset,1).
REIFY(done,bitset,2).
REIFY(done,bitset,3).
// and so on
```

Or it could be componentized.

### Patricia Tries
[fillaitre](https://www.lri.fr/~filliatr/ftp/ocaml/ds/ptset.ml.html)
```souffle
.type ptrie = Nil {} 
            | Leaf {x : unsigned} 
            | Branch {prefix : unsigned, branchbit : unsigned, l : ptrie, r : ptrie}

.type Bool = False {} | True {}
/*
.decl mem(x : unsigned, t : ptrie, tf : Bool)
mem($Nil(), _, $False()). // not valid
*/
.decl add(x : unsigned, t : ptrie, t2 : ptrie)
add(x, $Empty(), $Leaf(x)).
add(x, $Leaf(x)), $Leaf(x)).

```
### BDDs
bddbdddb is a datalog that used binary decision diagrams as it's backing store. It's an interesting idea. BDDs are very powerful.

BDDs are a relaitve of hash consing.See [type safe modular hash consing](https://www.lri.fr/~filliatr/ftp/publis/hash-consing2.pdf) section 3.3

Souffle ADTs are a variety of hash cons.

```souffle
.type BDD = True {} | False {} | ITE {c : number, t : BDD , e : BDD}

bdd_and(x : BDD, y : BDD, z : BDD)
//bdd_and($True(), $True(), $True()).
//bdd_and($True(), $False(), $False()).
//bdd_and($False(), $True(), $False()).
//bdd_and($False(), $False(), $False()).
bdd_and(x,y, $False()) :- need_bdd_and(x, y), {y = $False() ; x = $False()}.
bdd_and(x,y, x) :- need_bdd_and(x, y), y = $True().
bdd_and(x,y, y) :- need_bdd_and(x, y), x = $True().
//bdd_and(x,y, $ITE( cx , ) ) :- need_bdd_and($ITE(cx, tx, ex), $ITE(cy,ty,ey)), cx < cy, bdd_and(tx,   ) .
//bdd_and(x,y, $ITE( cx , ) ) :- need_bdd_and($ITE(cx, tx, ex), $ITE(cy,ty,ey)), cx < cy, bdd_and(  ) .
bdd_and(x,x,x) :- need_bdd_and(x,x).
bdd_and(x,y,z) :- need_bdd_and(x,y), x = $ITE(cx, tx, ex), y = $ITE(cy,ty,ey), x != y,
      {
        cx < cy, bdd_and(tx, y, zx), bdd_and(xe, y, ze), zc = xc;
        cx = cy, bdd_and(tx, ty, zx), bdd_and(xe, ye, ze), zc = $ITE(cx, zt, ze);
        cx > xy, bdd_and(x, yt, zt), bdd_and(x, ye, ze), zc = yc
      }, z = $ITE(zc,zt,ze).
```

Wait... are bdds of the bits kind of like hash consed patricia trees?

## BogoSort
Hmmmm... Can I do this?

```souffle
.decl array(index : unsigned, n : number)
array(0,14)
array(1,934).
array(2,49).
array(3,-23209).

// permute
array(i+1,n) :- array(i,n), i < 3.
array(i-1,n) :- array(i,n), i > 0.

// subsume bad possibilities...?
array(i-1, n) <= array(i, n) :- i > 0, 
```
What about building a relation of pairs
```
pair(a,b) <= pair(b,a) :- b <= a, a <= b
```


bubble sort
```
// could use max over input iindices instead of N
#define N 4
.decl in(index : number, v : symbol)
in(2 , "a").
in(0 , "b").
in(1 , "c").
in(3 , "d").

proc(i, x1, t + 1), proc(i+1,y1, t + 1):- proc(i, x,t), proc(i+1, y, t), t%2 = i%2 , t < N * N, 
   (  x < y, x1 =x,y1 = y;  x >= y, x1 = y, y1 = x).

out(i,x) :- proc( i, x, N).
```

path based. Take shortest oriented edges. Graph is then 
```
v(1)
v(2)
v(3)

// shortest edges
edge(i,j) :- v(i), v(j), i < j.
edge(i,j) <= edge(i,k) :- k <= j.

//edge(i,i) :- min().
//edge(i,j) :-  edge(i,j)

path(0,i,i) :- min(i : v(i) ).
path(n+1,i,k) :- path(n, i,j), edge(j,k).

out(i,x) :- path(i,_,x).

```

Radix sort?

## Dynamic Programming
### Q learning
Grid world + subsumption / lattice.

## CHR
See note on prolog for more on CHR

Constraint handling rules have some similarity to datalog with subsumption and sometimes you can translate programs.
Datalog has set semantics, CHR has multiset semantics. Sometimes you add CHR rules to make set semantics
subsumption allows some deletion.

Timestamps and water marks?
max(t1,t2)+1  :- foo( , t1), bar(t2) 

:- watermark(t), foo(t1), , t1 < t
foo() <= foo() :- watermark(t)

deletion watermark?

DDlog has a multiset thing. Seems reasonable this is better for chr.

You can have multiset if you include justification/provenance fields. See section below. This also prevents refirings.

```
a() \ b(1) <=> guard | b(2)
\\ is similar to
b(2) :- a(), b(1), guard.
b(1) <=  b(2) :- a(), guard.

```

```souffle
/*
CHR: 
  a() \ b(1) <=> guard | b(2) 
is similar to
Datalog:
  b(2) :- a(), b(1), guard.
  b(1) <=  b(2) :- a(), guard.

Merge Sort in CHR, given values as next(start,Value)
next(A,B) \ next(A,C) <=> A<B,B<C | next(B,C).
*/
.decl next(a : number, b : number)
next(b,c) :- next(a,b), a < b, b < c, next(a,c).
next(a,c) <= next(b,c) :- next(a,b), a < b, b < c.

next(0,7). next(0,4). next(0,3).
.output next
/*
---------------
next
a       b
===============
0       3
3       4
4       7
===============
*/
```

## Lambda representation
What is the most appropriate way? Probably we want to implement some kind of machine flavored implementation.
Or maybe a graph like representation.

I could literally do hash cons modulo alpha. I can dor xor trick. Hmm. PosTree is a trie.

Could make user defined functor for substition.

I could make udf for normalization. And memoize into a choice domain?

Combinators

lambda datalog. Pattern matching on ground lambda terms is good.

Yihong's let and fresh.
Might still need first class maps for environements.

## Parsing
What about good error parsing? It feels like the flexibility of a datalog could be nice. It's sort of why-not provenance.

[CYK Parsing](https://en.wikipedia.org/wiki/CYK_algorithm) is an example of dynamic programming.
Earley = magic set of CYK. Doing it on demand

`substr` makes this feasible. This unfortuantely is going to reintern the string though. So hard to believe it'll ever be efficient.


```souffle

.decl str(x : symbol)
.type char <: symbol
.decl chars(x : symbol, i : number, c : symbol )
chars(x, i, c) :- str(x), i = range(0, strlen(x)), c = substr(x, i, 1).

str("())()").
str("()()").
str("((()))").
//.output chars(IO=stdout)


.decl parens(x : symbol, i : number, j : number)
parens(x, i, i) :- str(x), i = range(0, strlen(x)+1).

//parens(x, i-1, j+1) :- i >= 1, "(" = substr(x,i-1,1), parens(x, i, j), ")" = substr(x,j,1).
parens(x, i-1, j+1) :- i >= 1, chars(x,i-1,"("), parens(x, i, j), chars(x, j, ")").

// pretty expensive
#define cat3(x,y,z) cat(x,cat(y,z))
#define cat4(x,y,z,w) cat(x, cat3(y,z,w))
parens(x, i-1,j+1) :- i >= 1, parens(x,i,j), substr(x,i-1,j-i+2) = cat3("(", substr(x,i,j-i) , ")").

parens(x, i, k) :- parens(x,i,j), parens(x,j,k).
.output parens(IO=stdout)
.decl parsed(x : symbol)
parsed(x) :- parens(x, 0, strlen(x)).
.output parsed(IO=stdout)

.type myparens = Append {x :myparens , y : myparens} | Parens {x : myparens} | Empty {}

.decl parens2(x : symbol, i : number, j : number, p : myparens)
// P --> eps
parens2(x, i, i, $Empty()) :- str(x), i = range(0, strlen(x)+1).
// P --> (P)
parens2(x, i-1, j+1, $Parens(a)) :- i >= 1, chars(x,i-1,"("), parens2(x, i, j, a), chars(x, j, ")").
// P --> PP
parens2(x, i, k, $Append(a,b)) :- parens2(x,i,j, a), parens2(x,j,k, b), a != $Empty(), b != $Empty().

.decl parsed2(x : symbol, p : myparens)
parsed2(x, a) :- parens2(x, 0, strlen(x), a).
.output parsed2(IO=stdout)



```




Chomsky normal form. Only allow epsilon at start

Magic set. The query we actuall want in `parsed(x)`.
needparens(x,i,j) guard predicate in front. But so what


I
```souffle
#define cat3(x,y,z) cat(x,cat(y,z))
#define cat4(x,y,z,w) cat(x, cat3(y,z,w))
.decl str(x : symbol)
.decl needparens(x : symbol)
.decl parens(x : symbol)
str("()()").
str("()(()())").
// inefficient, but cleaner to write. Don't have to track i,j
// Maybe it's not even that inefficient when you consider semi naive
// We get sharing between different parses also.
needparens(y) :- str(x), i = range(0,strlen(x)), len = range(1,strlen(x) - i + 1), y = substr(x, i, len).
parens("").
parens(y) :- needparens(y), parens(x), y = cat3("(", x, ")").
parens(z) :- needparens(z), parens(x), parens(y), z = cat(x,y).
.output parens(IO=stdout)

// Could also make more efficient if we use smarter needsparens.
// should only propagate needs parens if the first and last characters are parens or something.
// We're also filling up our symbol table here. Eh.

// If I donthave the needsparens guard, this wouldn't terminate. cat3 would keep making new strings.

```

```souffle
#define cat3(x,y,z) cat(x,cat(y,z))
.type parens =  Empty {} | Parens {x : parens} | Append {x : parens, y : parens} 
.decl str(x : symbol)
.decl needparse(x : symbol)
.decl parses(x : symbol, p : parens)
str("()(()())").
needparse(y) :- str(x), i = range(0,strlen(x)), len = range(1,strlen(x) - i + 1), y = substr(x, i, len).
parses("", $Empty()). // P --> eps
parses(y, $Parens(p)) :- needparse(y), parses(x,p), y = cat3("(", x, ")"). // P --> (P)
parses(z, $Append(px,py)) :- needparse(z), parses(x,px), parses(y,py), z = cat(x,y), // P --> PP
                             px != $Empty(), py != $Empty(). // For termination
.output parses(IO=stdout)
/*x       p
===============
()(()())        $Append($Parens($Empty), $Parens($Append($Parens($Empty), $Parens($Empty))))
                $Empty
()              $Parens($Empty)
(()())          $Parens($Append($Parens($Empty), $Parens($Empty)))
()()            $Append($Parens($Empty), $Parens($Empty)) */
```

Easy way to regexp?
If I want identifiers
```python
import string
print(" ".join([f"lower(\"{c}\")." for c in string.ascii_lowercase  ]))
print(" ".join([f"upper(\"{c}\")." for c in string.ascii_uppercase  ]))
print(" ".join([f"digit(\"{c}\")." for c in range(10)  ]))
```

```souffle
.decl lower(c : symbol)
.decl upper(c : symbol)
.decl char(c : symbol)
.decl digit(c : symbol)
lower("a"). lower("b"). lower("c"). lower("d"). lower("e"). lower("f"). lower("g"). lower("h"). lower("i"). lower("j"). lower("k"). lower("l"). lower("m"). lower("n"). lower("o"). lower("p"). lower("q"). lower("r"). lower("s"). lower("t"). lower("u"). lower("v"). lower("w"). lower("x"). lower("y"). lower("z").
upper("A"). upper("B"). upper("C"). upper("D"). upper("E"). upper("F"). upper("G"). upper("H"). upper("I"). upper("J"). upper("K"). upper("L"). upper("M"). upper("N"). upper("O"). upper("P"). upper("Q"). upper("R"). upper("S"). upper("T"). upper("U"). upper("V"). upper("W"). upper("X"). upper("Y"). upper("Z").
digit("0"). digit("1"). digit("2"). digit("3"). digit("4"). digit("5"). digit("6"). digit("7"). digit("8"). digit("9").

alpha(c) :- lower(c) ; upper(c).


```


Earley parsing. Put the carefullness in needparse instead
```souffle
#define cat3(x,y,z) cat(x,cat(y,z))
#define FIRST(rem) substr(rem,0,1)
#define LAST(rem) substr(rem,strlen(rem)-1,1)

.type parens =  Empty {} | Parens {x : parens} | Append {x : parens, y : parens} 
.decl str(x : symbol)
.decl needparse(x : symbol)
.decl parses(x : symbol, p : parens)
needparse("()(()())").
needparse(y) :- needparse(x), FIRST(x) = "(", LAST(x) = ")", y = substr(x,1,strlen(x)-2).
// only one iterator so that's nice I guess. And only because it's such a nasty rule
needparse(y), needparse(z) :- needparse(x), i = range(0,strlen(x)), y = substr(x,0,i), z = substr(x,i,strlen(x)-i). 



parses("", $Empty()). // P --> eps
parses(y, $Parens(p)) :- needparse(y), parses(x,p), y = cat3("(", x, ")"). // P --> (P)
parses(z, $Append(px,py)) :- needparse(z), parses(x,px), parses(y,py), z = cat(x,y), // P --> PP
                             px != $Empty(), py != $Empty(). // For termination
.output parses(IO=stdout)
```

```souffle

.type list_sexp = [hd : sexp, tl : list_sexp]
.type sexp = List {x : list_sexp} | Atom {x : symbol}

word(s,i,j) :- chars(s, i-1, c), alpha(c), word(s, i, j).


```


DCG
parser combinator
We need like a whole stack then. Blugh
```souffle
#define NEXT(rem) substr(rem,1,strlen(rem1)-1)
#define FIRST(rem) substr(rem1,0,1)
parse(x,NEXT(rem)) :- parse(x,rem1), FIRST(rem) = ")".


// regexp
#define NEXT(rem) substr(rem,1,strlen(rem1)-1)
#define FIRST(rem) substr(rem1,0,1)
#define FIRST(rem, c) substr(rem1,0,1) = c

#define STAR(class) parse(x,NEXT(rem)) :- parse(x,rem1), FIRST(rem) = c, class(c).
starupper(x,NEXT(rem)) :- starupper(x,rem1), FIRST(rem) = c, upper(c).

// as transition system
recog("nextstate",x, rem) :- recog("upper", x, rem) , FIRST(rem) = c, !upper(c), 

// as transition system. don't need x really. uhhh. Yes we do. We need a bottom up transform then.
recog("nextstate", rem) :- recog("upper", rem) , FIRST(rem) = c, !upper(c), 



```
So it seems like this is a general transfomation. I can exchange a global context parameter x that I dig into with substr for a need predicate.
The two are uncoupled. Recurse over the thing first to reak it up, then bottom up the pieces. Don't do in one pass.





- [earley parsing](https://github.com/souffle-lang/souffle/blob/master/tests/example/earley/earley.dl)
- [parser in datalog](https://homes.cs.washington.edu/~bodik/ucb/cs164/sp13/lectures/09-Datalog-CYK-Earley-sp13.pdf) bottom up parsing
- [parsing and generation as datalog queries](https://aclanthology.org/P07-1023.pdf)
- [DCGs + memoizing = Packrat Parsing](https://mercurylang.org/documentation/papers/packrat.pdf)

## Hilog
```souffle
.type binreltag = Edge {} | Star {r : binreltag}
// Closure is a bad name for this example

.decl binrel( r : binreltag, x : number, y : number)
binrel($Star(r), x, y) :- needstar(r), binrel(r, x, y). // hmm this'll never stop becaus we'll keep starring stars. Perhaps needs to be predicated upon need.
binrel($Star(r), x, z) :- needstar(r), binrel(r, x, y), binrel($Star(r), y, z).

.decl needstar(r : binreltag)
needstar($Edge()).

binrel($Edge(), 1, 2).
binrel($Edge(), 2, 3).
binrel($Edge(), 3, 4).

.output binrel(IO=stdout)
```
It may also be nice to make a universal type (for which number actually serves pretty well?).


## meta circular interpreter
See extensive prolog literature on meta circular intepreters
https://www.metalevel.at/acomip/

```souffle
//.type Pred = [name : symbol, args : TList]
//.type Clause = {head : }
.type pat = Var {x : symbol} | Lit { x : number}
.type relpat = R0 { rel : symbol } | R1 {rel : symbol, x : pat} // | R2 {}
.type body = [ hd : relpay, tl : body ]

// .type body = Conj {a : body, b : body} | Pat {p : relpat}
// or inline 

// alternatively make clause a data structure. But whatever. clause becomes a global object.
.decl clause(hd : relpat, body : body)
clause(hd, body).
// clause(program, hd, body) for multiple programs

.type ctx = [ snoc : body, cons : body ]


// Probably shouldn't be so controlling about match
match(   nextctx) :- match($R1(r, $Lit(x)), ctx), unaryrel(r, x)
headstate(   ) :- pat_in(body, $R1($Var(x)) ), headstate($R1(r, $Var(x)) , body)
// no but you need more state than just what's in the head. edge(x,y), path(y,z) needs y around for consistency

// eq( body , , ). for union find? 

:- match(_snoc, nil)
           :- $R1

.type varbind = [x : number , vbind ; varbind ]
index( varbind, n : unsigned, x : number)
index()
// require labelling variables in order they appear to simplify
// Pre Normalize out unification?
(  ctx, $R1(r, $Var())  ,varbind), unrel(r,y), index(varbind ,n,$Var())
(  ctx, $R1(r, $Var(n))  ,varbind), index( ,n,$Lit(y)), unrel(r, y).


```

## Equality Saturation
See blog posts

egglog

## Term Rewriting
It's similar to "path" in some respects.

Maybe don't bother with "t" parameter?

```
.type Term = Lit {x : signed} | Add {a : Term, b : Term} | Var {x : symbol}
.decl simplify(t : Term, t2 : Term)

simplify(t,t2) <= simplify(t,t3) :- t2 <= t3.

// recursive cases
simplify(t,$Add(ta2,tb2)) :- simplify(t, $Add(ta,tb)), simplify(ta, ta2), simplify(tb, tb2).

// patterns
simplify(t, a) :- term(t), t = $Add($Lit(0), a).

// should have the analog of "edge" here
simplify(t,t2) :- simplify(t,t1), simplify(t1,t2).
//simplify(t0,a) :- simplify(t0,t), t = $Add($Lit(0),a).


simplify(t,t) :- term(t).

//initiliaze
term(t) :- start(t).
term(a), term(b) :- term($Add(a,b)).

```



## Graph Algorithms
Graph form of monoidal category in soufflé?
Graph rewriting? We have graph matching. How do we say some subgraph is better than some other.
Graph combinator reduction?

## Translating Imperative Programs
similar to translating to functional style.
Figure out the state. Make them all parameters to relation
One style is:
```
foo(nextstate) :- foo(state).
```

You need program counter to do in this style.
Instead can use store style. Every statement of program gets own relation. Need to pass entire store

```
line2(newx) :- line1(x), newx = x + 1.
line3(x,y) :- line2(x), y = x * 3
```

We're edging on dataflow analysis at this point.

```souffle
line2("x", x + 1):- line1("x", x).
line3("x",x) :- line2("x",x).
line3("y", x *3) :- line2("x",x).
```

Note the big difference here though. We have _factored_ the old line3 relation. The new version is not capable of storing seperate runs without dataloss. We no longer would know which "x" corresponded to which "y".
This is of some relation to lossless joins and things in database theory.
This factoring can be useful as an overapproximation technique.

## Translating functional programs 
Lift function to relation by making return value part of relation
fib(n) becomes fib(b,ret)

Datalog is bottom up. You need to rip apart all the recursive calls. What is the most principled way to see this? Principled transformation to bottom up call?
```souffle
fact(0,1).
fact(1,1).
fact(n + 1, (n+1) * m) :- fact(n, m), n < 10.
```

I like the build a table of all possible arguments.
```souffle
needed(n).
needed(n - 1) :- needed(n), n > 0. 
fact(0,1).
fact(1,1).
fact(n + 1, (n+1) * m) :- fact(n, m), needed(n).
```
For ADTs this ends up being a table of all subterms.

Is needed a representation of call frames maybe?


## Model Checking
See Chapter 8 State-Space Search with Tabled Logic Programs

Farmer puzzle

Die Hard puzzle
```souffle
.pragma "provenance" "explain"
.decl reach(big : unsigned, small : unsigned)
reach(0,0).
// move water small to big
reach(big + small, 0) :- reach(big,small), big + small <= 5.
reach(5,  small - (5 - big)) :- reach(big,small), !big + small <= 5.
// move water big to small
reach(0, big + small) :- reach(big,small), big + small <= 3.
reach(big  - (3 - small),  3) :- reach(big,small), !big + small <= 3.
// empty big
reach(0, small) :- reach(_,small).
// empty small
reach(big,0) :- reach(big,_).
// fill big
reach(5, small) :- reach(_,small).
// fill small
reach(big,3) :- reach(big,_).

.decl big_is_4(small : unsigned)
big_is_4(small) :- reach(4,small).
.output big_is_4(IO=stdout)
/*
---------------
big_is_4
small
===============
0
3
===============
Explain is invoked.
Enter command > setdepth 10
Depth is now 10
Enter command > explain big_is_4(3)
reach(0, 0)                          
--------(R8)                         
reach(5, 0)  5 > 3                   
---------------(R5)                  
    reach(2, 3)                      
----------------(R7)                 
    reach(2, 0)      2 <= 3          
------------------------(R4)         
        reach(0, 2)                  
-------------------------(R8)        
         reach(5, 2)          7 > 3  
--------------------------------(R5) 
            reach(4, 3)              
---------------------------------(R1)
             big_is_4(3)             
*/
```


## Timestamping 
Transtion systems. All possible executions. Model Checking.
Dedalus
```souffle
.decl foo(a : number, b : number, time : unsigned)
foo(a,b,t) <= foo(a1,b1,t2) :- t < t2. //possibly allow subsumption of new states only. This won't build all possible paths though.
foo(x,y,t) :- bar(x,t1), biz(y, t2), t = max(t1,t2) + 1.

reached(a,b) :- foo(a,b,t). // how will this interact with subsumption? Why even bother timestamping if you just want reached.
```

Using datalog to control reactive systems

```souffle
//.pragma "libraries" "libc.so.6"
.functor time(): unsigned // unix system call
.decl timestamp(t : unsigned)
timestamp(@time()) :- true.
.output timestamp(IO=stdout)
```
Ah I see 
<https://github.com/souffle-lang/souffle/blob/d1522e06c6e99c259951dc348689a77fa5f5c932/src/interpreter/Engine.cpp#L381>
I can't open libc.so.6 because this string is being made in this way. libc.so is not the right kind of file.

[Integrity Constraints for Microcontroller Programming in Datalog](https://users.informatik.uni-halle.de/~brass/micrologS/) arduino timestamping, external pin relations. pretty cool.
[Microlog - A Datalog for Microcontrollers and other Interactive Systems](https://dbs.informatik.uni-halle.de/microlog/)

[Dedalus](https://www2.eecs.berkeley.edu/Pubs/TechRpts/2009/EECS-2009-173.pdf) http://bloom-lang.net/faq/
Timely dataflow

## Theorem Proving
A lot of these techniques are taken from interpeting the Lambda Prolog rules.
Question: Is it possible to consider static analysis over lambda prolog to systematically understand some of these tricks?

Consider Jens Otten tutorial

### Skolemization for Existential Heads
$ \forall x, \psi(x) \implies \exists y, \phi(x,y)$ can be replaced with 
$ \forall x, \psi(x) \implies \phi(x,y(x))$ where y is now the function that selects the approproate existential value. You can represent function symbols of this kind wtih ADTs. ADTs are great because they know if you've already made the symbol or not.
```
.type Skolemized = Y { x : xtype } | Lit { a : ytype}
```
An alternative semantics might be to try

$ \forall x, \psi(x) \implies \phi(x,autoinc())$ but then the thing will never terminate.

### Goals / Queries
Souffle doesn't quite have a notion of goal. But `.output` relations are the analog of goals/queries.
The magic set transform works this way.

If in prolog you would write
```
?- foo(X), bar(X,Y,7).
```
as a query, you can do the same thing by naming this query

```souffle
myquery(x,y) :- foo(x), bar(x,y,7).
.output myquery
```

In theorem proving, your axioms because clauses, and your to-be-proved theorem will become a goal of this variety.

### Uncurrying 
A logical formula of the form
$p \implies q \implies r$
is equivalent to 
$p \land q \implies r$
`r :- p, q`
So you can express axioms of this type by uncurrying.

A alternative approach to dealing with the same class of formula is "defunctionalization". Make predicates for each partial application of a horn clause.

```
part_rule1(x) :- p(x)
r(z) :- part_rule(x), q()
```

### Higher Order Clauses
$ (p \implies q) \implies r$ is a different animal from the above.
I'm not super sure how to deal with these.
I'd suggest that predicates need to be extended with a notion of context. Higher order rules like these are interpetted as something like

```
r(ctx_without_p) :- q(ctx_with_p)
```

What precisely I mean by ctx is unclear here. It seems like I'd need to internalize relations and or clauses into the language of datalog itself.
Contexts do have a partial order. Derivations in weaker contexts can subsume strong ones.
I suspect we are running into serious problems where we are just lacking the appropriate primitive to do this efficiently.

### Universal Quantifier
$\forall x, foo(x)$ is not a probem in unification based prolog, but it is in pattern matching based datalog where everything needs to be grounded in the head by the body of a clause.

Bounded quantification is one solution.
$\forall x \elem [0,10], foo(x)$
`foo(x) :- x = range(0,10)`

Not particularly satisfying.
We might also try to globally collect up all constants of that type. This is similar to the above, but a slightly diffferent flavor.
`foo(x) :- allsymbols(x)`

`allsymbols` can be manually instantiated as ground facts or generated from any predicate that uses symbol of said type
```
allsymbols(x) :- biz(x,_,_).
allsymbols(x) :- biz(_,_,x).
allsymbols(x) :- baz(x,_). 
```


Some foralls that are part of rules can just be dropped. $\forall x, \phi(x) \implies \phi(x)$. I suppose this could be considered an optimization of the `allsymbols` strategy.

### Categorical Example

```souffle
// these constructors are actually the skolemizaion of axioms
.type Morph = Comp {f : Morph, g : Morph} | Id {a : Ob} | M {f : symbol}
.type Ob <: symbol

.decl ob(a : symbol)

.decl eq(f : Morph, g : Morph) eqrel
.decl hom(f : Morph, a : Ob, b : Ob)

// category axioms
// identity morphism exists
hom($Id(a), a, a) :- ob(a).
eq(f, $Comp(f,$Id(b))), eq($Comp($Id(a),f), f) :- hom(f,a,b).
// composition exists
hom($Comp(f,g),a,c) :- hom(f, a, b), hom(g, b, c).//, f != $Id(_), g != $Id(_).
// associativity axiom rewrite rules
eq(fgh2, fgh), hom(fgh2, a, b) :- hom(fgh, a, b), fgh = $Comp(f,$Comp(g,h)), $Comp($Comp(f,g),h) = fgh2.
eq(fgh2, fgh), hom(fgh, a, b) :- hom(fgh2, a, b), fgh = $Comp(f,$Comp(g,h)), $Comp($Comp(f,g),h) = fgh2.
 

// typing rule guarded on eq
hom($Comp(f,g), a, c):- eq($Comp(f,g), _), hom(f, a, b), hom(g, b, c).
// Just filling out stuff.
eq(f,f), ob(a), ob(b) :- hom(f,a,b).

/*
.decl depth(t : Morph, n : unsigned)
depth($M(f), 1) :- hom($M(f), _, _).
depth($Id(a), 1) :- hom($Id(a), _, _).
depth($Comp(f,g), max(m,n) + 1) :- hom($Comp(f,g), _, _), depth(f,n), depth(g,m).
*/

hom(f,a,b) <= hom(f2,a,b) :- eq(f,f2), depth(f2, d2), depth(f,d1),  d2 <= d1.

hom($M("f"),"a","b").
hom($M("g"),"b","c").

.limitsize hom(n=15)
.output hom(IO=stdout)
```

Hmm. Comp(Id, f) is going off the rails. Any loop will. Can subsume on term size? Not clear who wins subsumption vs building bigger. Tag size inside of term?

Mayybe it's worth it to do Comp { symbol, morph} list style. Hard to do.
Could block composition rule on Id. Kind of a cheap shot

## Typeclass resolution.
See Lean paper Tabling Typeclasses
See Chalk (which uses datafrog?) https://github.com/rust-lang/chalk

Write typeclass rules as datalog/prolog clauses. The provenance tree is enough to actually construct the type class instances.


## Borrow Checker
Hmm the borrow checker is seperate from the trait engine chalk probably
See ascent paper which compares itself with datafrog based polonius
Polonius https://www.youtube.com/watch?v=_agDeiWek8w
switches polonius from diff dataflow to datafrog https://github.com/rust-lang/polonius/pull/36#issuecomment-390393717
https://github.com/frankmcsherry/blog/blob/master/posts/2018-05-19.md datafrog blog post
[An alias-based formulation of the borrow checker](http://smallcultfollowing.com/babysteps/blog/2018/04/27/an-alias-based-formulation-of-the-borrow-checker/) soufle datalog rules
[rust board discussion](https://internals.rust-lang.org/t/blog-post-an-alias-based-formulation-of-the-borrow-checker/7411)
"NLL"? Non lexical liftetimes https://stackoverflow.com/questions/50251487/what-are-non-lexical-lifetimes
This is perhaps related to alias analysis? But maybe not.
Also perhaps to subtyping.

region variables.
lifetimes
```souffle
// just collected up from post above

.decl cfg_edge(P:point, Q:point)
.input cfg_edge


.decl subset(R1:region, R2:region, P:point)
// Rule subset1
subset(R1, R2, P) :- base_subset(R1, R2, P).
// Rule subset2
subset(R1, R3, P) :- subset(R1, R2, P), subset(R2, R3, P).
// Rule subset3 (version 1)
subset(R1, R2, Q) :- subset(R1, R2, P), cfg_edge(P, Q).

.decl borrow_region(R:region, L:loan, P:point)
.input borrow_region

.decl region_live_at(R:region, P:point)
.input region_live_at

.decl requires(R:region, L:loan, P:point)
// Rule requires1
requires(R, L, P) :- borrow_region(R, L, P).
// Rule requires2
requires(R2, L, P) :- requires(R1, L, P), subset(R1, R2, P).
// Rule requires3 (version 1)
requires(R, L, Q) :-
  requires(R, L, P),
  !killed(L, P),
  cfg_edge(P, Q).

.decl killed(L:loan, P:point)
.input killed

.decl invalidates(P:point, L:loan)
.input invalidates

.decl loan_live_at(R:region, P:point)

// Rule loan_live_at1
loan_live_at(L, P) :-
  region_live_at(R, P),
  requires(R, L, P).

.decl error(P:point)

// Rule error1
error(P) :-
  invalidates(P, L),
  loan_live_at(L, P).

// Rule subset3 (version 2)
subset(R1, R2, Q) :-
  subset(R1, R2, P),
  cfg_edge(P, Q),
  region_live_at(R1, Q), // new 
  region_live_at(R2, Q). // new

// Rule requires3 (version 2)
requires(R, L, Q) :-
  requires(R, L, P),
  !killed(L, P),
  cfg_edge(P, Q),
  region_live_at(R, Q). // new
```

[polonius and region errors](http://smallcultfollowing.com/babysteps/blog/2019/01/17/polonius-and-region-errors/)
A sequel to the above post with other souffle rules

[Polonius and the case of the hereditary harrop predicate](http://smallcultfollowing.com/babysteps/blog/2019/01/21/hereditary-harrop-region-constraints/)
Hmm... So he's mixing harrop, lifetimes, datalog. My kinda guy.

[lifetimes.lifetime inference in souffle ](https://github.com/rljacobson/lifetimes)
## Type checking / inferring
Related of course to the above.

```souffle
.type type = Unit {} | Int {} | Bool {} | List {a : type} | Maybe {a : type} | Sum {a : type, b : type} | Prod {a : type, b : type}
.type term = TT {} | TInt { x : number} | True {} | False {} | Nil {} | Cons { hd : term, tl : term } | None {} | Some {x : term}
   | Annot {t : term, ty : type} | Var { n : unsigned} | Lam {body : term} | App {f : term, x : term}

//.type ctx = [ t : term, t:type, g : ctx ] 
.type ctx = [ ty:type, g : ctx ]   // don't need variable if we're doing de bruijn


//| $GNil {} $GCons { t :term, ty : type, ctx } 


/*
hastype($TT(), $Unit()).
hastype($TInt(n), $Int()) :- n = range(1,10). // cheating a little
hastype($True(),$Bool()).
hastype($False(), $Bool()).
*/
.decl hastype(t : term , ty : type) // mode++ sort of
.decl infertype(t : term) // mode -+ top down
.decl checktype(t : term, ty : type) // mode -- topdown
.decl prove(ty:type) // mode +-
// the proof provenance of hastype() will basically mirror the lambda term anyhow.
// This perhaps shows the parameter is unnecessary / inefficient.
// We could instead record the rule used and subsumption to shortest one.

// The only bottom up mode is ++ since we don't have non ground terms.


hastype(t, $Int()) :- infertype(t), t = $TInt(_).

// annotation rule
checktype(t, ty) :- infertype($Annot(t,ty)).

// Sub rule. Doesn't hurt anything
infertype(t) :- checktype(t,_).
hastype(t,b) :- hastype(t,a) , eq(a,b).


hastype($TT(), $Unit()) :- checktype($TT(), $Unit()).

checktype([ a , ctx], body, b) :- checktype(ctx, $Lam(body), $Arr(a,b)).

// Var=> rule
hastype( ctx, $Var(0), t) :- infertype(ctx, $Var(0)), ctx = [t,_].
// This is probably not how to do it.
hastype() :- infertype(ctx, $Var(n)), index(ctx, n, t).
needindex(ctx,n) :- infertype(ctx, $Var(n)).
infertype(ctx, $Var(n-1)) :- infertype([_, ctx], $Var(n)), n != 0.

// Can we reify the ctx into a relation? possibly
// and insert immediately alos when we create the context.
inctx([a,ctx], a) :- checktype($Lam(body), )
inctx([a,ctx], x) :- inctx([a,ctx], _ ), inctx(ctx, x).

index([a,ctx], 0. a) :- checktype($Lam(body), )
index([a,ctx], n + 1, x) :- index([a,ctx], _, _), index(ctx, n, x).

// This part is a mess. Would not using debruijn be better somehow?

```
[bidirectional typing](https://arxiv.org/pdf/1908.05839.pdf)
I suppose bidi checking feels nice because we are already used to thinking of the different modes as different predicates. We also need to make these distinctions for magic set transform

[Rust lifetime analysis written in souffle](https://github.com/rljacobson/lifetimes)


eqrel for hindley milner? Yihong had something like this
souffle-z3 for refinement typing?


## Datalog Decompilers
[gigahorse](https://github.com/nevillegrech/gigahorse-toolchain) - decompiler for smart contracts based on souffle
grammatech
Dr lojekyll



## CRDTs
CRDT are a latticy based structure. It makes sense that it might be realted or modellable in datalog

[expressing crdts as queries using datalog](https://speakerdeck.com/ept/data-structures-as-queries-expressing-crdts-using-datalog)
https://github.com/frankmcsherry/dynamic-datalog/blob/master/problems/crdt/query.dl souffle example
https://github.com/frankmcsherry/dynamic-datalog

## MultiSet Semantics
If you give a reason for each tuple, you can get multiset semantics.

paths in a dag
```souffle
.type reason = Base {n : number} | Trans { x : reason, y : reason}

.decl edge(n : number, m : number, r : reason)
edge(1,2, $Base(0)).
edge(2,3, $Base(1)).
edge(1,3, $Base(2)).
.decl path(n : number, m : number, r : reason)
path(i,j, r) :- edge(i,j,r).
path(i,k,$Trans(x,y)) :- edge(i,j,x), path(j,k,y).

.output path

```

If you start subsumpting these reasons you get something similar to provenance as explained above in subsumption.

## Access Control Policies

[Is Datalog a good language for authorization?](https://neilmadden.blog/2022/02/19/is-datalog-a-good-language-for-authorization/)
[open policy language rego](https://www.openpolicyagent.org/docs/latest/policy-language/)
[polar and oso](https://docs.osohq.com/learn/polar-foundations.html#the-search-procedure)
[biscuit](https://www.biscuitsec.org/)
[Datalog with Constraints: A Foundation for Trust Management Languages](https://crypto.stanford.edu/~ninghui/papers/cdatalog_padl03.pdf)
[Specifying and Reasoning about Dynamic Access-Control Policies Daniel J. Dougherty,1 Kathi Fisler,1 and Shriram Krishnamurthi 2](https://web.cs.wpi.edu/~dd/publications/ijcar06.pdf)
googlew "access control datalog" you get a bunch of hits. The references in these paper

description logics https://www.cs.man.ac.uk/~ezolin/dl/

AWS zelkova is not datalog

Differential dataflow useful?
vs alloy vs tla+ vs smt?

[souffle example](https://github.com/souffle-lang/souffle/blob/master/tests/example/access-policy/access-policy.dl)
## Make
Build systems like make a logic programing rukles
[lpmake for ciao](https://github.com/ciao-lang/lpmake/blob/master/examples/latex/Makefile.pl)
[Propositions as Filenames, Builds as Proofs: The Essence of Make](https://bentnib.org/posts/2015-04-17-propositions-as-filenames-essence-of-make.html)

CSS is prolog
https://twitter.com/soundly_typed/status/1513500166359298048?s=20&t=-ertSPtY87GogVCFq4f-Rw 
# Topics
## Provenance
[Explaining Outputs in Modern Data Analytics∗](http://www.vldb.org/pvldb/vol9/p1137-chothia.pdf) prvoencnace in differential dataflow <https://github.com/frankmcsherry/explanation> <https://github.com/frankmcsherry/blog/blob/master/posts/2016-03-27.md>

[decalarative datalog debugging for mere mortals](https://yanniss.github.io/DeclarativeDebugging.pdf)

## Semi Naive Eavluation
I remember a time when semi naive seemed pretty cryptic to me. I still amnot sure I understand it perfectly, but I have crossed the threshld 

Naive evaluations only needs one table per relation. You can keep track of if there is anything to do by checking whether you find new tuples as you go along.
You could do it instead with two tables
- old
- new
  
And then at the final step, take the set `old \ new` , see if it is empty for termination check, and add it into old


For every logical relation you need to keep 3 tables
- old (stable)
- delta (recent)
- new (to_add)
You need these three because you need a place to put new facts, but also you want to keep the most recent updated tuples as a seperate thing.
`delta = new \ old`


## Datalog+- and the chase
[Datalog+-](https://dl.acm.org/doi/pdf/10.1145/1514894.1514897) A Unified Approach to Ontologies and Integrity Constraints. Integraes datalog with equality and tuple generating dependencies. 
[Datalog+- questions and answers](https://www.aaai.org/ocs/index.php/KR/KR14/paper/viewFile/7965/7972)
- weakly acyclic
- guarded - one relation holds all atoms
- sticky


[DLV](https://en.wikipedia.org/wiki/DLV) datalog with disjunction. 
https://www.dlvsystem.it/dlvsite/dlv-user-manual/ 
constraints - empty headed rules...? I've also seen them as `! :- ` in dglp
some funky features here. I wonder what the execution semantics is. Maybe disjunctive heads go in constraint store?

negation as failure vs stable model

## Tabling
See prolog tabling
Tabling in prolog leads to something very similar in power to the memoizing datalog. however, you still have unification and logic variables, so it is not clear it is truly equivalent.

## Descriptive Complexity and Least Fiexed Point Logic

[https://en.wikipedia.org/wiki/Fixed-point_logic#Least_fixed-point_logic](https://en.wikipedia.org/wiki/Fixed-point_logic#Least_fixed-point_logic) descriptive complexity theory says datalog is same thing as first order logic with fixpoints. Curious because datalog is also in some sense restricted horn clauses whereas this is saying in another sense it is full FO + fixpoint. 



## Push based Datalog
[Brass's website](https://users.informatik.uni-halle.de/~brass/)
[push based datalog](https://users.informatik.uni-halle.de/~brass/push/talks/inap17.pdf)
[push method](https://users.informatik.uni-halle.de/~brass/push/)
push method ~ like seminaive of only one fact? Hmm. Interesting.
function calls correpond to heads. They memoize. Then they push themselves to any location predicate appears in body. Cute.
This gets you something like seminaive eval.
hmm. binding patterns are related to map vs set vs iterator storage.
This might lend itself really nicely to an embedded datalog. datakanren.
minikanren makes the horn clause aspect more hidden. It heavily uses the function call mechanisms of the host language for heads.
This uses host languae mechanism for bodys. It kind of has an object oriented feel for some reason to me. relations need to support call and iterate.
There's this big fixpoint.
Many language already support some kind of auto memoization.
```
class Rel():
  def __init__(self,name,arity):
  def __call__():
  def __iter__():
    # register as usage site here?
 @memo
 def f(x,y):
  
class Rule():

```

## Incremental / Differential Datalog
See DDlog.
See Database/Streaming

[differential dataflow v datalog](https://github.com/frankmcsherry/blog/blob/master/posts/2016-06-21.md) Uses magic sets in incrmenetal system in a cool way. Datalog is dataflow system with giant fixpoint around it. Generic join in a rust macro

Szabo https://szabta89.github.io/publications.html  [thesis](https://openscience.ub.uni-mainz.de/handle/20.500.12030/5617)

[Incremental Datalog with Differential Dataflows blog](https://www.nikolasgoebel.com/2018/09/13/incremental-datalog.html)
3df https://github.com/comnik/declarative-dataflow https://www.youtube.com/watch?v=CuSyVILzGDQ

https://www.clockworks.io/en/blog/ I guess this is a company / consulting service associated with differential dataflow.


Differential Dataflow is kind of semi naive on steroids. Instead of just having a totally ordered iteration time, it keeps a partially ordered set of previous times. This means we have to store more than just good, new, delta. We have to store a bunch of deltas until we can coalesce them.

Timestamps kind of are like reference counts or arena cleanup. They can trigger caolascing, compaction, or gabarge collection events.

Incrmenetal dataflow is semi naive without the fixpoint. Instead the deltas are coming in from outside in a streaming like situation.

Hmm. Do queries go backwards? A lens? holy shit is magic set a lens?


Adaptive function programming
Self adjusting computation https://www.umut-acar.org/research#h.x3l3dlvx3g5f
adapton
incremnetal  https://blog.janestreet.com/introducing-incremental/
[salsa](https://github.com/salsa-rs/salsa)
salsa.jl

Man I really need to decided where this stuff should go.

# Resources
[bag datalog](https://twitter.com/NickSmit_/status/1510832523701456896?s=20&t=5y91-I1SPrIGomAWSqs69w) https://arxiv.org/pdf/1803.06445.pdf
bag rewriting. derivation tree. rule(reason1,reason2) :- R(reason).R(reason)
No subsumption.
What about making these things the same thing. We have an equiavalence class of proofs. We extract a smallest one.
How do you record eq? downcast ids to integers
eq(i, i, reason)
proof extraction becomesan egrtaph extraction
We get the hash consing property for free.



topics:
- incremental datalog
- differential datalog https://github.com/frankmcsherry/blog/blob/master/posts/2016-06-21.md

[big datalog on spark]http://yellowstone.cs.ucla.edu/~yang/paper/sigmod2016-p958.pdf

[Modern Datalog systems at sigmod and vldb](https://github.com/frankmcsherry/blog/blob/master/posts/2019-09-06.md)
[Scaling-Up In-Memory Datalog Processing: Observations and Techniques]() Recstep




unsafe stratification:
strata_finish(), !query_strata.
Timestamps can d something similar
watermark(t), !query(t1), t1 < t 
or safe deletion
delete(t).
You can partial evaluate to satisfy rel_0 rel_1 rel_2... it is annoying though and not very scalable


[QL: Object-oriented Queries on Relational Data](https://drops.dagstuhl.de/opus/volltexte/2016/6096/pdf/LIPIcs-ECOOP-2016-2.pdf)

[datalog reloaded](https://link.springer.com/book/10.1007/978-3-642-24206-9?page=2#toc) a datalog compendiium 2011
 
[algerbaic modelling in datalog](https://dynresmanagement.com/uploads/3/5/2/7/35274584/datalog_warrenbookchapter.pdf)
Some logicblox stuff. Datalog meets mathemtical programming?

Generic Join



If you wrote a decompiler or compiler in datalog, provenance becoes something more concrete to talk about


Compare and contrast datalog vs CHR. subsumption allows us some of the deletion of CHR. Proapgation rules of chr are similar to datalog rules. We could possibly emulate multisets using subsumption by adding extra multiplicty parameter to realtions.


[datalog : concept history outlook 2018](https://dl.acm.org/doi/10.1145/3191315.3191317)
[declarative logic programming](https://www.google.com/books/edition/Declarative_Logic_Programming/CMatvAEACAAJ?hl=en)




`call/N` is emulatable clause by clause in prolog.
Is there an analogous meta predicate?
foo(a,b) :- push(["foo", a,b]).
bar(a) :- push(["bar", a]).



What about interfacing with prolog?
What about interfacing with lua or python? ocaml haskell, minizinc.




[Synthesizing Datalog Programs Using Numerical Relaxation](https://arxiv.org/abs/1906.00163) difflog
[provenance based synthesis of datalog programs](https://www.youtube.com/watch?v=cYAjOGhclcM&ab_channel=ACMSIGPLAN)
Building a compiler in datalog. I can parse. I can do program analysis. How do I backend? Backend takes arbitrary non monotonic choices.
Use choice domain? that could work. I could force an ordering through the program.
```souffle
// linear assembly sequence
.type Op = Mov {out , in , }
asm(1, "mov", "x", "y").
asm(2, ")

liveness(instr, var)

assign("x", : reg)


```

```souffle
.decl A(k:number, v:number)
.output A(IO=stdout)
A(1, 1).
A(1, x+1):-
    A(1, x),
    x < 10.
A(x, v1) <= A(_, v2):-
    v1 < v2.
```

[topdown vs bottom up datalog](https://twitter.com/wilton_quinn/status/1496393635533066241?s=20&t=XQ6lmI5ivNs5z5-EwnGKMQ)

[datalog and recursive query processing](http://blogs.evergreen.edu/sosw/files/2014/04/Green-Vol5-DBS-017.pdf)

What if i did a call to minizinc formulog style?

A reversible compiler. would requires exists and equality. ... egraph?
[dr lojekyll](https://www.petergoodman.me/docs/dr-lojekyll.pdf)

So an object oriented datalog.

"These are generative functors? Is that how they return a relation? Do these functors take arguments?. Would the analog in souffle to be running the C++ program api in a user defined functor?"

[geometric database](http://www.mmrc.iss.ac.cn/~xgao/paper/jar-gdbase.pdf) horn clauses. good clean fun
[So You Want To Analyze Scheme Programs With Datalog?](http://webyrd.net/scheme_workshop_2021/scheme2021-final2.pdf)
[parser in datalog](https://homes.cs.washington.edu/~bodik/ucb/cs164/sp13/lectures/09-Datalog-CYK-Earley-sp13.pdf) bottom up parsing


[analysis are arrows](https://luctielen.com/posts/analyses_are_arrows/)

[Static analysis in datalog slides](http://www.cse.psu.edu/~gxt29/teaching/cse597s19/slides/06StaticaAnalysisInDatalog.pdf)

[modulog](https://github.com/bobatkey/modulog) - datalog with ocaml style modules

[crepe](https://github.com/ekzhang/crepe) a rust prcoedural macro datalog

Dedalus datalog. Is it datalog with a time variable or something more? I think it may have changed the stratification conditions.


<https://twitter.com/csaba_hruska/status/1456575302906355715?s=20> subsumptive datalog good for lattices?

<http://logicprogramming.stanford.edu/readings/tekle.pdf>
More efficient datalog queires - subsumtive tabling beats magic sets

<https://www3.cs.stonybrook.edu/~kifer/TechReports/OpenRuleBench09.pdf> openrulebench. Some described benchmark problems for rule engines

<https://edmcman.github.io/papers/ccs18.pdf> Using Logic Programming to Recover C++ Classes and Methods from Compiled Executables

<https://github.com/grin-compiler/souffle-cfa-optimization-experiment>


Using SQL engines as backend. https://duckdb.org/2021/10/29/duckdb-wasm.html

https://www.youtube.com/watch?v=HRO3RkOHe_4&ab_channel=MayurNaik - constraint based analysis lecture 7

Nielson books seems a lot more readable to me now.

Z3 datalog has intervals? How do i find a list of supported domains
So I could use C-cube datalog
Or I could use Z3 datalog.
If I want to go in browser (and of course I do), then Z3 is not wise.
Neither is souffle.
Could roll own bad datalog.
Ogre?

https://souffle-lang.github.io/examples simple points to analysis

Is datalog actually a good fit
https://tudelft-cs4200-2020.github.io/ - hmm sppoofax
https://www.youtube.com/watch?v=Qp3zfM-JSx8&ab_channel=ACMSIGPLAN - souffle
[Demand Interprocedural Program Analysis Using Logic Databases](http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.648.1834&rep=rep1&type=pdf) - reps
Engler 96


prosynth - leanr datalog rules from data?

.type Binop = 
.type Expr = 
.type Stmt = 
   While 




https://arxiv.org/abs/2107.12909 - so you want to analyze scheme with datalog https://www.youtube.com/watch?v=oiXL44WlC-U&ab_channel=ACMSIGPLAN

Might this not be a nice pass for higher-order theorem proving?

CFA - labelling all subespressions =? program points?
In functional programs value and control flow are more intertwined

https://en.wikipedia.org/wiki/Use-define_chain

https://matt.might.net/articles/implementation-of-kcfa-and-0cfa/ - k-CFA: Determining types and/or control-flow in languages like Python, Java and Scheme
Might does stuff with this. Abstracxting abstract machines is about 
Van horn. Darais
Gilray. Micinski
It's in that Nelson book

olin shivers

https://dl.acm.org/doi/10.1145/2926697.2926698 - chloe paper Liveness-based garbage collection for lazy languages

https://www.youtube.com/watch?v=7fDfWBsiqok&ab_channel=ACMSIGPLAN - visualzing abstract absract machines


https://yanniss.github.io/
Points to analysis. Doop
https://yanniss.github.io/M221/
https://www.youtube.com/playlist?list=PLheERyVBk39SefKqkGEo5YesOn9rkl8fS in greek
https://www.youtube.com/watch?v=3RHv44Ehd5Y&list=PLRUJ115QHa0WMyGyP2j_1KRFJjaT0kFOu&ab_channel=plast-lab - doop and datalog tutorials

objects are represented by allocation sites. firest abstraction. Good idea.
Actual program textual positions
context sensitivity is what makes an analysis precise (call stack, maybe loop unroll?)
andersen style analysis.
pointer analysis
flow-sensitive, field-sensitive, heap cloning, bdd, k-cfa
mutual recursion

source, alloc, and move instructions. a databse of each one.

```prolog
varpointsto(var, obj) :- alloc(var, obj).
varpointsto(to, obj) :- move(to, from), varpointsto(from,obj).

%assignemnts are local
assign(to,from) :- assignlocal(from, to, _).

%but also any function call is an assigneent
assign(formal, actual) :- calgraphedge(invocation, toMethod), formalparam[index, toMethod] = formal, ActualParam[index,uinvocation] = actual.

% and returns
assign(local,return) :- callgraphedge(invocation,toMethod), returbnvar(return, toMethod), assignReturnValue[invocation] = local.

varpointsto(var,heap) :- assignheapallocation(heap,var, inMethod),  reachable(inMethod).
varpointsto(to, heap) :- assign(to from)

// base.fld = from
fieldpointsto(baseheap, fld, heap) :- storinstancefield(from, base, fld, _), varpto(base,baseheap), varpto(from,heap).

// to = base.fld
varpto(to,heap) :- loadinstancefield(base,fld,to), vpto(base,baseheap), fieldpto(baseheap,fld, heap).

// base.toMethod(...) 
reachable(tomethod), callgraphedge(invocation, tomethod), varpto(this,heap) :-
    reachable(inmethod), instruction:method([invocation]), 
    virtualmethodinvocation( invocation ) = base,
    varpointsto(base, heap),



```

a model of context senssitive
call site sensitivity
variables are qualified by the call site of their enclosing method



prelude.ml = open KB yada yada

#include prelude.ml


could I compile datalog to bap?
class(slot,slot,slot) :- class(slot,slot,slot),
class(slotname : f(x,y) , ) :-
==
request body
promise head,

build rule.

differences
- classes have named columns, not positional (extensible). They also have unique ids always. Kind of more similar to souffle records?
- Modedness. Can I even promise multiple slots at once? In a sense datalog is not interestingly moded.
- It's more of a tabled prolog. Top down requests which lazily trigger table instantation

val promise : ('a, 'p) slot -> ('a obj -> 'p t) -> unit
('a, 'p) slot -> 'a obj -> 'p t

program(obj@{ insn : q , semantics : s }) :-   
program( obj: o, semantics : s, ) :-

Program.cls
promise slot1 (fun obj -> 

)

Hmm obj is incoming. slots are possibly incoming or outgoing

provides <-trigger(slot, obj), collects
    (slot : slotexpr :- obj)    -- the api of promise has obj incoming and slot outgoing
    Things don't _have_ to be built off of obj, but it sure helps.

An option domain is closest to ordinary datalog / tabled prolog


we can only promise on one slot. We can provide them all though. Individual slots are joined.
a list of lattice tuples vs lattice with projections

so datalog gives uniqueness of an entry easily
path(x,z) :- edge(x,y), path(y,z).
path(x,y) :- edge(x,y)
edge(1,2)
edge(2,3)

vertex(1).
vertex(2).
path(1,_).
path(2,_).
path(3,_).

path(a, _) :- vertex(a). -- trigger on path? but path doesn't exist


p@path( head_slot , tail_slot ) :- 



datalog over intervals. Maybe this would be an interesting blog post.
The relation itself has to implement the lattice api. Not the individual fields
What makes semi naive evaluation possible is the difference operator (heyting?)
Datalog does require a notion of projection. And a notion of relation composition/database join
E' = proj( A /\ B /\  C /\ D )
E1 = E \/ E'


Sometimes I've had knowledge base objects for which I immediately fill a slot upon creation, because that slot is essentially part of the objects identity. As an example, I have path objects in the KB. The only time i make one is when I have a particular path to talk about and I'm never going to offer another opinion about what that path is, all other information is derived from it. It feels slightly awkward that I have to define this slot using an optional domain, basically as far as I can tell, because I have to create an empty object and then provide for the slot on the next line. So I'm only using the `None` case for the briefest moment, but now have to deal with that case or use `Option.value_exn` whenever I access it. Is there a more elegant way to deal with nonoptional slots? I could use the `flat` domain with `[]` as a default but that is conflating 

- 

https://kilthub.cmu.edu/articles/thesis/Holmes_Binary_Analysis_Integration_Through_Datalog/7571519
homles binary analysis through datalog
https://github.com/maurer/marduk/tree/master/mycroft
https://github.com/maurer/holmes


http://reports-archive.adm.cs.cmu.edu/anon/anon/usr/ftp/2006/CMU-CS-06-180R.pdf alias analysis datalog



hmm. temporally oblivious. Interesting.
This idea of using explicit time is interesting. Why didn't I consider using an epoch variable?

Synactic sites. also interesting. Syntax is intrinisically finite.

doop, paddle, wala, bddbdbdbd


https://www.youtube.com/playlist?list=PLamk8lFsMyPXrUIQm5naAQ08aK2ctv6gE - SOOT lectures. 

https://yanniss.github.io/ptaint-oopsla17.pdf - unified points to and taint tracking

Interpeting programs into datalog?


Context sensitivty. I kind of imagine copies of the CFG coming out of the plane of the screen. Finite loop unrolling and then just regular widening. A mapping from block to visitation # might work for example. Many combos might not exist. This probably won't get you much


What would be a simple functional language to do this on?


https://arxiv.org/abs/2101.04718 Declarative Demand-Driven Reverse Engineering

https://link.springer.com/chapter/10.1007/978-3-030-11245-5_11 - demand control flow analysis



## building souffle emscripten
We revmoed all the extra flags turned off tests
removed all mentions of libffi
src/CMakeLists.txt - removed werror
CMakeLists.txt

removed ffi.h from interpeter/engine.cpp by removing the entire case

ok the frontend needs a bunch of stuff. It calls mcpp first.
This strips comments maybe?
Can link in mcpp, but for now, just remove that stage. use fopen and fclose instead of popen

We need to load into emscripten file system. It crashes kind of opaquely
/media/philip/phils_gud_disk/emsdk/upstream/emscripten/em++  -O3     -s ERROR_ON_UNDEFINED_SYMBOLS=0 -fuse-ld=lld @CMakeFiles/souffle.dir/objects1.rsp  -o souffle.js @CMakeFiles/souffle.dir/linklibs.rsp --preload-file test.dl 

remove loadDLL in engine.cpp. Maybe we can turn that back on. Do we even need it?

https://github.com/hoodmane/libffi-emscripten
https://github.com/emscripten-core/emscripten/issues/11066
It's conceviable libffi could be made to work

I could probably easily enough manually remove any stratification restrictions.

Actually, yizong mentioned some flags to do that
--disableTransformers=SemanticChecker 
"it may not do what uou expected"



Why can I not use the souffle implementation of ADT?
There is a cool directory of examples. There is a rewriting example in there





https://twitter.com/luctielen/status/1416319909055827970 datalog paper and haskell implementation
 https://souffle-lang.github.io/pdf/cc.pdf

Datalog for disassembly dldasm https://www.usenix.org/system/files/sec20fall_flores-montoya_prepub_0.pdf
instruction starts and ends is actually a hard problem. variable instruction lenght + stripping

instruction_start(insn : int, byte : int), instruction_end(insn : int, byte : int) 
bits(byte : int,  bits : byte ) ?

block(blk, insn)
Blockhead
blocktail


Identify instruction starts
Identify function starts
Build the CFG
Do a simple VSA

control flow

is_jmp(insns)
next(insn1 : , insn2 : ).



Dfiferential dataflow?
Jhanme street incremental?
https://en.wikipedia.org/wiki/Incremental_computing
Instead of datalog?
what does change mean?
diff x y
apply x dx = y

a -> (b, db -> da)
id = \x -> (x, \dx -> dx) 
everything starts at 0

stream processing
data Flow da db = da -> (db, Flow da db)

demand driven
(a -> (b, (unit -> b) -> (() -> a)  
datalog as an embedded DSL (semi naive eval really)
(Rel,Rel,Rel) -> Rel
join :: (Rel, Rel) -> Rel
join = \(r1,r2) -> r1 ++ r2, \(dr1, dr2) -> dr1 ++ dr2
fix :: (Rel -> Rel) -> Rel -> Rel
fix l = \x -> let (y, dl) = l x in
              let dx = diff y x in
              match dx with
              | [] -> (x, dl)
              | _ ->  y ++ dl dx
fix :: (Rel -> Rel) -> (Rel -> Rel)
fix 

relation foo x y z = 
fresh (\x -> 
 
)
fix :: Flow a a -> Flow a a
fix f = \da -> db, f2 = f a in 
              match db with
              | 0 -> (0, fix f2)
              | _ -> let (db2, f3) = fix f2 db in
                     (db + db2, fix f3)

trace :: ((Rel,Rel) -> (Rel, Rel)) -> Rel -> Rel




f(f(a)) = f(a) problem

% mark equiv as equivalence relation.

a(0).
f(1, 0).
f(2, 1).
equiv(1,2).

%congruence closure 1
% different orders of these?
% this is a very direct interpetation of congruence clsoure inference rule.
equiv(A, A') :- equiv(B, B'), f(A, B), f(A', B').


%alternative form
eclass( id , head, args) :- 

% get proof.

% f(Self, )
% f(Self, n )

Datalog might be a good DSL for specifying egraph computation problems. It allows multipatterns. 
A special relation = for egraph equality. We disallow unification?
Stratified negation can be allowed in egraph pattern matching.
The egraph is a database.

pat1(A,B,C) :- 

Can't we use unification variables as eclasses?

We can't generate new eclasses though.

equiv(X,Y) :- lhspat, rhs(X)
rhschunk(Fresh, ) :- lhspat
rhschunk(Fresh, ) : lhspat

The de moura bjorner matcher is some kind of brother of the WAM.


This might enable integrating congurence closure with program analysis passes.


Datalog is a specification language of relations. It is similar in some respects to SQL.

A relation is a set of tuples. One method for storing it is to use an array of tuples.

A slightly expanded form of datalog we could require that every variable is unique unless using a special `=` clause. 
It has a simple precodural reading

However, this naive storage method and algorithm is not the most efficient. Ideally, you want to use some pieces of the tuples as indices and use fast data structures for them (hashmaps or search trees). There is also much redundant computation here.
We want to push from small relations into larger ones and use indexing to 

factored form:
ancestor() :-  parent() ; (), ()
Kind of like a function call now.
generators that return only unique elements
Hmm. That's kind of a curious thing. It's push memoization rather than pull memoization.

def ancestor():
    seen = set()

    if newtup not in seen:
        yield newtup

Top down + Memoization

function parent()
    return [(:greg, :larry)]
end

function ancestor(x,y,z)
    for (x,z) parent()
end

a relation lifter.

Or could use explicit fix? memofix 
function rel(f, args...) 
    ctx = Dict()
    for arg in args
        if arg isa Symbol

    end
end

We really want to extend previous definitions not override them

Stream memoization.
How can I get the other modes for free? If you implement the fully producing mode, receiving mode is easy.
But unduly expensive.
How do you solve mode constraints.
Asymptotic costs. log_n( n^5 * ) 


https://www3.cs.stonybrook.edu/~warren/xsbbook/node5.html assign once variables.
@prolog x = y 

if inscope(x)
if inscope(y)
You could catch the undefvarerror? maybe.

I guess we could macro the entire function and change the semantics of =.
@nondet block for multiple function defintiions

I guess we could return unique IDs along the channels too
Using mutiple dispatch
f(::X, ::Y)
f()

@nondet()
f(x) = 
f(x) = 
end
rewrites to
f(x)
    [def1, def2]
end

How do we encode the mutliples:
1. array
2. channel
3. coroutine?
3. iterator

Hmmm. I could use tabled swipl instead of souffle.