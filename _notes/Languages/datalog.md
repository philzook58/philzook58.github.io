---
layout: post
title: Datalog
---
- [What is datalog?](#what-is-datalog)
- [What can you do with datalog?](#what-can-you-do-with-datalog)
  - [Program Analysis](#program-analysis)
- [Implementations](#implementations)
  - [Formulog](#formulog)
  - [Flix](#flix)
  - [dr lojekyl](#dr-lojekyl)
- [Souffle](#souffle)
  - [intrinsic functors](#intrinsic-functors)
    - [Parsing](#parsing)
    - [BitSets](#bitsets)
      - [Bitset reflection](#bitset-reflection)
  - [Souffle proofs](#souffle-proofs)
  - [Magic Set](#magic-set)
  - [Examples](#examples)
  - [User Defined Functors](#user-defined-functors)
  - [ADTs](#adts)
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
      - [Choice domain](#choice-domain)
  - [Choice Domain](#choice-domain-1)
  - [Souffle source](#souffle-source)
- [Examples](#examples-1)
  - [Lambda representation](#lambda-representation)
  - [Equality Saturation](#equality-saturation)
  - [Theorem Proving](#theorem-proving)
  - [Typeclass resolution.](#typeclass-resolution)
  - [Type checking / inferring](#type-checking--inferring)
- [Resources](#resources)
- [class(slotname : f(x,y) , ) :-](#classslotname--fxy----)
  - [building souffle emscripten](#building-souffle-emscripten)

# What is datalog?
When I say datalog, I might mean a couple intertwined different things. I might be referring to bottom up execution of logic programs.
Or I might be concentrating on 

# What can you do with datalog?
Well, anything you can do with ordinary database queries. What do you do with those? I dunno. Search for patterns

But then on top of that you can use recursive queries. And that is where things get more interesting.
Program analysis.

topics:
- incremental datalog
- differential datalog

## Program Analysis
[Unification based pointer analysis](https://github.com/souffle-lang/souffle/pull/2231) "Steensgaard style" vs Anderson style



# Implementations
- Souffle
- Flix
- Rel
- [Datafun](http://www.rntz.net/datafun/). lambda calculus with type system for tracking lattice monotonicity. and built in set type with comprehensions.
- [differential datalog](https://github.com/vmware/differential-datalog)
- dr lojekyll
- formulog

## Formulog
SMT formulas as data. Interesting distinction with CHC where smt formula are predicates.
Refinement type checker.

## Flix
[online playground](https://play.flix.dev/)
Also install as a vs code plugin. very nice.
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


as(a, number) I can cast ADTs to numbers?
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

### Parsing
`substr` makes this feasible. This unfortuantely is going to reintern the string though. So hard to believe it'll ever be efficient.

CYK Parsing is an example of dynamic programming.

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

## Magic Set

Specializes datalog program to a particular query / output.
Query answer transfomation

We could imagine applying dataflow analysis techniques to prolog programs. We can write dataflow analysis in a pleasant way using datalog. The languages of datalog and prolog coincide. Datalog terminates.

I suppose I identify datalog with bottom up execution, which is not necessarily the case depending on author.

In prolog SLD resolution, there are program points. We could create relations describing the store at these points. These are the supplementary 
For annotated predicates we could move the annotations as extra fields of the predicates instead of as annotations. This feels more natural when interpreting as a dataflow analysis. Annotations are a describing the binding state? (annotations are lattice? Maybe so but not in the right way)

"It is a form of partial evaluation: at query time, rewrite (specialize) the entire program to an equivalent one, then evaluate it bottom-up. A binding-time analysis identifies which predicates benefit from specialization. Sideways-information passing strategy guides the rewrite."
"I see it as a way to "hack" a bottom-up execution (from facts) into computing top-down (from queries). John Gallagher's query-answer transformation is related to that and used for program analysis https://arxiv.org/pdf/1405.3883.pdf, https://bishoksan.github.io/papers/scp18.pdf"


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

safer alternaitve
```
.comp Vector<T>{
.type vector = V0 {} | V1 {x1 : T} | V2 {x1 : T, x2 : T} | V3 {x1 : T, x2 : T, x3 : T} | V4 {x1 : T, x2 : T, x3 : T, x4 : T}
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

#### Choice domain

Choice using subsumption, static or dynamic notion of "better".


## Choice Domain
<https://souffle-lang.github.io/choice> picks first one to come along
Can I combine choice domain and lattice. But choice domain once you pick you're done...
well. I can recover lattice style via an explicit congruence closure. So. it doesn't matter I guess.



##  Souffle source
- synthesizer - actual code printers
- include/souffle - the runtime of souffle
- ram, relational abstract machine
- 



# Examples
## Lambda representation
What is the most appropriate way? Probably we want to implement some kind of machine flavored implementation.
Or maybe a graph like representation.

I could literally do hash cons modulo alpha. I can dor xor trick.

Could make user defined functor for substition.

I could make udf for normalization. And memoize into a choice domain?


## Equality Saturation
See blog posts

egglog

## Theorem Proving

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

## Type checking / inferring
Related of course to the above.


# Resources
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

[Rust lifetime analysis written in souffle](https://github.com/rljacobson/lifetimes)
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

https://dl.acm.org/doi/10.1145/2926697.2926698 - chloe paper

https://www.youtube.com/watch?v=7fDfWBsiqok&ab_channel=ACMSIGPLAN - visualzing abstract absract machines

https://github.com/nevillegrech/gigahorse-toolchain - decompiler for smart contracts based on souffle
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