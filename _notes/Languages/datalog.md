---
layout: post
title: Datalog
---


# What is datalog?
When I say datalog, I might mean a couple intertwined different things. I might be referring to bottom up execution of logic programs.
Or I might be concentrating on 

# What can you do with datalog?
Well, anything you can do with ordinary database queries. What do you do with those? I dunno. Search for patterns

But then on top of that you can use recursive queries. And that is where things get more interesting.
Program analysis.

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

## Subsumption examples
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


A canonical element relation. Similiar to union find algorithm
```
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

[dr. disassembler](https://github.com/lifting-bits/dds) and blog post

Linear "datalog" - destructive state update
Using Sqllite - https://www.sqlite.org/lang_with.html recursive ctes seem to get you a lot. Cool examples. Mandelbrot

bottom up Dynamic programming in datalog?

`f(@g()) :- true` Sometimes you need to put true in the rhs position.

# Souffle source
- synthesizer - actual code printers
- include/souffle - the runtime of souffle
- ram, relational abstract machine
- 

# Resources
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

prosynth - leanr datalog rules from data?

.type Binop = 
.type Expr = 
.type Stmt = 
   While 




https://arxiv.org/abs/2107.12909 - so you want to analyze soufle with datalog https://www.youtube.com/watch?v=oiXL44WlC-U&ab_channel=ACMSIGPLAN

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