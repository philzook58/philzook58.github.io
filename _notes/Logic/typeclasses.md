---
layout: post
title: Typeclasses
---

- [Applications](#applications)
- [Canonical Structures](#canonical-structures)
- [Unification Hints](#unification-hints)
- [Diamonds](#diamonds)
- [Overlapping](#overlapping)
- [Multiparameter](#multiparameter)
- [Traits](#traits)
- [Functional Dependencies](#functional-dependencies)
- [Associated Types](#associated-types)
- [Prolog](#prolog)

[wiki](https://en.wikipedia.org/wiki/Type_class)


# Applications
basic 1 parametr type classes
`class Eq a`

`class Coerc a b`

`class Collect e ce`

#
[How to make ad-hoc polymorphism less ad-hoc -  wadler and Blott](https://people.csail.mit.edu/dnj/teaching/6898/papers/wadler88.pdf) the OG.

[wadler typeclas page](https://homepages.inf.ed.ac.uk/wadler/topics/type-classes.html)

[Quantified class constraints](https://homepages.inf.ed.ac.uk/wadler/papers/quantcc/quantcc.pdf) harrop extension to typeclass clauses
# Canonical Structures
Typeclasses vs Canonical Structures. I don't get it.
Could I make a model? Maybe in prolog?
Diamond problem
Inheritance.
What are typeclasses? "Kind of like prolog"
Things are incompatible for some reason?
Canonical structures add unification hints?
[canonical structures ofr the working coq user - mahboubi tassi](https://hal.inria.fr/hal-00816703v1/document)

[How to Make Ad Hoc Proof Automation Less Ad Hoc](https://people.mpi-sws.org/~dreyer/papers/lessadhoc/icfp11.pdf)
Type parameters on the outside vs inside. Canonical structures have them inside. packed records

[Dependently Typed Records for Representing Mathematical Structure - Pollack](https://link.springer.com/chapter/10.1007/3-540-44659-1_29) "pebble style"
pakced vs unpacked


[First Class Type Classes - Sozeau and Oury](https://sozeau.gitlabpages.inria.fr/www/research/publications/First-Class_Type_Classes.pdf) not canonical structures but it is in coq.

# Unification Hints

[Hints in unification Andrea Asperti, Wilmer Ricciotti, Claudio Sacerdoti Coen, and Enrico Tassi](https://www.cs.unibo.it/~sacerdot/PAPERS/tphol09.pdf) interesting paper. Describes how typeclasses and canonical structures can be put under a similar umbrella as extesnible unification mechanisms.


# Diamonds

Coherence - typeclass systems can have diamonds

Diamonds are what are feared and dreaded. Why exacty?


[](http://blog.ezyang.com/2014/07/type-classes-confluence-coherence-global-uniqueness/)

[trait coherence little orphan impls](https://smallcultfollowing.com/babysteps/blog/2015/01/14/little-orphan-impls/)
Overlapping - typeclass systems often take prolog style unification without backtracking, i.e. only one instance is allowed to apply. This is smart in the sense that it makes thge performance of the system simpler and more reliable, and performance here is compilation time for your users. It is of course also limitting

# Overlapping

[Instance Chains: Type Class Programming Without Overlapping Instances](https://web.cecs.pdx.edu/~mpj/pubs/instancechains.pdf)
Non-overlapping means no heads are unifiable

non-overlapping means no backtracking. Can use egglog for unification then. Hmm. but head unification _itself_ needs backtracking.

# Multiparameter


[Type-checking multi-parameter type classes 2002](https://www.cambridge.org/core/journals/journal-of-functional-programming/article/type-checking-multi-parameter-type-classes/EABE479DF71BA3B31843E1518E5FA265)

# Traits
To me it looks like a refactoring or multiparam typeclasses.
Build syntatic rep of rust traits and then compiel to prology stuff from there.
impl(Trait(A,B,C), T).

[rustc guide](https://rustc-dev-guide.rust-lang.org/traits/resolution.html)
[common rust traits](https://stevedonovan.github.io/rustifications/2018/09/08/common-rust-traits.html)
[chalk book](https://rust-lang.github.io/chalk/book/)

Something to think about: Applications of egglog to typeclass resolution modulo equality. https://arxiv.org/abs/2001.04301 I don't really have a feel for the relation between tabled top down and magic set transformed bottom up although there clearly is one. I guess I'm also not clear on how magic set works in egglog for that matter. I don't know how to execute egglog top down in the first place.
An example would be finding a typeclass for Vec n a where you take the assoc/comm mult and add  axioms on the size index. Presumably the equational axioms must also be associated with instance dictionaries. Hmm. Maybe this is not as straightforward as I thought. You also need instances for congruence?
There isn't a problem with ordinary bottom up egglog, it just seems very wasteful on a query driven application like this

Chalk is also a very good point. [The cahlk blog posts](https://github.com/rust-lang/chalk) exliciitly talk about specialized equality. That is intriguing. I should contact Niko Matsakis.
https://smallcultfollowing.com/babysteps/blog/2017/01/26/lowering-rust-traits-to-logic/ Prolog + euqliaty reasoning he syas he's looking for

Chalk even talks about making a union find.


asscoaited types
IntoIterator
Item

```
intoiter(vec(T)) :- intoiter(T).
iter_item(vec(T)) = T :- intoiter(vec(T)).


eq(T,U)

query:
into_iter(vec(T))


```
Good examples of multi arg typeclasses?


Provenance of chalk or polonius are importatn for good error messages.

Guess missing clauses?

We need harrop for generic problems?
# Functional Dependencies
[Type Classes with Functional Dependencies? - Jones 2000](https://web.cecs.pdx.edu/~mpj/pubs/fundeps-esop2000.pdf)

[spj expression concern about fundeps](https://mail.haskell.org/pipermail/haskell-prime/2006-February/000289.html)

[Understanding Functional Dependencies via Constraint Handling Rules - stuckey duck sulzmann spj](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/jfp06.pdf)



[A general framework for hindley/milner type systems with constraints - sulzmann thesis](https://dl.acm.org/doi/10.5555/931853) HM(X)

[stuckey sulzmann - a theory of overloading](https://dl.acm.org/doi/10.1145/583852.581495) HM(X) + CHR
# Associated Types
[Associated Type Synonyms](https://www.microsoft.com/en-us/research/wp-content/uploads/2005/01/at-syns.pdf)
[Associated Types with Class](https://www.microsoft.com/en-us/research/wp-content/uploads/2005/01/assoc.pdf)

Associated types are of some relationship to functional dependencies

Does
class Foo a b c | a -> b, a -> c
work like
class Foo a where
    type b
    type c

# Prolog
[Tabled typeclass resolution](https://arxiv.org/abs/2001.04301)

Typeclasses look like prolog predicates

instances are prolog rules.
The proof of a successful resolution is a recipe for building the appropriate 

Associated types means a piercing of this barrier



datalog
egglog


```
implements(clone,life(A,T))

impl(tostring, life(A,i64)).
impl(tostring, vec(T)) :- impl(tostring, T).

% associate what trait owns fields
traitfield(tostring, tostring).

dotcall( foo, tostring ) :- type(foo, T), traitfield(Trait, tostring), impl(Trant, T). 
% dotcall(TEnv, foo, tostring)




% annotate everything with lifetimes?

% https://stevedonovan.github.io/rustifications/2018/09/08/common-rust-traits.html
% display, default, format, clone,

% sized
% borrow


% from to

% iterator
```


Original Wadler paper

Rust Chalk for Trait inference


BAP universal valures
OCaml typeclasss system
Oleg modellign typeclasses as prolog
<https://inbox.ocaml.org/caml-list/20190904152517.GA2014@Melchior.localnet/>
<http://okmij.org/ftp/ML/index.html#trep>


So what is the synctatic condition that precludes search?
1. nonoverlapping 

Would it be more interesting to just 
What am I understanding here?

Canonical structures was suggesting that some kind of inconstency would manifest.
Maybe lambda prolog gets us closer. We can have existential variables and such.

extensible unification


nat === (carrier nat_abGrp) :- 
A === A.


nat == carrier(Eq) :- Eq == natEq.
carrier(Eq,nat).



nonunifiable(L) :- all( /= , L ).


% haskell has no backtracking
% every case has a cut.
eq(tup()) :- !.
eq(tup(A,B)) :- !, eq(A), eq(B)

% 

eq(int, prim__equal_int).
eq(tup(A,B), lambda( x, case( x, tup(a,b) => bool_and( apply(EqualA, a) , apply(EqualB, b )  )    )  )  ) :- 
      eq(A, EqualA), eq(B, EqualB).
eq(tup(A,B), comp(and, par(EqualA,EqualB)))


eq(int).
eq()
eq(tup(A,B)) :- eq(A), eq(B).


ord(bool).
ord().

functor( maybe )
functor(compose(F,G)) := functor(F), functor(G)

traversable :-

% superclass
class(ord(A)) :- call(ord, A), class(eq(A))



"diamonds appear evertwhere. See pullbacks" ~ Hale