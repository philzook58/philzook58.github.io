---
layout: post
title: Continuations and Effects
tags: continuations
description: continuations and effects
---
- [Continuations](#continuations)
  - [Relationship between monads and continuations](#relationship-between-monads-and-continuations)
  - [Contexts and Holes](#contexts-and-holes)
  - [Are continuations functions?](#are-continuations-functions)
  - [The stack as a closure](#the-stack-as-a-closure)
- [Delimitted Continuations](#delimitted-continuations)
  - [Continuations Prompts](#continuations-prompts)
  - [One Shot](#one-shot)
- [Exceptions](#exceptions)
- [Call-cc](#call-cc)
    - [dynamic-wind](#dynamic-wind)
- [Algebraic effects](#algebraic-effects)
  - [Exceptions](#exceptions-1)
- [Resources](#resources)


# Continuations
Continuations are the work that was going to be done.
In a low level view, the contents of the stack, registers, and program counter are enough. Capturing all that is a pain, but it can be done. The system call `fork` for example kind of copies all of that brute force.
Depending how you write an interpreter, the capturing the work to be done can be tricky. Very often we write interpreters using recursive function calls. We are borrowing the host language stack to hold work to be done. If you explicitly manage the interpreter stack, it becomes more clear how to talk about the continuation. 

## Relationship between monads and continuations
mother of all monads. Buyt also Filinkski paper. refiication and reflection - In a langue with  effects like ocaml, we can reflect / reify the exceptions or mutation into their pure form that uses monad dsiciplaine. Converting native ocaml exception to Either exceptions [https://www.reddit.com/r/haskell/comments/1cyajx/the_mother_of_all_monads_school_of_haskell/](https://www.reddit.com/r/haskell/comments/1cyajx/the_mother_of_all_monads_school_of_haskell/) some caustic yet intriguing discussion. The embedding is (x >>=) like how cps embedding is (x $)?

[https://gist.github.com/sjoerdvisscher/a56a286ccfabce40e424](https://gist.github.com/sjoerdvisscher/a56a286ccfabce40e424) This is interesting. Using cont monad in swift probably to deal with the lack of higher kinded types. Similar to rust problem

https://www.reddit.com/r/haskell/comments/1cyajx/the_mother_of_all_monads_school_of_haskell/

## Contexts and Holes


## Are continuations functions?
Mostly no.

[standard ml contiutation signature](https://www.smlnj.org/doc/SMLofNJ/pages/cont.html)
```
type 'a cont
val callcc : ('a cont -> 'a) -> 'a
val throw : 'a cont -> 'a -> 'b
val isolate : ('a -> unit) -> 'a cont
type 'a control_cont
val capture : ('a control_cont -> 'a) -> 'a
val escape : 'a control_cont -> 'a -> 'b
```
throw is apply. The question is do we really want `cont` and `(->)` to be interchangeable. In a CPS implementation, the are 

## The stack as a closure
A closure is an value that contains a code pointer and captured data. To invoke a closure, you need to know some things about it's layout, but not everything. It hides it's implementation. Closures are objects in this sense.

Closures sometimes only store minimal amounts of environment, but in a naive implementation can store much more, maybe a copy of every variable in local scope for example instead of just the variables it closes over.

The conventional C stack has a return address and all the context of what has been going on. This really is a function pointer and environment. It is a closure. This closure however does not rely on the garbage collector to reclaim its memory, but so what?


# Delimitted Continuations
Oleg delimcc an implemntation of delimitted continuations for the
This uses exceptions (trap frames) as stack markers. In ocaml, at every try block puts handlers in the stack. These are marks
It then copies the stack up to these points.
mentions camlcallcc by xavier leroy https://xavierleroy.org/software.html It's pretty small actually. Very interesting. It is copying the stack quite literally.


A delimitted continuation is a mapping between contexts... ?
[lwt fibers using delimcc](http://ambassadortothecomputers.blogspot.com/2010/08/mixing-monadic-and-direct-style-code.html)

[libmprompt](https://github.com/koka-lang/libmprompt) A 64-bit C/C++ library that aims to implement robust and efficient multi-prompt delimited control.
## Continuations Prompts
[](https://stackoverflow.com/questions/29838344/what-exactly-is-a-continuation-prompt)

Marks
[racket docs on conituation karks](https://docs.racket-lang.org/reference/contmarks.html)
[Compiler and runtik support for continuation marks](https://www.cs.utah.edu/plt/publications/pldi20-fd.pdf)
The stack exists. You can put marks on it that could be searched for.

## One Shot
One shot continuationns can be called at most or exactly once. This is simpler and more efficient to implement and covers many (but not all) use cases

https://discuss.ocaml.org/t/multi-shot-continuations-gone-forever/9072 



# Exceptions

# Call-cc
call with current continuation
Relationship to double negation encoding


[An argument against call-cc](https://okmij.org/ftp/continuations/against-callcc.html)
[undelimited continuations are covalues rather than functions](https://okmij.org/ftp/continuations/undelimited.html)
### dynamic-wind

# Algebraic effects

What even are algebraic effects?

Kind of like resumable exceptions.
Also kind of like yield-step (exactly like?).

[Koka](https://koka-lang.github.io/koka/doc/book.html)
[Generalized evidence passing for effect handlers: efficient compilation of effect handlers to C](https://dl.acm.org/doi/10.1145/3473576)
[Implementing Algebraic Effects in C](https://www.microsoft.com/en-us/research/publication/implementing-algebraic-effects-c/) [libhandler](https://github.com/koka-lang/libhandler)

Interaction trees. THe semantics of a program is a tree of call and response patterns.
THe handler is a fold over the tree giving it semantics

[High-Level Effect Handlers in C++](https://homepages.inf.ed.ac.uk/slindley/papers/cppeff-draft-august2022.pdf)
## Exceptions

Either Err a piggy backs error handling on the regular return mechanisms. Every stack frame needs to be inspected to bubble error up. This is not how native ocaml exceptions are implemented and probably not how many systems do it.

CPS piggybacks other control flow on closure creation mechanisms.



[Ocaml is getting an effect system](https://pldi21.sigplan.org/details/pldi-2021-papers/14/Retrofitting-Effect-Handlers-onto-OCaml) 
See my ocaml notes for more.

* [Efficient compilation of algebraic effect handlers](https://dl.acm.org/doi/abs/10.1145/3485479)
* [effectfuljs. a javascrpt transpiler for effects](https://github.com/awto/effectfuljs) very cool. multi prompt delim conitautiona too?
* https://www.stephendiehl.com/posts/exotic03.html effect systems are off to the side, but do they help explain lifetimes?  https://news.ycombinator.com/item?id=25178437 interesting commments. Oleg talk. Frank language
* divergence as an effect. But also is memory usage an effect 
* ocaml algebraic effects.  https://github.com/ocaml-multicore/effects-examples https://www.youtube.com/watch?v=z8SI7WBtlcA&feature=emb_title&ab_channel=JaneStreet https://ocamlverse.github.io/content/future_ocaml.html#typed-algebraic-effects https://github.com/ocamllabs/ocaml-effects-tutorial
* There was an andrej bauer video https://www.youtube.com/watch?v=atYp386EGo8&ab_channel=OPLSS What's Algebraic About Algebraic Effects and Handlers?
*  Sandy Maguire and polysemy
* resumable exceptions.
* Related the the python yield stuff. 
* Daan Leijen paper https://www.microsoft.com/en-us/research/wp-content/uploads/2016/08/algeff-tr-2016-v2.pdf comes up
* Koka, Eff, F*, Link, Helium
* [Daan Leijen Asynchrony with Algerbaic Effects](https://www.youtube.com/watch?v=hrBq8R_kxI0&ab_channel=Vercel)
* Plotkin papers
* Alexis King effects for less https://www.youtube.com/watch?v=0jI-AlWEwYI&ab_channel=Z%C3%BCrichFriendsofHaskell
* https://github.com/ghc-proposals/ghc-proposals/pull/313 delimitted continuation primops ghc proposal. Lots of interestnig discussion
* Pretnar 2015  An Introduction to Algebraic Effects and Handlers Invited tutorial pap https://www.eff-lang.org/handlers-tutorial.pdf
- https://cs.ru.nl/~dfrumin/notes/delim.html delimitted contiunuations
- Asai
- [Eff directly in ocaml](https://arxiv.org/pdf/1812.11664.pdf) Kiselyov Sivaramakrishnan  
- [algerbaic effects for the rest of us](https://overreacted.io/algebraic-effects-for-the-rest-of-us/) async functions and generators have a different "color". effects remove the need for this how?
common lisp condition system is related? Is another example of resumable exceptions.

# Resources
[srfi 226: Control Features](https://srfi.schemers.org/srfi-226/srfi-226.html)

[https://github.com/rain-1/continuations-study-group/wiki/Reading-List](https://github.com/rain-1/continuations-study-group/wiki/Reading-List)

Coroutines and generators as effect systems. javascript cotuotines to conitations [https://gist.github.com/yelouafi/bbc559aef92f00d9682b8d0531a36503](https://gist.github.com/yelouafi/bbc559aef92f00d9682b8d0531a36503)

Rebvisting coroutines [http://www.inf.puc-rio.br/~roberto/docs/MCC15-04.pdf](http://www.inf.puc-rio.br/~roberto/docs/MCC15-04.pdf)

[https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.398.9600&rep=rep1&type=pdf](https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.398.9600&rep=rep1&type=pdf) Yield - mainstream delimitted continuations. slides [http://parametricity.net/dropbox/yield-slides.subc.pdf](http://parametricity.net/dropbox/yield-slides.subc.pdf)

https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.399.1021&rep=rep1&type=pdf
Lazy v Yield - kiselyov sabry peytonjones
Inremental linear pretty printing

https://twitter.com/sigfpe/status/1274764185658769408?s=20

io.py [https://gist.github.com/alexknvl/e15ea9762a58935b28f2](https://gist.github.com/alexknvl/e15ea9762a58935b28f2)
https://github.com/alexknvl/ai-meetup/blob/master/19-09-26-ppl1/ppl-meetup.ipynb probablistic programming
https://twitter.com/ezyang/status/1300278419188580353?s=20

[https://pypi.org/project/effect/#:~:text=Effect%20is%20a%20library%20for,It%20supports%203.6%20and%20above.](https://pypi.org/project/effect/#:~:text=Effect%20is%20a%20library%20for,It%20supports%203.6%20and%20above.) effect - as python library

takafumi asrakaki using julia yieldto for a "callcc"
https://julialang.zulipchat.com/#narrow/stream/137791-general/topic/call.2Fcc.20for.20Julia.3F.20%28or.20how.20to.20use.20.60yieldto.60%29/near/218188425


[https://news.ycombinator.com/item?id=24257488](https://news.ycombinator.com/item?id=24257488) Anatomy of Lisp. Lisp in small pieces.

[https://www.cs.utexas.edu/ftp/garbage/cs345/schintro-v14/schintro_142.html#SEC271](https://www.cs.utexas.edu/ftp/garbage/cs345/schintro-v14/schintro_142.html#SEC271)

Lambda prolog book is drectly talking about semantics in terms of sequents

[https://github.com/nornagon/jonesforth/blob/master/jonesforth.S](https://github.com/nornagon/jonesforth/blob/master/jonesforth.S) Jones forth tutorail assembly

https://slang.soe.ucsc.edu/cormac/papers/pldi93.pdf The essence of compiling with continuations. Pushing A normal form.