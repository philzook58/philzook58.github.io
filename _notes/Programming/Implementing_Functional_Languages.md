---
layout: post
title: Functional Languages Implementation
---

See also notes on:
- binding forms
- continuations
- ocaml
- haskell
- scheme / lisp


# Abstract Machines
# CEK

# SECD
# Krivine
# ZAM
# G-machine
# Combinators
# HVM

[Justine Lambda Calculus in 400 Bytes](https://justine.lol/lambda/) unbelievable

Xavier leroy implementing functional languages
https://xavierleroy.org/talks/compilation-agay.pdf really good.
He describes an interesting operation "disassembling" SOme relation to quote :: Value -> Term


```ocaml
type term = 
 | Var of int
 | Const of int
 | Lambda of term
 | Apply of term * term
 | Prim of value list -> value * term list
and env = value list 
and value = Lit of int | Closure of term * env

let rec eval env = function
| Var n -> List.nth n env
| Const n -> Lit n
| Lambda t -> Closure (t, env)
| Apply f x ->
     let Closure(f', env') = eval env f in
     let x' = eval env x in
     eval (x' :: env') f'
| Prim (f, args) -> let args' = List.map (eval env) args in
                    f args'
```



Terms are syntax. The original program? Values are data objects. Bit patterns?

```ocaml
type aexpr = Lit of int | Add of aexpr * aexpr
type rpn = Push of int | Add

let rec compile : aexpr -> rpn list = function
| Lit n -> [Push n]
| Add (a,b) -> (compile a) @ (compile b) @ [Add]

```

```ocaml
(* term as above*)
type machine = 
| Access of int
| Closure of machine list
| Return
| Apply

let rec compile : term -> machine list = function
| Var n -> [Access n]
| Lambda t -> [Closure (compile t) @ [Return]]
| Apply (f,x) -> (compile f) @ (compile x) @ Apply
```

[data representation of chicken scheme](https://www.more-magic.net/posts/internals-data-representation.html) very similar to ocaml
[cheney on the mta of chicken scheme](https://www.more-magic.net/posts/internals-gc.html)

[resources on compilers for fnctional languages](https://github.com/soupi/rfc/blob/master/fun-compilers.md)
<http://t3x.org/klisp/klsys/index.html> KLSYS a kilolisp systems - bytecode compiler etc of lisp 2000 lines C, 3000 lines lisp
<http://t3x.org/index.html> Also lots of books: lisp from nothing, lisp system implementation


<http://www.iro.umontreal.ca/~feeley/papers/YvonFeeleyVMIL21.pdf> a msall scheme vm compiler and repl in 4k
<https://github.com/udem-dlteam/ribbit>
<http://www.iro.umontreal.ca/~feeley/> Marc Feeley


<https://arxiv.org/pdf/1805.08842.pdf> compiling with continuations and LLVM

https://www.cs.princeton.edu/~appel/papers/safe-closure.pdf
closure converision is safe for space- Appel paper in coq about closures

Defunctionalization and closures
How do anonymous functions actually come to be?
Function pointers in C.
Closures are open function data types
Defunctionalizations are closed function data types. Internal to an algorithm we build closures, but the external interface does not accept them.

Continuations
Control flow is implicit and there are implicit auxiliary data structures. One of them (perhaps the most primordial) is the program counter. Even programming in assembly it is often a little hidden behind using instructions like jmp and call that yuou are manipulating it. 
For example in programming an FPGA, it is puzzling how you can get a sequential algorithm to run as there is no CPU a priori available. A standard approach is to build a finite state machine and a register that holds which state you are in. This register is effectivley the program counter. This is a micro special purpose cpu in many respects.

The next implicit control structure is the stack, which holds in it a pointer to what code to return to and also the context needed for the code to run.

The stack holds a code pointer and an environment, and in this sense it has great similarity to a closure.



Depth first search vs Breadth first.
Depth first is easy, because you can just use recursive function calls whereas breadth first is a pain because you need to maintain 
a queue. However, this is a false perspective. You can write DFS using a manual stack data structure. You are using the implicit stack of your programming language.

Assembly programmers know very intimately that the stack exists (if they choose to even have one). They have access to a continuation in this sense. It is part of a strange close mindedness that the memory of a program is divided into a heap and stack. This does not have to be. We could have multiples of each, forego them, perhaps have other fundamental regions of some other kind of data type. Implementing the stack as a heap allocated object is a valid approach. This allows you to save and destroy multiple stacks at will and is essentially what CPS boils down to under the hood assuming a typical implementation of a functional programming language.




What else does this paper bring into play? Correctness conditions

Functional programming has both a pure branch/smenatics and an operational semantics. It also has techniques needed to transform functional looking things into a form that can be executed by a computer. The output of a functional compiler is assembly.


Hmm. Yes proving the cps version of a list reverse is the same as no cps is 
Does CPS help streuctural recursion restirctions in coq?


http://www.t3x.org/lfn/index.html lisp from nothing
https://news.ycombinator.com/item?id=20591771


-dlambda and -dinstr flags for ocaml. interesting
http://cadmium.x9c.fr/distrib/caml-instructions.pdf
https://dev.realworldocaml.org/compiler-backend.html



https://news.ycombinator.com/item?id=25386756 compiler course cornell. Interesting links in comments
https://news.ycombinator.com/item?id=25273907 llvm comments



http://ezyang.com/jfp-ghc-rts-draft.pdf ghc rts


http://fyquah95.github.io/some-fun-with-ocaml-closures closure represnetatio n



If you can write a fold, you can write finally taglessly. Deepply nested patterns mactches are convenient. Double negation removal is one example. You need to refiying the pattern into a data structure.

There are many courses that use racket and ocaml

  * [https://www.seas.upenn.edu/~cis341/current/](https://www.seas.upenn.edu/~cis341/current/)
  * [https://course.ccs.neu.edu/cs4410/](https://course.ccs.neu.edu/cs4410/)
  * [https://www.seas.harvard.edu/courses/cs153/2018fa/schedule.html](https://www.seas.harvard.edu/courses/cs153/2018fa/schedule.html)
  * [https://iucompilercourse.github.io/IU-P423-P523-E313-E513-Fall-2020/](https://iucompilercourse.github.io/IU-P423-P523-E313-E513-Fall-2020/) IU compiler course Racket
  * [http://ace.cs.ohio.edu/~gstewart/courses/4100-18/](http://ace.cs.ohio.edu/~gstewart/courses/4100-18/)
  * [https://www.cs.cmu.edu/~janh/courses/411/17/schedule.html](https://www.cs.cmu.edu/~janh/courses/411/17/schedule.html)
  * [https://www.cs.utexas.edu/ftp/garbage/cs345/schintro-v14/schintro_142.html](https://www.cs.utexas.edu/ftp/garbage/cs345/schintro-v14/schintro_142.html)
  * https://blog.sigplan.org/2019/07/09/my-first-fifteen-compilers/ kuper describes nanopass style
  * http://andykeep.com/pubs/dissertation.pdf nanopass dissertation
  * [https://bernsteinbear.com/blog/compiling-a-lisp-0/](https://bernsteinbear.com/blog/compiling-a-lisp-0/) nice blog series compiling lisp to C
  * https://bernsteinbear.com/assets/img/11-ghuloum.pdf incremental appraoich to compiler construction



I like to start things simple.

Functional programming is cool and useful, but it isn't clear how to implement the features they provide on hardware that is controlled by assembly code.

There is a topic in functional programming call "abstract machines". 

#### Why Abstract Machines?

Abstract machines give a more explicit way on how to evaluate a program with a step relationship.

I think this may be closer to how hardware is built because physical systems are often characterizable by the space of states and the transitions or time evolution of them.

Something that is less compelling about abstract machines is that they aren't entirely trivial and explicit. The may still contain nontrivial data structures or judgement. What is trivial or not is in the eye of the beholder.

A huge issue that needs to be dealt with is how to deal with functions that capture variables from their environment.

#### Why Stacks?

I don't know. Stacks are a fairly innocuous data structure and easy to provide in many situations. The name stack seems to come from a stack of papers, which is pretty simple. The analog of registers might be a chalk board and the analog of random access memory might be a set of labelled boxes.

#### The RPN Calculator

The Reverse Polish Notation calculator gives a simple way to use a stack to evaluate arithmetic.

There is a place for code and a place for 

[http://learnyouahaskell.com/functionally-solving-problems](http://learnyouahaskell.com/functionally-solving-problems)

#### Defunctionalizing an Arithmetic Evaluator

You are imprisoned by the data and control constructs that the language you are using provides. You can step out of this by refusing to use them, and sometimes this can make things more clear. For example, sometimes it may be useful to control your own manual stack. This comes up for example when you are doing a depth first search and then want to go breadth first. You change a FILO stack into a FIFO queue.

An evaluator written in a recursive style has an implicit language provided stack controlling and remembering what things to do. It's very convenient. 

This is one of the examples in the Defunctionalization paper and it is a good starting schematic for the Evaluators paper.

#### Adding Bools

We could make a calculator for bools on their own with And, Or and other boolean operations. This would be very similar to the RPN calculator.

We can have both arithmetic and boolean operations. We can translate from arithemtic to booleans via comparison operations, and from boolean to arithemtic via the If-Then-Else construct.

#### Adding Let Bindings

Let bindings allow us to give names to values. The names themselves are often consdiered not particularly meaingful. 

Let bindings are among the simplest examples of a binding form. Binding forms are things that introduce a name. The name itself is not meaningdful in that if you replaced it at the binding site and all usage sites, you have an equivlaent expression in some sense. This is called alpha renaming.

One story (Leroy's slides) is that adding Let to your language requires a new data structure called the environment.

#### Adding Print Commands

Printing is considered to be an effect in Haskell and not available for pure programs. The Call By Push Value

#### Named Functions

Named functions also gives you recursion.

#### Currying and Closures.

One transformation is known as lambda lifting, where you 

[http://matt.might.net/articles/closure-conversion/](http://matt.might.net/articles/closure-conversion/)

[http://blog.sigfpe.com/2007/07/data-and-codata.html](http://blog.sigfpe.com/2007/07/data-and-codata.html) Sigfpe data and codata link david found. data has recursive calls on strict subpieces. codata has recursive calls underneath constructors so that it is always productive. Least fixed point vs greatest fixed point. This is that definedness ordering. Codata pattern matching focuses on the destructors of a record, rather than the constructors of a variant. It kind of feels like you're pattern matching on the evaluation context one layer deep rather than pattern matching on the value. One perspective is to take pattern matching as primitive, another is that you want to compile it away .  [https://www.cs.mcgill.ca/~dthibo1/papers/popl170-abel.pdf](https://www.cs.mcgill.ca/~dthibo1/papers/popl170-abel.pdf) [https://www.cs.uoregon.edu/Reports/MS-201806-Sullivan.pdf](https://www.cs.uoregon.edu/Reports/MS-201806-Sullivan.pdf) masters thesis descrbing and implemetynig [https://ix.cs.uoregon.edu/~pdownen/publications/esop2019.pdf](https://ix.cs.uoregon.edu/~pdownen/publications/esop2019.pdf) codata in action

[http://noamz.org/talks/logpolpro.pdf](http://noamz.org/talks/logpolpro.pdf) - really interesting zeilberger notes. <|> is the apply function occuring in defunctionalization. The negative types are defunctionalized continuations?

[https://www.microsoft.com/en-us/research/wp-content/uploads/2016/04/sequent-calculus-icfp16.pdf](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/04/sequent-calculus-icfp16.pdf) - SPJ sequent core

Forth. What about other control flow. What about Lazy If? The joy language has quotation forms. This feels very similar to cbpv thunks [http://www.kevinalbrecht.com/code/joy-mirror/index.html](http://www.kevinalbrecht.com/code/joy-mirror/index.html)

How does unification play into this. The WAM. Or proof formats as code? Metamath is some kind of stack machine isn't it? Is there a defunctionalization reconstruction of metamath,. The flattened postfix form of proofs occurs in those discrimination trees. a fast proof checker for atp

[https://arxiv.org/pdf/1109.6273.pdf](https://arxiv.org/pdf/1109.6273.pdf) Focalization. 

[https://semantic-domain.blogspot.com/2014/10/focusing-is-not-call-by-push-value.html](https://semantic-domain.blogspot.com/2014/10/focusing-is-not-call-by-push-value.html)

So you have this focus that moves around. And polarity. And these things remove inessential churn in the space of possible proofs. backtracking happens only when needed, specifically in /\L and \/R and focL and maybe other spots. If ou erase polrity annotations, you get a normal looking propsitions. You can arbitrarily add consistent polarity annotations? These correspond somehow perhaps to 

natural deduction has intro elim rules. sequent has left right rules. You can have intuitionsitc sequent calc

Values vs computations. Value vs co-values. Values vs contexts. Functions take values zand return compuutations. Thunking converts between computation to valu. pattern matching is a computation

[https://www.cs.cmu.edu/~fp/courses/](https://www.cs.cmu.edu/~fp/courses/) 0 frank pfenning. 

adk [https://www.reddit.com/r/haskell/comments/hp1mao/i_found_a_neat_duality_for_cps_with_call_by_push/](https://www.reddit.com/r/haskell/comments/hp1mao/i_found_a_neat_duality_for_cps_with_call_by_push/)

call by push value. A language that has thunks but not first class functions is possible. thunks are frozen commands. They can capture environment and be force, but not accept new commands. lambda x is pop x. V' is push V. reverse function application syntax

    
    <code>model in ocaml
    
    type 'a thunk = unit -> 'a
    let stack = newref [a]
    
    let lam f = let x = pop () in f x
    let app x = push x 
    
    
    A CK machine with print statements.
    
    </code>

There is some choices on what to target. Do you want to write a parser? Interpeter? Abstract machine? Do you want first class functions?

What is your language

  * Arithmetic expressions
  * Boolean expressions
  * let
  * Mixed Arith Bool
  * List of Commands.
  * Untyped lambda
  * named procedures.
  * Simply typed lambda
  * Mutation? References
  * Polymorphic lambda
  * callcc delimcc
  * error throw try catch
  * Read Write files
  * Pattern matching
  * Structs / Records / Tuple
  * ADTs

I find it always useful to consider arithemtic expressions. I know em well, they're simple, and the expose a decent percentage / good warmup of the features of lambda claculus. The big confusing things they miss are binding forms and substitution.

    
    <code>data AExpr = Lit Int | Add AExpr AExpr
    newtype Value = Value Int
    data AHole = LeftHole AExpr | RightHole Value -- ??? | HAdd AHole AHole | ALit Int
    
    eval (Add x y) = (eval x) + (eval y)
    eval (Lit i) = i
    
    -- cps
    evalk (Add x y) k = evalk x (\x' -> (evalk y (\y' -> k (x' + y'))))
    evalk (Lit i)   k = k i
    
    --defunctionalize
    
    data Lam = L1 AExpr Lam | L2 Int Lam | Halt
    
    evald (Add x y) l = evald x (L1 y l)
    evald (Lit i) (L1 a l) = evald a (L2 i l)
    evald (Lit i) (L2 j l) = evald (Lit (i + j)) l
    evald (Lit i) Halt = i
    
    -- Finally, we need to note a non trivial property to get accumulator passing style?
    
    apply (L1 a l) i = L2 
    
    -- an Aexpr example (with if then else) is actually in the defunctionaliztion paper
    
    step (e , []) = e
    step (Lit i, (LeftHole e) : k) = ( e  , (RightHole (Value i)) : k  )
    step (Lit i, RightHole (Value j) : k) = ( Lit (i + j), k )
    step (Add x y, k) = ( x , (LeftHole y) : k)
    
    No but Lefthold + Righthole + list is a zipper of the tree isn't it?
    
    Defunctionalization
    Go to use site?</code>

Next is BExpr or let bindings

The next feature that is nice to add is let bindings. Let bindings are a big step up in complexity. Lets are a feature that allows us to express sharing.

Xavier Leroy has some cool stuff in this course [https://xavierleroy.org/mpri/2-4/](https://xavierleroy.org/mpri/2-4/)

[https://www.nimblemachines.com/zinc-abstract-machine/](https://www.nimblemachines.com/zinc-abstract-machine/) Zinc machine

lambda mu mubar corresponds to sequent calculus somehow [https://ix.cs.uoregon.edu/~pdownen/publications/sequent-intro.pdf](https://ix.cs.uoregon.edu/~pdownen/publications/sequent-intro.pdf) Compling with classical connectives. Does this mean that a proof from vampire is a program possibly in this calculus? Could I build a proof asistant around this calculus where you program in lambda mu mubar? Maybe I could use a coninutation monad inside coq? Dependent lambda mu mubar? Abstract machines for CoC?

[http://logitext.mit.edu/tutorial](http://logitext.mit.edu/tutorial) - pretty cool little tutorial on sequent claculus

So sequent calculus is a strange little man. What is $latex \vdash$ ? 

Well, the point of formal proofs is that they are forms. This means that they are constructed out of steps that feels as straightforward, mechanical, and automatic as possible such that the checking of proofs is very difficult to get wrong. The syntax becomes this very dry and dead thing. You and I know we're talking about the naturals or whatever, but we're supposed to pretend we don't know that and just see the rules for what they are. I'm quite bad at this. 

Sequent calculus originates in the 30s, where the idea of computer wasn't exactly unknown, but definitely in a very different state than it is today. Certainly no significant actual general purpose computers had been brought into existence yet (Babbage maybe?). So the intent was to be using this stuff on pencil and paper.

The sequent can be read in different ways. One way is as a relation. Using the syntax Seq( hyps, concs ) makes this feel better to me. using a strange infix symbol to denote a relationship feels odd.

The sequent is a piece of the state of an incomplete proof. You've partially figured out how to prove some bits and not others and the sequent encodes this.

The piece of the state it is missing is that proofs in this system take the form of trees. So actually the state of the proof is multiple sequents.

The structural rules can be partially  

It is rather odd to me that there are three things in the calculus that all feel like implication. $latex \rightarrow$ $latex \vdash$ and the horizontal line. They do all reflect into each other. In addition, conjuction and disjunction reflect into the hypotheses list and conclusions. What is the point?

There does appear to be a point. You can have a big formula that is not obviously a tautology to my eye, but then through a sequence of many steps, each of which makes sense to me, reduce it to triviality. Somehow, these ridiculous seeming reflections make this possible.

The cut rule somehow invents an intermediate formula. Most of the other rules aren't like this. It's somewhat worrying. How does one mechanically invent this formula? I suppose you could enumerate as possible formulas?

    
    <code>data C = C V E
    data V = Mu (E -> C ) | Lam (V -> E -> C) | Inj1 V | Inj2 V
    data E = MuBar (V -> C) |  Stack V E | Choice (V -> C) (V -> C)
    run (C (Mu f) e        ) = run (f e)
    run (C v      (MuBar f)) = run (f v)
    run (C (Lam  f)  (Stack v e) ) = run (f v e)  
    run (C (Inj1 v)   (Choice f g)  ) = run (f v)
    run (C (Inj2 v))  (Choice f g) )  = run (g v)
    run x = x -- default case. Stuck?</code>

This is tail recursive. It feels somewhat like joining together Yield Await streams? Yea... We could probably make a stream library around this formalism.

Lambda mu is the classical natural deduction. Which is slightly different than sequent calc [https://stackoverflow.com/questions/28752112/interpret-parigots-lambda-mu-calculus-in-haskell](https://stackoverflow.com/questions/28752112/interpret-parigots-lambda-mu-calculus-in-haskell) [https://math.stackexchange.com/questions/3200700/difference-between-lambda-mu-calculus-and-intuitionistic-type-theory-lem](https://math.stackexchange.com/questions/3200700/difference-between-lambda-mu-calculus-and-intuitionistic-type-theory-lem)

[https://homepages.inf.ed.ac.uk/wadler/topics/dual.html](https://homepages.inf.ed.ac.uk/wadler/topics/dual.html) - wadler dual cbv cbn

Evaluation Contexts as one hole things. Armando had a section about them. callCC reifies this into a lambda, which is a value. During evaluation, we imagine there being a kind of cursor that is focused on a piece of an expression.  They tend to end up very stack-like or zipper like. Zippers have also been described as one hole objects [http://calculist.blogspot.com/2006/08/stack-is-context-zipper.html](http://calculist.blogspot.com/2006/08/stack-is-context-zipper.html) [http://okmij.org/ftp/continuations/zipper.html](http://okmij.org/ftp/continuations/zipper.html)

People talk about capturing the current continuation as a form of reifying the stack.

Abstract Machines - What is an abstract machine. It should be a thing that feels something like the surface language and something like . But that is also an IR. A machine should have an execution model. And the execution model should feel like something implementable by x86? It should be iterative in some sense? Tail recursive perhaps is another way of phrasing it. Danvy takes an interpreter which uses complex recursion and cps-es it and the defunctionalizes it to an iterative form. Also they should be first order, using no closures?  [https://tidsskrift.dk/brics/article/download/21783/19214](https://tidsskrift.dk/brics/article/download/21783/19214)

matt Might van horn [http://matt.might.net/papers/vanhorn2010abstract.pdf](http://matt.might.net/papers/vanhorn2010abstract.pdf) They add in stores and garbage collection and other things

  * krivine [https://www.irif.fr/~krivine/articles/lazymach.pdf](https://www.irif.fr/~krivine/articles/lazymach.pdf)
  * SECD
  * CEK [http://matt.might.net/articles/cek-machines/](http://matt.might.net/articles/cek-machines/) [https://www.youtube.com/watch?v=PwD7D7XUzec](https://www.youtube.com/watch?v=PwD7D7XUzec) [https://cstheory.stackexchange.com/questions/41256/is-a-cek-machine-an-implementation-of-a-cesk-machine](https://cstheory.stackexchange.com/questions/41256/is-a-cek-machine-an-implementation-of-a-cesk-machine)
  * Zinc
  * CAM
  * Spinless tagless g machine (STG)

Evidently If you use direct substitution, you can avoid the E part. That's mentioned in the sequent claculus tutorial. Don't need to look stuff up in an Env if you've already substituted.

mubar is something like callcc, it capures the current context stack. mu is something like a let binding context. It is rather strange these are dual. lambda takes both a valu and a continuation. It appears to be in cps form.

So just a simple lambda calculus does not have the control operators necessary to represent mu and mubar. mu is a sequencing operator, mubar is callcc.

Defunctionalizing the continuation. [https://www.brics.dk/RS/07/7/BRICS-RS-07-7.pdf](https://www.brics.dk/RS/07/7/BRICS-RS-07-7.pdf)

When we evaluated the lambda calculus, it is easiest to write this in a recursive form. Dealing with trees often feels easiest in recursive form, although I suppose maybe a visitor pattern is ok too. But that's still recursive. function calls and recursion is a kind of control flow and a facility that many languages provide. 

Any example of recursion can be turned into an iterative looking thing by maintaining your own call stack, basically reimplementing this feature. However, you may have some wisdom or optimization that might be obvious to you that the compiler would not know. Perhaps you don't need a full call stack. Perhaps you know how to reuse memory in a clever way. Perhaps you know certain things don't need to be maintained. These are all difficult for the compiler in general to infer, and in fact probably can't because for general purpose use they wouldn't even be correct. 

Defunctionalizing is a brother to closure conversion. Functions pointers are fine in C. We have first class functions in that sense. But if you close over free variables, that's a little less easy. One makes a record of a function pointer and 

Is my tendency to convert R -> R functions and think of them as parametrized polynomials or samples a form of defunctionalization? Could defunctionalization adn refunctionalization give intuition to how to deal with higher order differentiayion

Pointers are rather odd from a conceptual point of view. They assume this global referencing space. Defunctionalization instead of have a point, has a tag value. So the lambda type becomes equivalent to an algebraic data type.

Defunctionalizaion can be used to serialize functions. I think the first thing to come to mind is to just ship code over the network. See the next point.

A curious point. If we expand our mind, what we are often doing is looking at the real source code. Source code of functions is a perfectly acceptable seeming format for functions. And then we need an intepreter. Which is the defunctionalized apply function. So perhaps defunctionalization can be thought of as an extremely condensed first order representation of functions starting from the complete syntax tree. Like if you saw that a data type never had 95% of it's constructors used, you could just trim them? Or if a tree data type only had 3 actual trees in use. It might also be considered (shocker) a form of partial evaluation? na maybe not.

Defunctionalization and church boehm encodings. Is defunctionalization achieve by looking at use sites or creation sites of functions?

I guess using ADT gives us currying of our defunctionalized data types for free?

Refunctionalization. If a type is only used by a single interpretation function, it can be refunctionalized. This is because functions are a data type with a single interface: applying them to arguments.

Richard Eisenberg used defunctionalization in the singleton's library becayse haskell's typelevel doesn't really have higher order functions available [https://typesandkinds.wordpress.com/2013/04/01/defunctionalization-for-the-win/](https://typesandkinds.wordpress.com/2013/04/01/defunctionalization-for-the-win/)

Hmm. They claim that abstract machine operate directly on syntax, whereas virtual machines operate on intermediate languages requiring compilation

[https://ulrichschoepp.de/Docs/modules_tr.pdf](https://ulrichschoepp.de/Docs/modules_tr.pdf) Krishnamswami has some interesting suggestions at the bottom of Jimmy's asrticle [https://blog.sigplan.org/2019/12/30/defunctionalization-everybody-does-it-nobody-talks-about-it/](https://blog.sigplan.org/2019/12/30/defunctionalization-everybody-does-it-nobody-talks-about-it/)

In order to compile, we need to inject programs into initial states of the machines. Staged programming is a way to remove the overhead of this. See krishnamswami yallop. Why does it matter if you're going to a machine rep if you're just interpreting into core constructs anyway?

We can take a physical perspective that at the moment not withstanding any hypothetical dna computers or whatever, the only technology that scales in time and speed is electronics. A commonly used abstraction in this domain is that of the digital circuit. They are controlled by clock signals for which the circuit takes on states and then next states. 

Higher up the stack, we have the abstractions available from C. We have the abstraction of functions calls, the low level details of the stack abstracted away by lagnauge facilities, often the ability to malloc and free.



[https://caml.inria.fr/pub/papers/xleroy-zinc.pdf](https://caml.inria.fr/pub/papers/xleroy-zinc.pdf) Leroy describes the zinc machine and basically a whole ml implementation. Very interesting 

Dybvig thesis

Lisp in small pieces of obscure. He is so entrenched as a lisp expert

Henry Baker seems nuts. The Cheney on the MTA 

[https://tidsskrift.dk/brics/article/download/21784/19215](https://tidsskrift.dk/brics/article/download/21784/19215) - Danvy compilter

[https://www.theseus.fi/bitstream/handle/10024/166119/Nguyen_Anh%20.pdf;jsessionid=B320E037D6B6F7760E3BAE1C2A287F94?sequence=2](https://www.theseus.fi/bitstream/handle/10024/166119/Nguyen_Anh%20.pdf;jsessionid=B320E037D6B6F7760E3BAE1C2A287F94?sequence=2) bachelor thesis doing tiger compiler to llvm

Leroy Imp to stack machine [https://deepspec.org/event/dsss17/leroy-dsss17.pdf](https://deepspec.org/event/dsss17/leroy-dsss17.pdf) in coq.

[https://semantic-domain.blogspot.com/2020/02/thought-experiment-introductory.html](https://semantic-domain.blogspot.com/2020/02/thought-experiment-introductory.html) Neel Krishnaswami's hypotehtiocal coompiler course

