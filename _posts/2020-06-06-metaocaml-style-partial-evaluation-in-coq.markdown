---
author: philzook58
comments: true
date: 2020-06-06 23:44:18+00:00
layout: post
link: https://www.philipzucker.com/metaocaml-style-partial-evaluation-in-coq/
slug: metaocaml-style-partial-evaluation-in-coq
title: MetaOCaml style Partial Evaluation in Coq
wordpress_id: 2763
categories:
- Formal Methods
tags:
- coq
- metaprogramming
---




[MetaOCaml](http://okmij.org/ftp/ML/MetaOCaml.html) is a very cool system for partial evaluation. I'm very jealous.







If one chooses to ignore the proof aspects of Coq for a moment, it becomes a bizarre Ocaml metaprogramming system on insane steroids. Coq has very powerful evaluation mechanisms built in. Why not use these to perform partial evaluation?





![](/assets/piglegs-1024x640.png)Let's put some legs on this pig. Artwork courtesy of [David](https://davidtersegno.wordpress.com/)





We had a really fun project at work where we did partial evaluation in Coq and I've been tinkering around with how to make the techniques we eventually stumbled onto there less ad hoc feeling.







A problem I encountered is that it is somewhat difficult to get controlled evaluation in Coq. The fastest evaluation tactics [vm_compute and native_compute](https://coq.inria.fr/refman/proof-engine/tactics.html#coq:tacv.vm-compute) do not let you protect values from unfolding. There is a construct that is protected though. Axioms added to Coq cannot be unfolded by construction, but can be extracted. So I think a useful mantra here is axioms ~ code. 






    
    
```

Require Import Extraction.
Axiom PCode : Type -> Type.
Extract Constant PCode "'a" => "'a".

Axiom block : forall {a : Type}, a -> PCode a.
Extract Inlined Constant block => "".
```








It is useful to mark what things you expect to run and which you expect to block execution in the type. You can mark everything that is opaque with a type `PCode`. `block` is a useful combinator. It is _not_ a `quote` combinator however, as it will allow evaluation underneath of it.  Nothing however will be able to inspect a blocked piece of code. It's amusing that the blocking of computation of axioms is exactly what people dislike, but here it is the feature we desire. PCode is short for partial code indicating that it is possible for evaluation to occur within it. We'll see a `Code` that is more similar to MetaOcaml's later.







It is a touch fishy to extract `block` as nothing `""` rather than an identity function `(fun x -> x)`. It is rather cute though, and I suspect that you won't find `block` occurring in  a higher order context although I could easily be wrong (ahhh the sweet dark freedom of ignoring correctness). If this makes you queasy, you can put the function in, which is likely to compiled away, especially if you use the flambda switch. Not as pretty an output though.







We can play a similar extraction game with two HOAS-ish combinators.






    
    
```

Axiom ocaml_lam : forall {a b: Type}, (PCode a -> PCode b) -> PCode (a -> b).
Extract Inlined Constant ocaml_lam => "".

Axiom ocaml_app : forall {a b : Type},  PCode (a -> b) -> PCode a -> PCode b.
Extract Inlined Constant ocaml_app => "".
```








Here are some examples of other primitives we might add. The extra imports makes extraction turn nat into the native Ocaml int type, which is nice. It is not made so clear in the Coq manual that you should use these libraries to get good extraction of some standard types (perhaps I missed it or should make a pull request).  You can find the full set of such things here: [https://github.com/coq/coq/tree/master/theories/extraction](https://github.com/coq/coq/tree/master/theories/extraction)






    
    
```

From Coq.extraction Require Import ExtrOcamlBasic ExtrOcamlNatInt.
Axiom ocaml_add : PCode nat -> PCode nat -> PCode nat.
Extract Inlined Constant ocaml_add => "(+)".
Axiom ocaml_mul : PCode nat -> PCode nat -> PCode nat.
Extract Inlined Constant ocaml_mul => "(*)".
```








If we had instead used the Coq definition of `nat` addition, it wouldn't be protected during `vm_compute`, even if we wrapped it in `block`. It would unfold plus into it's recursive definition, which is not what you want for extraction. We want to extract (+) to native ocaml (+). 







You can add in other primitives as you see fit. Some things can get by merely using `block`, such as lifting literals.







Here is a very simplistic unrolling of a power  function with a compile time known exponent, following[ Kiselyov's lead](http://okmij.org/ftp/ML/MetaOCaml.html#using).






    
    
```

Fixpoint pow1 (n : nat) (x : PCode nat) : PCode nat :=
  match n with
  | O => block 1
  | S O => x
  | S n' => ocaml_mul x (pow1 n' x)
  end.

Definition pow2 (n : nat) : PCode (nat -> nat) := ocaml_lam (fun x => pow1 n x).

Definition compilepow : PCode (nat -> nat) := Eval native_compute in pow2 4.
Extraction compilepow.
(*

(** val compilepow : (int -> int) pCode **)

let compilepow =
   (fun x -> (*) x ((*) x ((*) x x)))

*)
```








What about if you want a quasiquoting interface though? Well here is one suggestion. The same code should become either PCode or more ordinary Coq values depending on whether you decide to quote it or not. So you want overloadable syntax. This can be achieved via a typeclass.






    
    
```

(* No, I don't really know what Symantics means. Symbolic semantics? It's an Oleg-ism.
*)
Class Symantics (repr : Type -> Type) :=
  {
  lnat : nat -> repr nat;
  lbool : bool -> repr bool;
  lam : forall {a b}, (repr a -> repr b) -> repr (a -> b);
  app : forall {a b},  repr (a -> b) -> repr a -> repr b;
  add : repr nat -> repr nat -> repr nat;
  mul : repr nat -> repr nat -> repr nat
  }.

```







    
    
```

(* A simple do nothing newtype wrapper for the typeclass *)
Record R a := { unR : a }.
Arguments Build_R {a}.
Arguments unR {a}.
(* Would Definition R (a:Type) := a. be okay? *)

Instance regularsym : Symantics R :=
  {|
  lnat := Build_R;
  lbool := Build_R;
  lam := fun a b f => Build_R (fun x => unR (f (Build_R (a:= a) x)));
  app := fun _ _ f x => Build_R ((unR f) (unR x));
  add := fun x y => Build_R ((unR x) + (unR y));
  mul := fun x y => Build_R ((unR x) * (unR y));
  |}.


Instance codesym : Symantics PCode := 
  {|
  lnat := block;
  lbool := block;
  lam := fun a b => ocaml_lam (a := a) (b := b);
  app := fun a b => ocaml_app (a := a) (b := b);
  add := ocaml_add;
  mul := ocaml_mul
  |}.


```








Now we've overloaded the meaning of the base combinators. The type `PCode` vs `R` labels which "mode" of evaluation we're in, "mode" being which typeclass instance we're using. Here are two combinators for quasiquoting that were somewhat surprising to me, but so far seem to be working. `quote` takes a value of type `a` being evaluated in "`Code` mode" and makes it a value of type `Code a` being evaluated in "`R` mode".  And `splice` sort of undoes that. I would have used the MetaOcaml syntax, but using periods in the notation seemed to make coq not happy.






    
    
```

Definition Code : Type -> Type := fun a => R (PCode a).

Definition quote {a}  : PCode a -> Code  a := Build_R.
Definition splice {a} : Code a  -> PCode a := unR.

Declare Scope quote_scope.
Notation "<' x '>" := (quote x) : quote_scope.
Notation "<, x ,>" := (splice x) : quote_scope.

Notation "n + m" := (add n m) : quote_scope.
Notation "n * m" := (mul n m) : quote_scope.
```








Now you can take the same version of code, add quote/splice annotations and get a partially evaluated version. The thing doesn't type check if you don't add the appropriate annotations. 






    
    
```

Open Scope quote_scope.

Fixpoint pow1' (n : nat) (x : Code nat) : Code nat :=
  match n with
  | O => quote (lnat 1)
  | S O => x
  | S n' => <' <, x ,> * <, pow1' n' x ,> '>
  end.

Definition pow2' (n : nat) : Code (nat -> nat) := <' lam (fun x => <, pow1' n <' x '> ,> ) '>.

Definition compilepow' : Code (nat -> nat) := Eval native_compute in pow2' 4.
Extraction compilepow'.

(* Same as before basically.
(** val compilepow' : (int -> int) code **)

let compilepow' =
   (fun x -> (*) x ((*) x ((*) x x)))
*)
```








Coolio.







### Increasingly Scattered Thoughts







With more elbow grease is this actually workable? Do we actually save anything over explicit language modelling with data types? Are things actually hygienic and playing nice? Not sure.







We could also give notations to `lam` and the other combinators. Idiom brackets [https://wiki.haskell.org/Idiom_brackets](https://wiki.haskell.org/Idiom_brackets)  might be nice for `app`. I am a little queasy going overboard on notation. I generally speaking hate it when people do stuff like this.







Monad have something to do with partial evaluation. Moggi's [original paper](https://core.ac.uk/download/pdf/21173011.pdf) on monads seems to have partial evaluation in mind.






    
    
```

(* This is moggi's let. *)
Axiom ocaml_bind : forall {a b}, PCode a -> (a -> PCode b) -> PCode b.
Extract Inlined Constant ocaml_bind => "(fun x f -> f x)".
```








Doing fix: playing nice with Coq's fix restrictions is going to be a pain. Maybe just gas it up?







`match` statements might also suck to do in a dsl of the shown style. I supposed you'll have to deal with everything via typeclass dispatched recursors / pattern matchers. Maybe one notation per data type? Or mostly stick to if then else and booleans. :(







Quote and splice can also be overloaded with another typeclass such that they just interpret completely into R or the appropriate purely functionally defined Gallina monad to emulate the appropriate effects of interest. This would be helpful for verification and development purposes as then the entire code can be proved with and evaluated in Coq.







Extracting arrays, mutable refs, for loops. All seems possible with some small inlined indirections that hopefully compile away. I've been finding [godbolt.org ](https://godbolt.org/)interesting to look at to see what flambda can and can't do. 







Do I need to explcitly model a World token or an IO monad or is the Code paradigm already sufficiently careful about order of operations and such?







Some snippets






    
    
```


Extract Constant ref "'a" => "'a ref".
(* make_ref     =>     "ref*)
Axiom get_ref : forall a, ref a -> World -> a * World.
Extract Constant get_ref => "fun r _ -> (!r  ,())".
Axiom set_ref : forall a, ref a -> a -> World -> unit * World.
Extract Constant set_ref => "fun r x _ -> let () = r := x in (() , ())".


Axiom Array : Type -> Type.
Extract Constant Array "'a" => "'a array".

Axiom make : forall {a : Type}, Code nat -> Code a -> Code World -> Code (Array a  *  World).

Extract Constant make => "fun i def _ -> ( make i def , ())".
Axiom get : forall a, Array a -> nat -> World -> a * World.
Extract Constant get => "fun r i _ -> (r.(i)  ,())".
Axiom set : forall a, Array a -> nat -> a -> World -> unit * World.
Extract Constant set => "fun r i x _ -> let () = r.(i) <- x in (() , ())".
```








MetaOCaml is super cool. The quote splice way of building of the exact expressions you want feels nice and having the type system differentiate between Code and static values is very useful conceptually. It's another instance where I feel like the types really aid the design process and clarify thinking. The types give you a compile time guarantee of what will and won't happen.







There are other systems that do compile time stuff. Types themselves are compile time. Some languages have const types, which is pretty similar. Templates are also code generators. Macros.







Why Coq vs metaocaml? 







  * MetaOcaml doesn't have critical mass.  Its ocaml switch lags behind the mainline. Coq seems more actively developed.
  * Possible verification and more powerful types (at your peril. Some may not extract nice)
  * One can go beyond purely generative metaprogamming since Ltac (and other techniques) can inspect terms.
  * Typeclasses
  * Can target more platforms. Haskell, Scheme, possibly C, fpgas?






However, Metaocaml does present a much more ergonomic, consistent, well founded interface for what it does.







One needs to have some protected structure in coq that represents a syntax tree of your intended ocaml expression. One natural choice would be a data type to represent this AST.







You also want access to possibly impure abilities of ocaml like mutation, errors, loops, arrays, and unbounded recursion that don't have direct equivalents in base Gallina. You can model the purely functional versions of these things, but you don't persay want to extract the purely functional versions if you're seeking the ultimate speed.







Why Finally Tagless Style. Anything you can do finally taglessly you can do in initial style. 







  * Positivity restrictions make some things difficult to express in Coq data types. You can turn these restrictions off, at your peril. Raw axiomatic fixpoints and HOAS without PHOAS become easier
  * Ultimately we need to build both a data type and an interpreter. A little bit using finally tagless cuts out the middle man. Why have a whole extra set of things to write?
  * Finally tagless style is open. You can add new capabilities without having to rewrite everything everywhere






Downsides







  * More confusing
  * Optimizations are harder
  * Is the verification story shot?






I guess ultimately there might not be a great reason. I just wandered into it. I was doing Kiselyov stuff, so other Kiselyov stuff was on the brain. I could make a DSL with Quote and Splice constructors.







#### Partial Evaluation Links







Typed Template Haskell gives you similar capabilities if that is more of your jam [https://www.philipzucker.com/a-little-bloop-on-typed-template-haskell/](https://www.philipzucker.com/a-little-bloop-on-typed-template-haskell/)







The MetaOcaml book - Kiselyov [http://okmij.org/ftp/meta-programming/tutorial/index.html](http://okmij.org/ftp/meta-programming/tutorial/index.html)







[http://okmij.org/ftp/tagless-final/JFP.pdf](http://okmij.org/ftp/tagless-final/JFP.pdf) Finally Tagless, Partially Evaluated is a paper I come back to. This is both because the subject matter is interesting, it seems to hold insights, and that it is quite confusing and long. I think there are entangled objectives occurring, chronologically this may be an early exposition of finally tagless style, for which it is not the most pedagogical reference.







Jason Gross, Chlipala, others? . Coq partial evaluation. Once you go into plugin territory it's a different game though. [https://people.csail.mit.edu/jgross/personal-website/papers/2020-rewriting-popl-draft.pdf](https://people.csail.mit.edu/jgross/personal-website/papers/2020-rewriting-popl-draft.pdf)







Partial Evaluation book - Jones Sestoft Gomard [https://www.itu.dk/people/sestoft/pebook/jonesgomardsestoft-a4.pdf](https://www.itu.dk/people/sestoft/pebook/jonesgomardsestoft-a4.pdf)







Nada Amin, Tiark Rompf. Two names to know [https://scala-lms.github.io/](https://scala-lms.github.io/) scala partial evaluation system [https://www.youtube.com/watch?v=QuJ-cEvH_oI](https://www.youtube.com/watch?v=QuJ-cEvH_oI)







Strymonas - a staged streaming library [https://strymonas.github.io/](https://strymonas.github.io/)







Algebraic staged parsing - [https://www.cl.cam.ac.uk/~nk480/parsing.pdf](https://www.cl.cam.ac.uk/~nk480/parsing.pdf)







Nielson and Nielson - Two level functional languages book







[https://dl.acm.org/doi/10.1145/141478.141483](https://dl.acm.org/doi/10.1145/141478.141483) - Improving binding times without explicit CPS-conversion. This bondorf paper is often cited as the why CPS helps partial evaluation paper







Modal logic. Davies and Pfenning. Was a hip topic. Their modal logic is something a bit like metaocaml. "Next" stage has some relationship to Next modal operator. Metaocaml as a proof language for intuitinisitc modal logic.







Partial evaluation vs optimizing compilers. It is known that CPS tends to allow the internals of compilers to make more optimizations. The obvious optimizations performed by a compiler often correspond to simple partial evaluations. Perhaps to get a feeling for where GHC gets blocked, playing around with an explicit partial evaluation system is useful.







An unrolled power in julia. It is unlikely I suspect that you want to use this technique to achieve performance goals. The Julia compiler itself is probably smarter than you unless you've got some real secret sauce.  







## Rando (or ARE THEY!?!) continuation links







continuations and partial evaluation are like jam and peanut butter. 







I've been digging into the continuation literature a bit







William byrd call/cc tutorial [https://www.youtube.com/watch?v=2GfFlfToBCo](https://www.youtube.com/watch?v=2GfFlfToBCo)







Kenichi Asai - Delimitted continuations for everyone [https://www.youtube.com/watch?v=QNM-njddhIw](https://www.youtube.com/watch?v=QNM-njddhIw)







  * [http://okmij.org/ftp/continuations/](http://okmij.org/ftp/continuations/)
  * [http://blog.sigfpe.com/2008/12/mother-of-all-monads.html](http://blog.sigfpe.com/2008/12/mother-of-all-monads.html)
  * [https://gist.github.com/lexi-lambda/d97b8187a9b63619af29689e9fa1b880](https://gist.github.com/lexi-lambda/d97b8187a9b63619af29689e9fa1b880)
  * [https://www.cs.utah.edu/plt/publications/icfp07-fyff.pdf](https://www.cs.utah.edu/plt/publications/icfp07-fyff.pdf)






Which of the many Danvy papers is most relevant







  * Defunctionalization and refunctionalization - Defunctionalize the continuation, see Jimmy's talk [https://dl.acm.org/doi/abs/10.1145/773184.773202](https://dl.acm.org/doi/abs/10.1145/773184.773202)  and 
  * [http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.6.2739&rep=rep1&type=pdf](http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.6.2739&rep=rep1&type=pdf) Continuation based partial evaluations 1995
  * https://dl.acm.org/doi/pdf/10.1145/91556.91622 1990 abstracting control
  * Abstract machines = Evaluators https://dl.acm.org/doi/pdf/10.1145/888251.888254 Functional correspondence 2003
  * https://www.researchgate.net/profile/Olivier_Danvy/publication/226671340_The_essence_of_eta-expansion_in_partial_evaluation/links/00b7d5399ecf37a658000000/The-essence-of-eta-expansion-in-partial-evaluation.pdf Essence of Eta expansion (1995) Reference of "the trick"
  * Representing control (1992) https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.46.84&rep=rep1&type=pdf Explains plotkin translation of CPS carefully. How to get other operators






Names to look out for: Dybvig, Felleison, Oleg, Filinksi, Asai, Danvy, Sabry







[https://github.com/rain-1/continuations-study-group/wiki/Reading-List](https://github.com/rain-1/continuations-study-group/wiki/Reading-List) Great reading list







What are the most interesting Oleg sections.







CPS. Really this is converting a syntax tree of lambda calculus to one of another type. This other type can be lowered back down to lambda calculus.







Control constructs can fill in holes in the CPS translation. 







Evaluation context. Contexts are terms with a single hole. Variables can also be used to show holes so therein lies some ocnfusion.







Abstract Machines







Ben pointed out that Node is in continuation passing style







To what degree are monads and continuations related? [http://hjemmesider.diku.dk/~andrzej/papers/RM-abstract.html](http://hjemmesider.diku.dk/~andrzej/papers/RM-abstract.html) Mother of all monads.







Certainly error handling and escape are possible with continuation







Call-cc is as if the compiler converts to cps, and then call-cc grabs the continuation for you







call-cc allows you to kind of pull a program  inside out. It's weird.







Compiling to continuations book







Lisp in Small Pieces







CPSing a value x    ~     \f -> f x. 







[https://homepages.inf.ed.ac.uk/wadler/papers/papers-we-love/reynolds-discoveries.pdf](https://homepages.inf.ed.ac.uk/wadler/papers/papers-we-love/reynolds-discoveries.pdf) - The discoveries of continuations - Reynolds. Interesting bit of history about the discovery in the 60s/70s









