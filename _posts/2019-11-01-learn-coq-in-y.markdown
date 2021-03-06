---
author: philzook58
comments: true
date: 2019-11-01 15:34:05+00:00
layout: post
link: https://www.philipzucker.com/learn-coq-in-y/
slug: learn-coq-in-y
title: Learn Coq in Y
wordpress_id: 2465
categories:
- Formal Methods
tags:
- coq
---




Edit: It's up! [https://learnxinyminutes.com/docs/coq/](https://learnxinyminutes.com/docs/coq/)







I've been preparing a Learn X in Y tutorial for Coq. [https://learnxinyminutes.com/](https://learnxinyminutes.com/)







I've been telling people this and been surprised by how few people have heard of the site. It's super quick intros to syntax and weirdness for a bunch of languages with inline code tutorials.  
I think that for me, a short description of that mundane syntactic and programming constructs of coq is helpful.  
Some guidance of the standard library, what is available by default. And dealing with Notation scopes, which is a pretty weird feature that most languages don't have.   
The manual actually has all this now. It's really good. Like check this section out [https://coq.inria.fr/refman/language/coq-library.html](https://coq.inria.fr/refman/language/coq-library.html) . But the manual is an intimidating documents. It starts with a BNF description of syntax and things like that. The really useful pedagogical stuff is scattered throughout it. 







Anyway here is my draft (also here [https://github.com/philzook58/learnxinyminutes-docs/blob/master/coq.html.markdown](https://github.com/philzook58/learnxinyminutes-docs/blob/master/coq.html.markdown) where the syntax highlighting isn't so janked up). Suggestions welcome. Or if this gets accepted, you can just make pull requests






    
    
```coq


---
language: Coq
filename: learncoq.v
contributors:
    - ["Philip Zucker", "http://www.philipzucker.com/"]
---

The Coq system is a proof assistant. It is designed to build and verify mathematical proofs. The Coq system contains the functional programming language Gallina and is capable of proving properties about programs written in this language.

Coq is a dependently typed language. This means that the types of the language may depend on the values of variables. In this respect, it is similar to other related languages such as Agda, Idris, F*, Lean, and others. Via the Curry-Howard correspondence, programs, properties and proofs are formalized in the same language.

Coq is developed in OCaml and shares some syntactic and conceptual similiarity with it. Coq is a language containing many fascinating but difficult topics. This tutorial will focus on the programming aspects of Coq, rather than the proving. It may be helpful, but not necessary to learn some OCaml first, especially if you are unfamiliar with functional programming. This tutorial is based upon its OCaml equivalent

The standard usage model of Coq is to write it with interactive tool assistance, which operates like a high powered REPL. Two common such editors are the CoqIDE and Proof General Emacs mode.

Inside Proof General `Ctrl+C <enter>` will evaluate up to your cursor.


```coq
(*** Comments ***)

(* Comments are enclosed in (* and *). It's fine to nest comments. *)

(* There are no single-line comments. *)

(*** Variables and functions ***)

(* The Coq proof assistant can be controlled and queried by a command language called 
   the vernacular. Vernacular keywords are capitalized and the commands end with a period.
   Variable and function declarations are formed with the Definition vernacular. *)

Definition x := 10.

(* Coq can sometimes infer the types of arguments, but it is common practice to annotate
   with types. *)

Definition inc_nat (x : nat) : nat := x + 1.

(* There exists a large number of vernacular commands for querying information. 
   These can be very useful. *)

Compute (1 + 1). (* 2 : nat *) (* Compute a result. *)

Check tt. (* tt : unit *) (* Check the type of an expressions *)

About plus. (* Prints information about an object *)

(* Print information including the definition *)
Print true. (* Inductive bool : Set := true : Bool | false : Bool *)  

Search nat. (* Returns a large list of nat related values *)
Search "_ + _". (* You can also search on patterns *)
Search (?a -> ?a -> bool). (* Patterns can have named parameters  *)
Search (?a * ?a).

(* Locate tells you where notation is coming from. Very helpful when you encounter
   new notation. *)
Locate "+". 

(* Calling a function with insufficient number of arguments
   does not cause an error, it produces a new function. *)
Definition make_inc x y := x + y. (* make_inc is int -> int -> int *)
Definition inc_2 := make_inc 2.   (* inc_2 is int -> int *)
Compute inc_2 3. (* Evaluates to 5 *)

(* Definitions can be chained with "let ... in" construct.
   This is roughly the same to assigning values to multiple
   variables before using them in expressions in imperative
   languages. *)
Definition add_xy : nat := let x := 10 in
                         let y := 20 in
                         x + y.


(* Pattern matching is somewhat similar to switch statement in imperative
   languages, but offers a lot more expressive power. *)
Definition is_zero (x : nat) :=
    match x with
    | 0 => true
    | _ => false  (* The "_" pattern means "anything else". *)
    end.


(* You can define recursive function definition using the Fixpoint vernacular.*)
Fixpoint factorial n := match n with
                        | 0 => 1
                        | (S n') => n * factorial n'
                        end.


(* Function application usually doesn't need parentheses around arguments *)
Compute factorial 5. (* 120 : nat *)

(* ...unless the argument is an expression. *)
Compute factorial (5-1). (* 24 : nat *)

(* You can define mutually recursive functions using "with" *)
Fixpoint is_even (n : nat) : bool := match n with
  | 0 => true
  | (S n) => is_odd n
end with
  is_odd n := match n with
  | 0 => false
  | (S n) => is_even n
              end.

(* As Coq is a total programming language, it will only accept programs when it can
   understand they terminate. It can be most easily seen when the recursive call is
   on a pattern matched out subpiece of the input, as then the input is always decreasing
   in size. Getting Coq to understand that functions terminate is not always easy. See the
   references at the end of the artice for more on this topic. *)

(* Anonymous functions use the following syntax: *)

Definition my_square : nat -> nat := fun x => x * x.

Definition my_id (A : Type) (x : A) : A := x.
Definition my_id2 : forall A : Type, A -> A := fun A x => x.
Compute my_id nat 3. (* 3 : nat *)

(* You can ask Coq to infer terms with an underscore *)
Compute my_id _ 3. 

(* An implicit argument of a function is an argument which can be inferred from contextual
   knowledge. Parameters enclosed in {} are implicit by default *)

Definition my_id3 {A : Type} (x : A) : A := x.
Compute my_id3 3. (* 3 : nat *)

(* Sometimes it may be necessary to turn this off. You can make all arguments explicit
   again with @ *)
Compute @my_id3 nat 3.

(* Or give arguments by name *)
Compute my_id3 (A:=nat) 3.

(*** Notation ***)

(* Coq has a very powerful Notation system that can be used to write expressions in more
   natural forms. *)
Compute Nat.add 3 4. (* 7 : nat *)
Compute 3 + 4. (* 7 : nat *)

(* Notation is a syntactic transformation applied to the text of the program before being
   evaluated. Notation is organized into notation scopes. Using different notation scopes allows for a weak notion of overloading. *)

(* Imports the Zarith module containing definitions related to the integers Z *)
Require Import ZArith. 

(* Notation scopes can be opened *)
Open Scope Z_scope.

(* Now numerals and addition are defined on the integers. *)
Compute 1 + 7. (* 8 : Z *)

(* Integer equality checking *)
Compute 1 =? 2. (* false : bool *) 

(* Locate is useful for finding the origin and definition of notations *)
Locate "_ =? _". (* Z.eqb x y : Z_scope *) 
Close Scope Z_scope.

(* We're back to nat being the default interpetation of "+" *)
Compute 1 + 7. (* 8 : nat *)

(* Scopes can also be opened inline with the shorthand % *)
Compute (3 * -7)%Z. (* -21%Z : Z *)

(* Coq declares by default the following interpretation scopes: core_scope, type_scope, 
   function_scope, nat_scope, bool_scope, list_scope, int_scope, uint_scope. You may also
   want the numerical scopes Z_scope (integers) and Q_scope (fractions) held in the ZArith
   and QArith module respectively. *)

(* You can print the contents of scopes *)
Print Scope nat_scope.
(*
Scope nat_scope
Delimiting key is nat
Bound to classes nat Nat.t
"x 'mod' y" := Nat.modulo x y
"x ^ y" := Nat.pow x y
"x ?= y" := Nat.compare x y
"x >= y" := ge x y
"x > y" := gt x y
"x =? y" := Nat.eqb x y
"x  a
                                                  end.

(* A destructuring let is available if a pattern match is irrefutable *)
Definition my_fst2 {A B : Type} (x : A * B) : A := let (a,b) := x in
                                                   a.

(*** Lists ***)

(* Lists are built by using cons and nil or by using notation available in list_scope. *)
Compute cons 1 (cons 2 (cons 3 nil)). (*  (1 :: 2 :: 3 :: nil)%list : list nat *)
Compute (1 :: 2 :: 3 :: nil)%list. 

(* There is also list notation available in the ListNotations modules *)
Require Import List.
Import ListNotations. 
Compute [1 ; 2 ; 3]. (* [1; 2; 3] : list nat *)


(* 
There are a large number of list manipulation functions available, lncluding:

• length
• head : first element (with default) 
• tail : all but first element
• app : appending
• rev : reverse
• nth : accessing n-th element (with default)
• map : applying a function
• flat_map : applying a function returning lists 
• fold_left : iterator (from head to tail)
• fold_right : iterator (from tail to head) 

 *)

Definition my_list : list nat := [47; 18; 34].

Compute List.length my_list. (* 3 : nat *)
(* All functions in coq must be total, so indexing requires a default value *)
Compute List.nth 1 my_list 0. (* 18 : nat *) 
Compute List.map (fun x => x * 2) my_list. (* [94; 36; 68] : list nat *)
Compute List.filter (fun x => Nat.eqb (Nat.modulo x 2) 0) my_list. (*  [18; 34] : list nat *)
Compute (my_list ++ my_list)%list. (*  [47; 18; 34; 47; 18; 34] : list nat *)

(*** Strings ***)

Require Import Strings.String.

Open Scope string_scope.

(* Use double quotes for string literals. *)
Compute "hi"%string.

(* Strings can be concatenated with the "++" operator. *)
Compute String.append "Hello " "World". (* "Hello World" : string *)
Compute "Hello " ++ "World". (* "Hello World" : string *)

(* Strings can be compared for equality *)
Compute String.eqb "Coq is fun!"%string "Coq is fun!"%string. (* true : bool *)
Compute ("no" =? "way")%string. (* false : bool *)

Close Scope string_scope.

(*** Other Modules ***)

(* Other Modules in the standard library that may be of interest:

• Logic : Classical logic and dependent equality
• Arith : Basic Peano arithmetic
• PArith : Basic positive integer arithmetic
• NArith : Basic binary natural number arithmetic
• ZArith : Basic relative integer arithmetic
• Numbers : Various approaches to natural, integer and cyclic numbers (currently axiomatically and on top of 2^31 binary words)
• Bool : Booleans (basic functions and results)
• Lists : Monomorphic and polymorphic lists (basic functions and results), Streams (infinite sequences
defined with co-inductive types)
• Sets : Sets (classical, constructive, finite, infinite, power set, etc.)
• FSets : Specification and implementations of finite sets and finite maps (by lists and by AVL trees)
• Reals : Axiomatization of real numbers (classical, basic functions, integer part, fractional part, limit, derivative, Cauchy series, power series and results,...)
• Relations : Relations (definitions and basic results)
• Sorting : Sorted list (basic definitions and heapsort correctness)
• Strings : 8-bits characters and strings
• Wellfounded : Well-founded relations (basic results)
 *)

(*** User-defined data types ***)

(* Because Coq is dependently typed, defining type aliases is no different than defining
   an alias for a value. *)

Definition my_three : nat := 3.
Definition my_nat : Type := nat.

(* More interesting types can be defined using the Inductive vernacular. Simple enumeration
   can be defined like so *)
Inductive ml := OCaml | StandardML | Coq.
Definition lang := Coq.  (* Has type "ml". *)

(* For more complicated types, you will need to specify the types of the constructors. *)

(* Type constructors don't need to be empty. *)
Inductive my_number := plus_infinity
                     | nat_value : nat -> my_number.
Compute nat_value 3. (* nat_value 3 : my_number *)


(* Record syntax is sugar for tuple-like types. It defines named accessor functions for
   the components *)
Record Point2d (A : Set) := mkPoint2d { x2 : A ; y2 : A }. 
Definition mypoint : Point2d nat :=  {| x2 := 2 ; y2 := 3 |}.
Compute x2 nat mypoint. (* 2 : nat *)
Compute mypoint.(x2 nat). (* 2 : nat *) 

(* Types can be parameterized, like in this type for "list of lists
   of anything". 'a can be substituted with any type. *)
Definition list_of_lists a := list (list a).
Definition list_list_nat := list_of_lists nat.

(* Types can also be recursive. Like in this type analogous to
   built-in list of naturals. *)

Inductive my_nat_list := EmptyList | NatList : nat -> my_nat_list -> my_nat_list.
Compute NatList 1 EmptyList. (*  NatList 1 EmptyList : my_nat_list *)

(** Matching type constructors **)

Inductive animal := Dog : string -> animal | Cat : string -> animal.

Definition say x :=
    match x with
    | Dog x => (x ++ " says woof")%string
    | Cat x => (x ++ " says meow")%string
    end.

Compute say (Cat "Fluffy"). (* "Fluffy says meow". *)

(** Traversing data structures with pattern matching **)

(* Recursive types can be traversed with pattern matching easily.
   Let's see how we can traverse a data structure of the built-in list type.
   Even though the built-in cons ("::") looks like an infix operator,
   it's actually a type constructor and can be matched like any other. *)
Fixpoint sum_list l :=
    match l with
    | [] => 0
    | head :: tail => head + (sum_list tail)
    end.

Compute sum_list [1; 2; 3]. (* Evaluates to 6 *)


(*** A Taste of Proving ***)
(* Explaining the proof language is out of scope for this tutorial, but here is a taste to
   whet your appetite. Check the resources below for more. *)

(* A fascinating feature of dependently type based theorem provers is that the same
  primitive constructs underly the proof language as the programming features.
  For example, we can write and prove the proposition A and B implies A in raw Gallina *)

Definition my_theorem : forall A B, A /\ B -> A := fun A B ab => match ab with
                                            | (conj a b) => a
                                                       end.

(* Or we can prove it using tactics. Tactics are a macro language to help build proof terms
   in a more natural style and automate away some drudgery. *)
Theorem my_theorem2 : forall A B, A /\ B -> A.
Proof.
  intros A B ab.  destruct ab as [ a b ]. apply a.
Qed.

(* We can prove easily prove simple polynomial equalities using the automated tactic ring. *)
Require Import Ring.
Require Import Arith.
Theorem simple_poly : forall (x : nat), (x + 1) * (x + 2) = x * x + 3 * x + 2.
  Proof. intros. ring. Qed.

(* Here we prove the closed form for the sum of all numbers 1 to n using induction *)

Fixpoint sumn (n : nat) : nat :=
  match n with
  | 0 => 0
  | (S n') => n + (sumn n')
  end.

Theorem sum_formula : forall n, 2 * (sumn n) = (n + 1) * n.
Proof. intros. induction n.
       - reflexivity. (* 0 = 0 base case *)
       - simpl. ring [IHn]. (* induction step *)
Qed.
```

With this we have only scratched the surface of Coq. It is a massive ecosystem with many interesting and peculiar topics leading all the way up to modern research.

## Further reading

* [The Coq reference manual](https://coq.inria.fr/refman/)
* [Software Foundations](https://softwarefoundations.cis.upenn.edu/)
* [Certfied Programming with Dependent Types](http://adam.chlipala.net/cpdt/)
* [Mathematical Components](https://math-comp.github.io/mcb/)
* [Coq'Art: The Calculus of Inductive Constructions](http://www.cse.chalmers.se/research/group/logic/TypesSS05/resources/coq/CoqArt/)
* [FRAP](http://adam.chlipala.net/frap/)












Bonus. An uneditted list of tactics. You'd probably prefer [https://pjreddie.com/coq-tactics/](https://pjreddie.com/coq-tactics/)






    
    
```



(*** Tactics ***)
 (* Although we won't explain their use in detail, here is a list of common tactics. *)

(* 

    * exact
    * simpl
    * intros
    * apply
    * assert
    * destruct
    * induction
    * reflexivity
    * rewrite
    * inversion
    * injection
    * discriminate
    * fold
    * unfold


        Tacticals
    * try
    * ;
        * repeat
        *



 Automatic
    * auto
    * eauto
    * tauto
    * ring
    * ring_simplify
    * psatz
    * lia
    * ria


LTac is a logic programming scripting language for tactics

       From Tatics chapter of LF
        intros: move hypotheses/variables from goal to context
reflexivity: finish the proof (when the goal looks like e = e)
apply: prove goal using a hypothesis, lemma, or constructor
apply... in H: apply a hypothesis, lemma, or constructor to a hypothesis in the context (forward reasoning)
apply... with...: explicitly specify values for variables that cannot be determined by pattern matching
simpl: simplify computations in the goal
simpl in H: ... or a hypothesis
rewrite: use an equality hypothesis (or lemma) to rewrite the goal
rewrite ... in H: ... or a hypothesis
symmetry: changes a goal of the form t=u into u=t
symmetry in H: changes a hypothesis of the form t=u into u=t
unfold: replace a defined constant by its right-hand side in the goal
unfold... in H: ... or a hypothesis
destruct... as...: case analysis on values of inductively defined types
destruct... eqn:...: specify the name of an equation to be added to the context, recording the result of the case analysis
induction... as...: induction on values of inductively defined types
injection: reason by injectivity on equalities between values of inductively defined types
discriminate: reason by disjointness of constructors on equalities between values of inductively defined types
assert (H: e) (or assert (e) as H): introduce a "local lemma" e and call it H
                                              generalize dependent x: move the variable x (and anything else that depends on it) from the context back to an explicit hypothesis in the goal formula

clear H: Delete hypothesis H from the context.
subst x: For a variable x, find an assumption x = e or e = x in the context, replace x with e throughout the context and current goal, and clear the assumption.
subst: Substitute away all assumptions of the form x = e or e = x (where x is a variable).
rename... into...: Change the name of a hypothesis in the proof context. For example, if the context includes a variable named x, then rename x into y will change all occurrences of x to y.
assumption: Try to find a hypothesis H in the context that exactly matches the goal; if one is found, behave like apply H.
contradiction: Try to find a hypothesis H in the current context that is logically equivalent to False. If one is found, solve the goal.
constructor: Try to find a constructor c (from some Inductive definition in the current environment) that can be applied to solve the current goal. If one is found, behave like apply c.
                                                                                       (* Dependent types. Using dependent types for programming tasks tends to be rather unergonomic in Coq. 
We briefly mention here as an advanced topic that there exists a more sophistictaed match statement that is needed for dependently typed. See for example the "Convoy" pattern.
*)

(*** Other topics ***)

(* Dependently Typed Programming - Most of the above syntax has its equivalents in OCaml. Coq also has the capability for full dependently typed programming. There is an extended pattern matching syntax available for this purpose.

   Extraction - Coq can be extracted to OCaml and Haskell code for their more performant runtimes and ecosystems
   Modules / TypeClasses - Modules and Typeclasses are methods for organizing code. They allow a different form of overloading than Notation
   Setoids - 
   Termination - Gallina is a total functional programming language. It will not allow you to write functions that do not obviously terminate. For functions that do terminate but non-obviously, it requires some work to get Coq to understand this.
   Coinductive - Coinductive types such as streams are possibly infinite values that stay productive.


 *)

```




