Partial Evaluation of SMT-LIB

I rather like SMT-LIB.

The ethos around it's use is that you use some system that will generate verification conditions. The verification conditions may be extremely unpalatable to human eyes.

I think this perspective can be a mistake.

It is possible and _fun_ to write problem DSLs in SMT-LIB itself.

# Partial Evaluation
It seems to be pretty common that SMT solvers run simplification passes over assertions. I suggest that this simplification pass can be seen as an pre-execution stage, similar to compile-time programming. There is no way Z3 is leaving behind expressions like `(+ 1 2)` before it starts branching search. That'd be insane.

As a stand-in for the pass, I use the Z3 `simplify` command, under the assumption that if simplify can strip out my DSL abstractions, so can the actual solve. This might not be true.

I quite like the MetaOcaml style discipline to typed metaprogramming. There is a type constructor called `code` which allows you to state which arguments and results are compile vs runtime. Different combinations of adding these annotations to functions are different kinds of partial evaluation.

In other systems, the type of code might just be `string` or an s-expression that will be run later. This is still good.

# Tools 

## define-fun

An idea that has been bugging me for a while is that I want SMT-LIB macros. I've thrown together a few prototypes trying to use Ocaml or Racket to do so, but my interest has petered out.

It is a

It is possible to remodel some uses of `forall` in terms a of a `define-fun`. In fact, SMT solvers try to find these transformations as macro-finder passes.

To say a relation is a function is to state `(forall (x) (exists (y) (R x y)))` adn `(forall (x y z) (=> (and (R x y) (R x z)) (= y z))`

To define a function is to state `(forall (x) (= (f x) definition_of_function))`.

Defining a function by cases 
```
(forall (x) (=> case1 (= (f x) definition_of_function)))
(forall (x) (=> case2 (= (f x) definition_of_function)))
...
```
where all the cases agree on their overlap and total. This is easiest to confirm if the cases are obviously disjoint.

There is a big difference if the definition is recursive or not (whether the definition_of_function contains a reference to `f`). A way to be sure that a function definition is well formed is to show that unrolling the definition will always eventually terminate.

Partial definitions vs partial functions.



## let
`let` is a wildly under appreciated construct in SMT-LIB. The bindings I've seen don't expose it. It's extremely useful for strucuring SMT-LIB in a readable way. 
Also the similarity of `let` and shadowing to mutational assignment makes the encoding of weakest precondition to .

# define-fun-rec

# lambda

True higher order reasoning is finicky at best. However, it is not unreasonable to expect the solver to be able to simplify an applied lambda to an argument. We should use lambdas only in such a way

# Arrays as environments
In many DSLs, there is some notion of variable. When you have a variable, typically you mean that somehow you can lookup the meaning of this variable in some environment. Directly modelling this is the way to deeply embed your DSL variables into

# Initial Encodings
A very natural way of trying to model a problem is to model an AST that can describe the problem and then worry about what to do with the AST later.

If you are in a language with algebraic datatypes like ocaml or haskell, this AST will probably be an algebraic datatype.

SMT-LIB does also contain algebraic datatypes and match expressions. Using `define-fun-rec` one can basically directly write the algorithm as one would in another language. 

# Final Encodings
# Modules and Tags
