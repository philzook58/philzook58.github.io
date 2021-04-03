I picked bidirectional typechecking for reading group

The fool.


It has something to do with focusing.

https://twitter.com/puffnfresh/status/1377474203444637701?s=20

http://noamz.org/thesis.pdf

https://consequently.org/papers/dggl.pdf

https://personal.cis.strath.ac.uk/neil.ghani/papers/ghani-jfcs09.pdf

Positive and negative types

Focusing

The two G and D categories in Harrop/Horn formula

Positivityv checking

Covaraince and contravaraince

hmm. Harper seems to suggest a positive v neagtive product type is a lazy vs strict distinction
https://ncatlab.org/nlab/show/product+type - 

https://ncatlab.org/nlab/show/sum+type - need multiple sequents for 


Linear logic.

Positive is "charactersize " by introductions. Plays nice with eager evaluation
Negative is "characterized" by eliminations. Plays "nice" with lazy evaluation

Introduction rules, elimination rules AND computation rules?

Proof search vs Preoof normalization semantics.

focussing and prolog

hmm harper actually has a chapter on classical logic dynamics

Bidrectional typing
Type synthesis can be interleaved with type checking


Inference rules: What is their computational reading/encoding?
The notation is extremely vague if this is your desire.


1. The expression below the line defines a relation.

Relations may be represented different ways
R a b c
Am i mixing types and expressions
1. [(a, b, c)] - explicit list (possibly infinite)
2. a -> b -> c -> bool  (decidable or partial depending on language) indicator function
3. Halfsies. a -> [(b,c)], a -> b -> [c],  in this sense a -> b -> c -> bool is really a -> b -> c -> [()]
3. a -> b -> c -> Prop -- a formula
5. explicit data type. data Rel = | True | False | And (Rel) (Rel) | Or | 
4. R(A,B,C). -- prolog
5. C C++, Java, Python? Do they give any new ideas?


This notion of modes is essentially the "Halfsies" notion.
Bidirectional typechecking defines the relation not between

A typing judgement is a relation between contexts, expressions, and types.
Expressions have types. Values have types. These are distinct notions.
Value as a meta notion vs Value as a subclass of expressions.


(tenv, expr, typ ) -> true
(tenv, expr) -> Maybe typ



