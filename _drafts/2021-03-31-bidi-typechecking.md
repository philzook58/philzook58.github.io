I picked bidirectional typechecking for reading group

The fool.


It has something to do with focusing? Hmm The review paper says explicitly it does not.



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


Checking is easy?
Inference is hard?

Is this always true?
Checking of application is hard
f x : b  because it needs to invent an inner type. 

We can make checking always go through with intense annotations. 

infertype below the line is good. It is producing information
infertype above the line is bad. It needs a information producing process to output

It almost feels like a constraint satisfaction problem to me.
Perhaps the more flexible notion of a prolog search with pruning.

We want to pick an ordering and infer/check for the rules such that 
they are well moded.
We want as many infers below lines and checks above lines as possible. These may be weighted by some notion of painfulness of annotation. Freqeuncy of usage * annotation size perhaps.
To require a synethsizing derivation is bad. To produce a synthesizing derivation is good.

The Pfenning recipe is a heuristic

Well moded : premise known.

The rules aren't independent of each other though? How does that hjapen?
Yes. The rules need to match up to each other.
Maybe really the cost is every annotation. which happens when there is a form that infers up top but checks below the line.

Of course, a language designer is not constrained to a fixed system. Adding extra forms,, or interesintg new
contexts or ways of thinkgin about things.



elimination forms are often in inference because there is an invented type

type-directed synthesis of programs is proof search.


1. principal judgement
2. elimination synethesize, introduction check. Elimination is usually above and introuducion usually below.
  This is counterintuitive, we have to step backward to step forward. WWe don't want synthesis above and check below.


A pile of introductions should just check? Carry the top level information through


subtyping :< often has input mode. It's easy to tell if things are subtypes than to come up with a maximal type persay


We don't want to dump information

The simply typed lambda calculus is kind of a bad example. It is so simple that really the nonbidirectional version does a pretty dang good job in raw prolog.


Inference rules: What is their computational reading/encoding?
The notation is extremely vague if this is your desire.


1. The expression below the line defines a relation.

Relations may be represented different ways
R a b c
Am I mixing types and expressions
1. [(a, b, c)] - explicit list (possibly infinite)
2. a -> b -> c -> bool  (decidable or partial depending on language) indicator function
3. Halfsies. a -> [(b,c)], a -> b -> [c],  in this sense a -> b -> c -> bool is really a -> b -> c -> [()]
3. type Rel a b c = a -> b -> c -> Prop -- a formula
5. explicit data type. data Rel = | True | False | And (Rel) (Rel) | Or |
4. R(A,B,C). -- prolog
5. C C++, Java, Python? Do they give any new ideas?


Ok but what about _Rules_. Different but related question.
1. Prolog clause. Problems
2. Coq Inductive data type
3. Cases in recursive function definitions
4. a pile of switch cases or whatever
5. Tactics -  th below -> ( [ th above ], [Pf above] -> Pf below ) 
6. LCF Recognizers - typ rule = [Pf up top] -> theore below -> Pf below - sometimes yuou need to give the shape of the thing you want below. Even all the above parts and the label of the rule might be insufficient. It is possible for this function to be partial / undecidable. Proof terms are a deep DSL recording these shallow moves.
7. You could make an argument for an inference rule being a relation of relations? A meta lifting.
8. rules with single things up top = executions of abstract machines


Inference rules are relations on syntactic forms?



This notion of modes is essentially the "Halfsies" notion.
Bidirectional typechecking defines the relation not between

A typing judgement is a relation between contexts, expressions, and types.
Expressions have types. Values have types. These are distinct notions.
Value as a meta notion vs Value as a subclass of expressions.


(tenv, expr, typ ) -> true
(tenv, expr) -> Maybe typ


type var = string
type expr = Var of var | Lam of var * expr | App of (expr * expr) | TT | Annot of (expr * typ)
type typ = Unit | Arr of typ * typ
type typ_ctx = (var * typ) list

type_check gamma = function
| Var v, 
| TT , Unit -> true
| e, t  -> let t' = type_infer gamma e in
           t = t'
and
type_infer gamma = function
| Var v -> lookup gamma v
| Annot e t -> let c = type_check gamma e t in
               if c then t else failwith "Bad annotation"
| App f x -> let Arr (a,b) = infer_type gamma f in
             let c = type_check gamma x a in
             if c then b else fail 
| _ -> failwith

Does it matter that we should return errors? I guess it does.

type_judge(Gamma, e,  type).
type_judge(Gamma, tt, unit).
type_judge(Gamma, lam(V,Body) , arr(A,B)) :- type_judge([ V -> A  | Gamma], Body , B ).
type_judge(Gamma, app(F,X) ,    )    :- 

mckinna mcbride gundry. tye inferencei n context
https://adam.gundry.co.uk/pub/type-inference-in-context/#:~:text=We%20consider%20the%20problems%20of,for%20implementing%20type%20inference%20algorithms.

Complete and easy
https://arxiv.org/pdf/1306.6032.pdf

FreezeML
https://www.pure.ed.ac.uk/ws/portalfiles/portal/142279783/FreezeML_EMRICH_DOA21022020_AFV.pdf

Nice simple tutorial
http://davidchristiansen.dk/tutorials/bidirectional.pdf

pfenning lecture notes
https://www.cs.cmu.edu/~fp/courses/15312-f04/handouts/15-bidirectional.pdf

He mentioned thaty a computational interpretation of inference rules requirtes modes
Symntax directed rules can be considered as checkers, since we can pattern match on the syntax and know what to do

What interesting problem can I use?
Well, interleaved moded predicates is interesting.


Mode correctness - not a notion of bidirectional type checking.

This is an interesting idea.
Take a prolog program that is ill formed.
Consider all possible modal forms. In recursiove calls, consider all possible modes to recrusviely call. Consider all orderings of right side preds too.
This is all mechanical enough it could be considered mode synthesis.
Perhaps + some test cases


rel(A,B) :- rel(A,C), rel(C,B).

rel+-(-A,+B) :- rel--, rel--

Trim all non well moded

Maybe I hsould use mercury?
Or swipl has a mode chekcing thing probably?
https://www.swi-prolog.org/pldoc/man?section=modes







