


Lambda Prolog is very cool.

The relationship between datalog and prolog seems to be a source of interesting questions and insights. Take anything from one and ask how it could be applied in the other.

What is Lambda Datalog?

## Lambda Prolog Features
### HOAS
Well first off, we want to be able to instrospect lambda terms as objects. This is the true original meaning of Higher Order Abstract Syntax (HOAS). In functional languages, embedding lambdas in your datatype is called HOAS. These lambdas are not destructible.

```haskell
data HOAS = Lam (HOAS -> HOAS) | App HOAS HOAS | Lit Int

instance Show HOAS where
    show (Lam f) = "Lam <opaque>"
    show (App f x) = "(" ++ show f ++ show x ++ ")"
    show (Lit i) = show i 

eval (App (Lam f) x) = f x
eval x = x

main = print (eval (App (Lam $ \x -> x) (Lit 3)))
```

### Normalization
Normalization is ordinary. I chose to go for locally nameless style, where you turn de bruijn indices into gensymed fresh variables when you traverse under lambdas. This has the reputation of being the easiest to get right.

Normalization should happen outside of any hash cons and we should only store normalized terms.

Since I have no types on my lambda terms, there is no guarantee they will normalize if you're not careful. Probably it would be good to use a simply typed lambda calc as the object lang.


### Miller Matching
Unification is taking two terms with variables and figuring out if the variables can be instantiated with something to make the terms syntactically equal.
Pattern matching is taking a term with variables and one term with no variables and figuring out if the . Pattern matching is one way unification or Unification is two way pattern matching. Unification is a bit harder to understand and describe.

There is also a plethora of unification/pattern matching modulo X, where X may be equalities, assocativity, commutativity, alpha or beta equivalence and others. 

Unification of terms with lambdas in them is called higher order unification. It's a natural thing to consider if you are trying to generalize some things that worked in first order logic (resolution theorem proving, prolog) to higher order logic. It turns out that unification modulo beta reduction is undecidable and a hard problem. Not something you obviously want persay to be a small step in your deduction system.

There is a restriction from full beta reduction that is decidable. This fragment is sometimes called Miller Unification.

Datalog has pattern matching where prolog has unification. So we need to only consider Miller pattern matching.

It's actually surprisingly fairly simple.

Miller pattern matching is kind of the minimal of what is necessary for scopes to play nice with pattern variables.

Suppose I had the problem  `\x. F = \x. x`. What is a good answer for `F`? `x` you say? What the hell is `x`? The thing is that `F` is actually implicitly bound and it's implicitly bound _outside_ of the lambda because we're going to take the solution to F and use it somewhere else, again outside of the lambda. Explicitly we might write `exists F, \x. F = \x. x`. F therefore cannot refer to the variable. It would then have escaped it's scope.

If instead we have the problem `\x. F x = \x. x` we can solve this as `F = \y. y`. How did we do this? Well, really `F(x)` should be considered as a monolithic thing. Application of pattern variables should be considered distinct from regular application. The things that F is applied to are the bound quantities to which F may refer, smuggled in via a lambda in F itself.

So here is the basic procedure: Traverse down the pattern and term making sure things match as you go along. When you hit a `F(x,y,z,...)` in the pattern, it will match some term `t` in the matchee. If the only bound variables `t` contained are `x,y,z,...`, then `F` is `\x \y \z t`. If `t` contains a bound variable not in `F`'s application list, the pattern match fails. Essentially, we need to "reabstract" the bound pieces in the term `t` and the variables `F` is applied to in the pattern tell us what pieces we're allowed to "reabstract".

We could also consider allowing `F` to be applied to non bound things like `F(42)`. While we can "reabstract" `42`, this is not a great idea because pattern matching becomes nondeterministic again. Consider `F(42) = 42 + 42 + 42`. This has many solutions. `F = \x. 42 + 42 + 42`,  `F = \x. x + 42 + 42`,  `F = \x. 42 + x + 42`,  `F = \x. 42 + x + x`,  `F = \x. x + x + x` and so on. Maaaaybe you could say the first or last are "better" in some sense, but I'm skeptical.

So there you have it. In the Miller fragment, you annotate pattern variables explicitly with the bound variables you are allowing `F` to reabstract. This can be seen as only applying `F` to bound variables, but I prefer to thing of pattern application and regular application as distinct.







### Harrop


## Lambda Datalog
### Context Lattice


`ctx2 |- bar :-  ctx1 |- foo`

We could also perhaps read this as internalizing `ctx1 => foo`. They are related concepts. I think turnstile is the most appropriate. Turnstile is always some kind of metalevel lifting of `=>`


`bar(x) |- foo(y) :- (bar(x) => foo(y))`

Is an implication elimination rule

```
true |- bar(x) => foo(y)
------------------------
bar(x) |- foo(y) 
```

We can emulate this in souffle by attaching an extra ctx field to every relation.
```
// simple truncated context. Only allows one premise
.decl Ctx = True {} | Foo {x : number} | Bar {y : symbol} 

.decl foo(x : number, ctx : Ctx)
.decl bar(x : number, ctx : Ctx)

foo(x, y) <= foo(x, $True()) :- true.
bar(x, y) <= bar(x, $True()) :- true.


```

Contexts are related to provenance. They are tracking certain "marked" entities are in the proof tree. For example, we could want to have have a lattice that checks if a fact requires "foo(3)", ie every proof has a foo(3) somewhere in it.

The lattice in question is the anti-chain lattice of the powerset of facts.



### Datalog normal form
You can put datalog into normal form of
```
e :- a,b,c,d.
```

```
n1 :- a.
n2 :- n1, b.
n3 :- n2, c.
n4 :- n3, d.
e :- n4.
```

This perspective helps us understand breaking up higher implications.

```
c :- (b => a), d 
```
becomes
```
{a} |- a :- d.
ctx \ {a} |- c :- ctx |- b, in(a,ctx).
```

```
{a} |- a :- d.
ctx |- c :- {a u ctx} |- b.
```

### Questions
How to deal with universal quantification properly?
The only way universal variables leak in is via being asserted into the context.
So we _could_ label them according to position in the context.
Or it is just understood these vars are only meaningful modulo permutation.
And have a special mechanism.
And we need to be aware of this when we lower contexts.

We don't need to hash cons the context. That's a souffle requirement.
It's kind of nice _maybe_

When we join facts, we need to join their contexts, requiring solving for a permutation. Hmm. But are their fresh variables linked or not?
It doesn't matter?
