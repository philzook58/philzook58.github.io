---
title: Lambda MicroEgg
date: 2026-09-20
---

It's an egraph that supports well-scoped alpha aware binders.

Everything [old](https://www.philipzucker.com/egglog0/) is new again.

I made a tool that attaches my lifting e-graph ideas  [arxiv](https://arxiv.org/abs/2606.22734) [youtube](https://www.youtube.com/watch?v=h1CzZguA6DE) to an s-expression based frontend.

- repo <https://github.com/philzook58/lambda-microegg>
- wasm demo <https://www.philipzucker.com/lambda-microegg/> . The oooooold playbook.

It's heavily based around Max's [microegg](https://github.com/mwillsey/microegg) <https://pavpanchekha.com/blog/microegg.html> . But I added built in binders, higher order miller patterns, and capture avoiding substitution in right hand sides.

Here is using the binders for some $\sum$ rewrite rules. `@` marks `sum` as a unary binding form. `{?a x}` is Miller pattern notation. More on that below.

```python
%%file /tmp/sum.sexp

(insert (@sum x (@sum y (* 2 y))))
(rewrite (@sum x (* ?a {?b x})) 
         (* ?a (@sum x {?b x})))  ; constant factoring
(rewrite (@sum x ?a) (* ?a N))    ; constant sum
(rewrite (* ?a ?b) (* ?b ?a))     ; mul commutativity
(run 10)
(guard (@sum x (@sum y (* 2 y)))  (* 2 (* N (@sum x x))))
```

    Overwriting /tmp/sum.sexp

```python
! lambda-microegg /tmp/sum.sexp
```

    ; inserted e4
    ; rewrite 1 added
    ; rewrite 2 added
    ; rewrite 3 added
    ; ran 5 rounds, 17 unions: 9 classes, 22 e-nodes
    ; match 21.72µs, apply 14.991µs, rebuild 19.347µs
    ; guard passed

Here is an AC-10 saturation run. This is a reasonable no thinking way to kind of know perf you're in the ball park of. On my computer, egg is ~0.6s for a similar thing, so we're slower but not extremely so.

Since liftings are stored as a byte stolen from the u32 Id, there hopefully isn't really much overhead associated with them, especially if not used.

```python
%%file /tmp/basic.sexp

(insert (+ 1 (+ 2 (+ 3 (+ 4 (+ 5 (+ 6 (+ 7 (+ 8 (+ 9 10))))))))))
(rewrite (+ ?a ?b) (+ ?b ?a))
(rewrite (+ ?a (+ ?b ?c)) (+ (+ ?a ?b) ?c))
;(rewrite (+ (+ ?a ?b) ?c) (+ ?a (+ ?b ?c)))
(run 100)
```

    Overwriting /tmp/basic.sexp

```python
! lambda-microegg /tmp/basic.sexp
```

    ; inserted e18
    ; rewrite 1 added
    ; rewrite 2 added
    ; ran 9 rounds, 262291 unions: 1023 classes, 57012 e-nodes
    ; match 350.089112ms, apply 999.980826ms, rebuild 152.433662ms

# Lambda Free Higher Order Application

There is a tension between the typical first order notion of application `FOApp(Symbol, Vec<Id>)` and the higher order binary version `HOApp(Id,Id)`. The latter can be encoded into the former using a ubiquitout "app" symbol `(app (app f x) y)`. This is burdensome to write though, so I added a different constructor and notation `[]` which automatically curries and uses `HOApp`.

```python
%%file /tmp/comp.sexp

(insert [map [comp f g] [cons 3 nil]])

(rewrite [[comp ?f ?g] ?x] [?f [?g ?x]])                      ; comp definition
; (rewrite [map ?f [map ?g ?x]] [map [comp ?f ?g] ?x])          ; map fusion
(rewrite [map ?f [cons ?x ?xs]] [cons [?f ?x] [map ?f ?xs]])  ; map cons
(rewrite [map ?f nil] nil)                                      ; map nil
(run 3)
(guard [[comp f g] 3] [f [g 3]])

```

    Overwriting /tmp/comp.sexp

```python
! lambda-microegg /tmp/comp.sexp
```

    ; inserted e12
    ; rewrite 1 added
    ; rewrite 2 added
    ; rewrite 3 added
    ; ran 2 rounds, 4 unions: 16 classes, 19 e-nodes
    ; match 28.954µs, apply 8.015µs, rebuild 19.358µs
    ; guard passed

If I switch out in an AC saturation example the first order `()` for the higher order `[]`  there is a cost to it. But, perhaps with some optimizations (like precomputing ground ids in the pattern) this could be improved.

```python
%%file /tmp/ho_ac.sexp

(insert [+ 1 [+ 2 [+ 3 [+ 4 [+ 5 [+ 6 [+ 7 [+ 8 [+ 9 10]]]]]]]]]) 
(rewrite [+ ?a ?b] [+ ?b ?a])
(rewrite [+ ?a [+ ?b ?c]] [+ [+ ?a ?b] ?c])
;(rewrite [+ [+ ?a ?b] ?c] [+ ?a [+ ?b ?c]]) 
(run 100)
```

    Overwriting /tmp/ho_ac.sexp

```python
! lambda-microegg /tmp/ho_ac.sexp
```

    ; inserted e28
    ; rewrite 1 added
    ; rewrite 2 added
    ; ran 9 rounds, 262143 unions: 2046 classes, 58035 e-nodes
    ; match 685.163722ms, apply 1.287551403s, rebuild 150.952363ms

Superposition provers like e-prover and zipperposition have received special smarts for this lambda free higher order fragment <https://inria.hal.science/hal-03485227/document>. It's a useful but simple thing.

# Miller Patterns

But in addition to this, it is really nice to support actual binders.

The variation of higher order patterns supported is Miller patterns.

A Miller pattern `{?a x y}` is basically a bound variable allowance pattern.

Another way of saying it it Miller patterns are higher order patterns where the metavariable must be applied to distinct bound variables, not arbitrary terms.

The pattern `?a` is allowed to contain the bound variables `x` and `y`, but not `z` (if there happens to be a bound `z` in the pattern).

It _is_ allowed to contain any free variables in scope at the top of the pattern, which is kind of interesting.

Miller patterns are basically the minimal way of making sense of patterns in a scoped syntax. There is some extra stuff you can do, but by and large it is decidable oasis in higher order matching / unification problems.

Some more description of the concept:

- <https://www.philipzucker.com/ho_unify/>
- <https://www.lix.polytechnique.fr/Labo/Dale.Miller/lProlog/proghol/extract.html> Chapter 4
- <https://en.wikipedia.org/wiki/Unification_(computer_science)#Higher-order_unification>
- <https://www.lix.polytechnique.fr/Labo/Dale.Miller/papers/jlc91.pdf> Is this the original reference on Miller patterns?

If you want to model beta substitution on an object `@lam` term, this is actually the following rule:

```python
%%file /tmp/beta.sexp

(insert [(@lam x x) 42])
(rewrite  [(@lam x {?body x}) ?e] {?body ?e}) ; beta substitution. Matches app(lam,e) basically.
(run 10)
(extract [(@lam x x) 42])
```

    Overwriting /tmp/beta.sexp

```python
! lambda-microegg /tmp/beta.sexp
```

    ; inserted e3
    ; rewrite 1 added
    ; ran 1 rounds, 1 unions: 3 classes, 4 e-nodes
    ; match 6.092µs, apply 4.989µs, rebuild 5.892µs
    42

What I think the thing I've actually added is the ability of pattern variables to have more context lying around than the base context.

This first example returns a substitution in a context of size 1. `?b` is the free variable in that context

```python
%%file /tmp/ctx.sexp

(insert (@lam x (@lam y (+ 3 y))))
(match (+ ?a ?b))
```

    Overwriting /tmp/ctx.sexp

```python
! lambda-microegg /tmp/ctx.sexp
```

    ; inserted e4
    ; match 1: ctx1 |-> {?a = 3, ?b = $0}

However in this very similar example, the context the substitution is in is context 0 (the empty context). `?b` refers to an extra bound variable. This is kind of, sort of a lambda, but it's a meta lambda.

```python
%%file /tmp/ctx2.sexp

(insert (@lam x (@lam y (+ 3 y))))
(match (@lam y (+ ?a {?b y})))
```

    Overwriting /tmp/ctx2.sexp

```python
! lambda-microegg /tmp/ctx2.sexp
```

    ; inserted e4
    ; match 1: {?a = 3, ?b = ctx1 |-> $0}

Also check it out. Alpha equivalent terms hash cons to the same thing. The `l_10` annotations are the lifting annotations, which are held in a byte stolen from the u32 Id.

```python
%%file /tmp/alpha.egg
(insert (@lam x (@lam y (+ x y))))
(insert (@lam a (@lam b (+ a b))))
(print-egraph)
```

    Writing /tmp/alpha.egg

```python
! lambda-microegg /tmp/alpha.egg
```

    ; inserted e3
    ; inserted e3
    ; egraph: 4 classes, 4 e-nodes
    ; e0 = ctx1 |-> $0
    ;   e0 <- var
    ; e1 = ctx2 |-> (+ $0 $1)
    ;   e1 <- (+ l_10(e0) l_01(e0))
    ; e2 = ctx1 |-> (@lam x0 (+ $0 x0))
    ;   e2 <- (@lam e1)
    ; e3 = ctx0 |-> (@lam x0 (@lam x1 (+ x0 x1)))
    ;   e3 <- (@lam e2)

Kind of more interesting (in it's unusualness) is there is memory sharing between terms that are _not_ alpha equivalent but are heavily thinning related. All of the the deeper terms in these `(@lam z (@lam w (@lam v x)))` and `(@lam z (@lam w (@lam v y)))`  actually hash cons to the same form, whereas a naive de bruijn index approach would not (they'd be `(lam (lam (lam var4))))` and `(lam (lam (lam var3))))`). Kind of you only pay hash cons memory for variables actually in use, not for the ones in scope.

```python
%%file /tmp/thin.sexp
(insert (@lam x (@lam y (@lam z (@lam w (@lam v x))))))
(insert (@lam x (@lam y (@lam z (@lam w (@lam v y))))))
(print-egraph)
```

    Writing /tmp/thin.sexp

```python
! lambda-microegg /tmp/thin.sexp
```

    ; inserted e5
    ; inserted e7
    ; egraph: 8 classes, 8 e-nodes
    ; e0 = ctx1 |-> $0
    ;   e0 <- var
    ; e1 = ctx1 |-> (@lam x0 $0)
    ;   e1 <- (@lam l_10(e0))
    ; e2 = ctx1 |-> (@lam x0 (@lam x1 $0))
    ;   e2 <- (@lam l_10(e1))
    ; e3 = ctx1 |-> (@lam x0 (@lam x1 (@lam x2 $0)))
    ;   e3 <- (@lam l_10(e2))
    ; e4 = ctx1 |-> (@lam x0 (@lam x1 (@lam x2 (@lam x3 $0))))
    ;   e4 <- (@lam l_10(e3))
    ; e5 = ctx0 |-> (@lam x0 (@lam x1 (@lam x2 (@lam x3 (@lam x4 x0)))))
    ;   e5 <- (@lam e4)
    ; e6 = ctx0 |-> (@lam x0 (@lam x1 (@lam x2 (@lam x3 x0))))
    ;   e6 <- (@lam e3)
    ; e7 = ctx0 |-> (@lam x0 (@lam x1 (@lam x2 (@lam x3 (@lam x4 x1)))))
    ;   e7 <- (@lam l_0(e6))

A curious nuance is that I can only support "ordered Miller patterns". This only really exposes itself in nonlinear patterns, where the variable is used twice. I could support this by allowing term creation in patterns or extending thinnings to also support exchange, which would bring us closer to, but subtly I think not quite the same as slotted, since scoping would be dealt with differently and variables are ordered. This means I wouldn't have to implement the group symmetry breaking stuff I think?

```python
%%file /tmp/nogood.sexp

(rewrite (@lam x (@lam y (pair {?a x y} {?a y x}))) wontwork)
```

    Overwriting /tmp/nogood.sexp

```python
! lambda-microegg /tmp/nogood.sexp
```

    /tmp/nogood.sexp:2:41: error: Miller metavariable '?a' arguments are out of order; write {?a x y} on the match left-hand side, then permute its arguments on the rewrite right-hand side if needed

# Bits and Bobbles

I could support fancier patterns if we just pull the band aid off term creation in patterns. Once a pattern var is grounded, we can use it to ground it's other uses, which may have more complex beta subsitution in them.

Maybe using different braces for the different concepts is goofy. It might be better to just remove FOApp even if there is a perf hit.

I was a bit surprised that the map comp fusion example can explode. Maybe egraphs suck.

I would probably like to support more than 7 variables while not paying much when I'm not using them. I'm currently leaning towards the "ephemeral enode" idea. I'd also like to play with injecting buchberger, multiset, string and semiring completion into the thing.

I'd like to do proofs next. I wanna try a proof log version which I traverse to spit out a proof term. Lean conventions.

Flatten patterns, dynamically go up or down or sideways depending?

If egglog was kind of designed for GATs is this good for SOGATs?

What is it all for?

relational calculus
integration rules
program interpreters
type checkers
fixpoint reasoning
forall exists reasoning. calc mode. proving redudnant rules.

Yes all alpha equivalent terms hash cons to the same memory

Kind of. The free variables have an implicit order to them
Alpha equal Closed terms and terms that use free variables in the same ordered way hash cons as equal
$0 + $1 and $1 + $0 do not hash cons the same
But $0 + $2 and $0 + $1 do hash cons to the same interned memory (edited)
$n being free variable n
$0 + $2 and $0 +$1 are observably distinct despite using the same interned memory because of thinning annotations on the identifier ( I stole   byte off a u32 Id)
So there is a maximum of 7 free vars allowed in the current implementation
I was trying to be close to zero cost for first order stuff (edited)

Bound variables also have an order to them. The free and bound variables are all the same stuff. But the order is defined by the binder order like in de bruijn indices or levels, so alpha renaming at  both the binder site and at the use sites really does nothing (edited)
If one alpha renames free variables you’re kind of not renaming their implicit binding site in a corresponding way?
The set-like character of unordered contexts is infecting stuff
[x, y] |- x + y is the same as [a,b] |- a + b but not the same as [b,a] |- a + b
Names are cursed
And alpha renaming is also cursed
It's a pretty bad non-semantic concept

I dunno man.

shift rules in summation identities seems interesting

Should I go binary App?

Allow term creation in left hand sides like Max said?

There is a temptation to do always more pattern preprecssing.

I haven't massively micro-optimized it, but I did take the easy wins / avoid some dumb unnecessary allocations. On meaningless microbenchmarks I'm maybe in the ballpark of 3x egg. Let's say that anything under 10x is fine.

There is a builtin capture avoiding substitution routine that can be used in right hand sides. It kind of recursively copies the egraph or in another sense is equivalent to extracting many terms, substituting and reinserting. The Lifting technique at every point strengthens a term to it's minimal required context. Because of this, we always know exactly what variables will be found expanding out from any eclass. This is kind of a generalization of a boolean ground flag which allows you to terminate beta substitution early.

I currently steal 1 byte off of the `u32` Id for thinnings to make my "Fat Id". The Id is actually not any fatter. AI made a nice encoding trick where a sentinal 1 marks where the thinning bitvector starts (in other words [false, true, true] = 0b00001011). This means we can support 7 variables in context. I'm on the fence about how best to support arbitrary width thinnings. I may make thinnings an entire extra u32, making fat ids 64 bits. Or perhaps I should go down the "ephemeral enode" angle and make it such that if your thinnig is larger than 7, I have a separate arena where I store very fat ids.

I think I'm kind of back in my sort-less era. There is something freeing about avoiding types. Prolog doesn't do it, egglog0 didn't. Why should I have to write all these declarations and extra junk?

I did heavily use AI. I've been pretty depressed and stressed the last couple weeks and year about what AI means for everything I've ever valued or invested in myself. I've been slowly swearing myself off more social media, forums, and news sites because it is just causing me net psychosis.

On the plus side (?) it was quite fun to just finally see some things actually happen. I have more ideas than I have programming skill.

On the negative side, even after reviewing the whole code multiple times, it still seems kind of "loose". I have not bothered trying to check the details of it's index manipulation math. I think it is probably right based on testing. AI does seem better at that sort of local stuff than I am.

I think I was basically not on track to be writing this myself. The amount of work just adds up and I'm ok at rust but never been very facile. I tend to not write frontends because I find writing a parser so uninteresting and painful. Hammering out some ideas about how to represent meaningful patterns with binders I think is actually the newest most interesting bits to me.

%%file /tmp/integ.sexp

(rewrite (@int x 1) $0)

I think it would be nonsensical for the left and right and side of a rewrite to be at different contexts. In order to insert a `?a` into the right hand side, we need to know how we are going to fill in the extra holes we've abstracted in it. We can use anything in scope to do so. Even if I fill in in the right hand side `(lam x (lam y (?a x y )))` again, that kind of isn't really a no-op in some respects because the bound variables on the lhs and rhs kind of are but kind of aren't the same things. Implementation-wise, it is a no-op though.

I did not mention much in my talk how to deal with binders. What I feel was kind of an interesting lesson is that binders are not the essential point and there is much to be clairified before you even start talking about binders. The essential point was contexts are a part of what terms are (or are required to make any semantic sense of a term with variables in it `[[ctx |- t]]`). Then the smarts that are useful to build in are manipulations of contexts like weakening and exchange. Liftings/Thinnings are one way of doing this.

I originally was exposing all the guts at the syntax level, but I was getting pretty confused too. Names are nice.
But nevertheless, people (and me) want things that look familiar so hewing close to orevious lambda matching designs I've seen like lambda prolog makes sense. Even I do not really want to write patterns referring to liftings

The confusing thing about binders is that they make multiple contexts at play inside a pattern. Some positions in the pattern are at different variables contexts than other parts and you need to specify how you want stuff to move between these different contexts. There is a sense that a priori `v7` in context A may not be the same as `v7` in context B since maybe you shift,insert,drop, and swap around variables while you're traversing the term from A to B.

A pattern is attempted to match against a term in context `n |-> e42` . The top of the pattern is in that context `n`, but inside the pattern more variables may be at play.

In the pattern `(map (lam x ?b) ?l)` matching against `7 |-> e4`, the top of the pattern is in context 7, `?l` is also at context 7, but `?b` is at context 8.

If we want a substitution that we carry over to a right hand side, `lhs -> rhs`, the subsitution should be in the top context of the pattern. `[?l = n |-> e14, ?b = n+1 |-> e18]`  Or is it better to think of it as `n |-> [?l = +0 |-> e14, ?b = +1 |-> e18]`.

I don't know that I want to think of `?b` as a lambda really. I think it's more just a term in context, but the context is noted to be split at a certain position.

`[[n |-> ]]`

The lifting perspective actually allows richer ways of bringing in new variables into the context rather than insisting they go into the front or the back of the current variables, but I don't know of an example where exposing this would be useful.

We could have explicit thinning patterns. We could also have variable disallowance annotations or variable allowance annotations.

A Miller pattern `(?a x y)` is basically a variable allowance pattern. We allow all free variables in and in fact we probably should never refer to free variables inside a rule. Doing so is kind of fishy scope-wise even if it is currently wired in.

I'll note that some kind of similar stuff shows up in metamath and metamath-zero. I suppose also in nominal  `#` constraints.

There is an unusual restriction I ended up adding to miller patterns in that variables need to be applied to in the pattern in the same order they were bound. `(lam x (lam y (?a x y)))` is ok but `(lam x (lam y (?a y x)))` is not. In terms of the implementation, this restriction reduced complexity by a nice amount, and you haven't really lost much because you can just flip the arguments as you use them in the right hand side of a rewrite.

One place this restrction may genuinly be a loss of power is in nonlinear patterns like `(foo (lam x (lam y (?a x y))) (lam x (lam y (?a y x))))`. One method to solve this would be to enable term creation in the pattern as Max has been suggesting. Maybe that's the right way to go
