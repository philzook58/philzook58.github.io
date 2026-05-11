---
title: Family Orienting Python Frozenset Dependent Type Theory
date: 2026-05-10
---
 
 I like trying to finitize things and put them in mundane trappings.

 In a previous post <https://www.philipzucker.com/frozenset_dtt/> , I tried to write python code on frozensets that in some way demonstrates the set semantics of dependent types. This post implements a slight but important change I wanted to do based on my new appreciation of the centrality of the concept of "family", a set valued function <https://en.wikipedia.org/wiki/Family_of_sets> . _Everything_ should be a family (a dict with set values). The counterintuitive part is that seemingly pointless `()` keys clean things up.

# Judgements Interpret as Mappings

Something that hit home recently is that in type theory, the thing you want to give semantics/meaning to is the full judgement `[[Gamma |- Yada]]`, not just the thing on the right hand side `[[Yada]]`.  The full judgement is basically some kind of mapping / function, which is easier to see if you write it as `[[Gamma |-> Yada]]` and forget about the turnstile `|-` which is connotationally loaded in a different way.

This was somehow very counterintuitive to me previously and highly intuitive to me now. I think part of the issue may come from a difference of infrastructure between how you think about models of first order-ish logic and that of type theory.

In first order logic, you don't really talk about translating judgements like `a, a -> b |- b` into an object of the model. I might think about how `[[x+4]]` has the value `43` in a particular model `{"x" : 39}`, and I might think about how the formula `[[x > 4]]` might be true or false in a model, but I have no impulse to assign a model specific truth value or object to `[[x > 7 |- x > 3]]`. Sure, this is some relative of the formula `[[x > 7 -> x > 3]]` which I would expect to be true in all models, but that is not the same thing. Doing this just isn't part of the typical definition of a first order model. <https://plato.stanford.edu/entries/modeltheory-fo/>  "Non typical" is not argument against something being done.

If we give the full judgements like `[[ x : Int |->  Bool ]]` meaning, actually giving a meaning to a "bare type" like `[[Bool]]` is not necessary, it's fluff. And it shouldn't be the starting point of a demonstration of semantics. If it does mean anything, it should mean exactly the same as a judgement with an empty context `[[ [] |- Bool ]]`.

In my previous blog post on dependent type theory as frozensets, I think this was the mistake at the outset to even consider `Bool = {True, False}`. I suspect a cleaner thing and more important thing is the 0-arity lifted version `Bool = {() : {True, False}}` as silly and redundant that looks. That's the thing though. Sometimes nonintuitive moves pay big dividends. We call those discoveries.

What this corresponds to is a choice is to only work with 0-arity stuff rather than have a separate notion of "bare value"

More mundanely, you can see that these 3 things are all kind of the same thing:

```python
e1 = 42
e2 = lambda: 42
e3 = {() : 42}
```

They aren't perfectly interchangeable, sometimes you need to add extra `lambda`, `f()`, and `f[()]` to expressions. But they are getting at the same stuff in some sense.

But if we are going to be making a bunch of combinators to manipulate n-ary functions, we can use those same combinators on `e2` but not on `e1`. Our combinators will need less special cases and work uniformly

For finite domains, dictionaries and functions are to some degree (ignoring computational and memory efficiency considerations) "the same thing".

So our judgements will be semantic objects made out of python dictionaries and sets and stuff. The horizontal inference lines will be represented basically by python functions that take in the stuff above the line and give back the judgement below the line.

```
foo judge1   bar judge2
----------------------- myrule
     biz judge3         
```

becomes

```python
def myrule(foo : Judge1, bar : Judge2) -> Judge3: ...
```

This is kind of an "LCF" style of correspondence between inference rules and something programmy. There are other possible modes such as giving stuff below the line and returning the top, giving all the pieces and giving a yes/no (this process being guaranteed to finish I think is what decidable typechecking is).

# Telescopes are Tries

Ok so we're going to try to build naive frozenset combinators that have the flavor of dependent type theory judgements. Many of them will corresponds to some inference rule of dependent type theory and dignify them in that way.

In another blog post <https://www.philipzucker.com/telescope_tries/> I state that telescopes (the dependent notion of contexts) are tries. Tries are a useful way of keying on sequences. I think this is still an interesting and perhaps useful point, but it is a bit simpler to just use dicts on tuples as my notion of `Yada` in context rather than actually implement tries.

```python
type Env = tuple[object,...]
type Ctx = frozenset[Env] # a set of environments
type InCtx[T] = dict[Env, T]  # a family of stuff indexed by environments

def is_ctx(ctx : Ctx) -> bool:
    assert isinstance(ctx, frozenset)
    assert len(ctx) >= 1
    return isinstance(ctx, frozenset) and all(isinstance(env, tuple) for env in ctx) # same length also

# empty context
emp : Ctx = {()} # [] |-

```

# Weakening / Thinning

Sometimes we want to take something and add some irrelevant garbage into the key. This is weakening / thinning / lifting, the kick I've been on recently. <https://www.philipzucker.com/dump_calculus/> <https://www.philipzucker.com/thin1/>

There are some useful simple weakenings that just dump stuff on the left or right of the tuple in a cartesian product kind of way

```python
def lweak[T](ctx : Ctx, x : InCtx[T]) -> InCtx[T]:
    """
    G |- yada     ctx |-
    --------------------- leftweak
    ctx, G |- yada 
    """
    return {env + env0  : v for env0,v in x.items() for env in ctx}

def rweak[T](ctx : Ctx, x : InCtx[T]) -> InCtx[T]:
    """
    G |- yada     ctx |-
    --------------------- rightweak
    G, ctx |- yada 
    """
    return {env0 + env  : v for env0,v in x.items() for env in ctx}

def proj_ctx[T](x : InCtx[T]) -> Ctx:
    """
       G |- yada
    ------------ proj
       G |-

    Not usually a rule. But ought to be admissible.
    """
    return frozenset(x.keys())

```

But there is also a more general thinning that let's you intersperse the junk throughout the tuple. You need arguments that described how you want this to happen in the form of a bitvector.

```python
# more general thinning


type Thin = list[bool] # Thinnings describe how to extract a subsequence from another. True means takse, False means don't take
def thin(t : list[bool], env : Env) -> Env:
    assert len(t) == len(env)
    return tuple(e for e, b in zip(env, t) if not b)

"""
  G |- yada      G <=t D
  ----------------------- weak
            D |- yada
"""

def weak[T](newctx : Ctx, t : list[bool], x : InCtx[T]) -> InCtx[T]:
    return { x[thin(t, env)] for env in newctx}
```

# Families as Set Valued Dictionaries

A raw `Type` is no longer a thing I want to concentrate on. Instead, let's say that _all_ types are actually families, an indexed set, aka a function/dict whose output is sets. Some simple families like `Bool` are 0-arity.

```python
type PreType = frozenset[object] # I will often be too lazy to wrap set in frozenset. frozenset looks like shit too.
# There is no "Type" really. only Family. Family is Type
type Family = dict[Env, PreType]

"""
------------------- BoolType
   [] |- Bool Type
"""
Bool : Family = {() : {True, False}}
Unit : Family = {() : {()}}
Void : Family = {() : {}}
RGB : Family = {() : {"R", "G", "B"}}
def Fin(n : int) -> Family:
    # This is meta parametrized (python function), since I can't make a dictionary of all integers
    return {() : frozenset(range(n))}

"""
A family with a nontrivial context
x : Bool |- (if x then Bool else Unit) Type
"""
ifUnitBool : Family = {(False,) : {()}, (True,) : {True, False}}


```

We can make an "admissible rule" of a combinator take takes any context and weakens Bool to that context. Admissible means that we could just use our previous combinators to define the rule.

```python

"""
   G |-
---------
  G |- Bool Type

Is an admissible rule
"""
def Bool1(ctx : Ctx) -> Family:
    return rweak(ctx, Bool)
```

Given that we have a type in context, we can produce a larger context with that type.

```python
"""
    G |- A Type
------------------- extend_ctx
   G, x : A |- 
"""
def extend_ctx(A : Family) -> Ctx:
    return frozenset({env + (x,)  for env, As in A.items() for x in As})

ctxBool : Ctx = extend_ctx(Bool)  # x : Bool |-

assert is_ctx(ctxBool)
ctxBool
```

    frozenset({(False,), (True,)})

Here are some example manipulations to build a concrete larger context

```python
Bool_Unit : Family = rweak(ctxBool, Unit)   # x : Bool |- Unit Type
ctxBoolUnit : Ctx = extend_ctx(Bool_Unit)   # x : Bool, y : Unit |-
ctxBoolUnit
```

    frozenset({(False, ()), (True, ())})

# Terms

Of course we also want a notion of a term/value in context. These correspond to functions to stuff. I could perhaps insist that sections always say what set they are in the bring it closer to how the `G |- t : A` feels. What we have here is really more like `G |- t` without the `A`.

```python
type Section = InCtx[object] # Section is "term". Basically sections are functions.

# empty context / 0-arity "functions" are constants / values
tt : Section = {() : ()}
true : Section = {() : True}
false : Section = {() : False}

"""

G |- t : A       G |- e : A    G |- c : Bool
--------------------------------------------
   G |- if c then t else e : A

"""

def ite(c : Section, t : Section, e : Section) -> Section:
    assert proj_ctx(t) == proj_ctx(e) == proj_ctx(c)
    return {env : t[env] if c[env] else e[env] for env in proj_ctx(t)}

"""
     G |- A type
-------------------
  G, x : A |- x : A
"""

def id(A : Family) -> Section:
   # schema for identity function. Not a Pi internalized one.
   return {env + (x,) : x for env, As in A.items() for x in As}

```

# Combining Types

We can make pairs of types

```python
def Pair(A : Family, B : Family) -> Family:
    assert proj_ctx(A) == proj_ctx(B)
    return { ctx : { (a,b)  for a in A for b in B[ctx]} for ctx,A in A.items()}

Pair(Bool, Bool)

"""
        G |- Pair A B 
  ---------------------
     G, x : Pair A B |- fst(a) 

"""

def pair(a : Section, b : Section) -> Section:
    assert proj_ctx(a) == proj_ctx(b)
    return {env : (a[env], b[env]) for env in proj_ctx(a)}
def fst(AB : Family) -> Section:
    return {env + ((a,b),) : a for env, ABs in AB.items() for (a,b) in ABs}
def snd(AB : Family) -> Section:
    return {env + ((a,b),) : b for env, ABs in AB.items() for (a,b) in ABs}

snd(Pair(Unit, Bool))
```

    {(((), False),): False, (((), True),): True}

`Sigma` and `Pi` are a little more interesting than before. but familiar.

```python
def Sigma(A : Family, B : Family) -> Family:
    return {ctx : { (a, b) for a in As for b in B[ctx + (a,)]}  for ctx, As in A.items()}
Sigma(Bool, ifUnitBool)
```

    {(): {(False, ()), (True, False), (True, True)}}

`Pi` is basically currying part of the key into the value.

```python
import itertools
from frozendict import frozendict
def Pi(A : Family, B : Family) -> Family:
    assert proj_ctx(A) == {ctx[1:] for ctx in proj_ctx(B)}
    A = {k : list(v) for k,v in A.items()}
    return { ctx : {frozendict({a : b for a,b in zip(As, bvs)}) for bvs in itertools.product(*[B[ctx + (a,)] for a in As])}  for ctx, As in A.items() }
Pi(Bool, ifUnitBool)
```

    {(): {frozendict.frozendict({False: (), True: False}),
      frozendict.frozendict({False: (), True: True})}}

There are combinators for constructing functions and applying them. This uses `itertools.groupby` to collect up contexts with a common prefix. This is kind of "currying" a dictionary, making it look more trie like.

```python
"""
 G, x : A |- t : B
 ----------------------
   G |- lam x, t : Pi A B

"""

def lam(body : Family) -> Section:
    return {subenv :  { env[-1] : body[env] for env in envs} for subenv, envs in itertools.groupby(sorted(body.keys()), key=lambda e: e[:-1])}

lam(id(Bool)) # |- lam x : Bool, x 
lam(ite(id(Bool), lweak(ctxBool, false), lweak(ctxBool, true))) # |- lam x : Bool, if x then false else true
```

    {(): {False: True, True: False}}

```python
"""
G |- f      G |- arg 
-------------------------------
    G |- apply f arg
"""

def apply(f : Section, arg : Section) -> Section:
    assert proj_ctx(f) == proj_ctx(arg)
    return {env : f[env][arg[env]] for env in proj_ctx(f)}

assert apply(lam(id(Bool)), true) == true
assert apply(lam(ite(id(Bool), lweak(ctxBool, false), lweak(ctxBool, true))), false) == true 

```

The Identity type

```python
def Id(A : Family) -> Family:
    return { ctx + (x,y) : {"refl"} if x == y else {} for ctx, As in A.items() for x in As for y in As}
Id(Bool)
# Pi(leftweak(_, Bool), Id(Bool))
```

    {(False, False): {'refl'},
     (False, True): {},
     (True, False): {},
     (True, True): {'refl'}}

```python
Id(Unit)
```

    {((), ()): {'refl'}}

# Bits and Bobbles

I thought this post was going to be about some more interesting models I've been thinking about that aren't just into finitesets

Type in context =

- set and subset
- set and frozenset euiqvalence relations
- set + taint tracking
- set of values and the time they arrive at. Only causal functions allowed. Cutoff time at N to finitize.
- Relational models. Type tags are secrets. Parametricity = noninterfereces / non secrete leakage. "Which dicts have 'the parametricity' in them?"

- Casting. Isomorphic types. Groupoids of casting `Cons <-> Snoc`. isomorphic Views.
- In knuckledragger it doe seem coherent to try and convert a proof to work over a different sort. If the nature of the proof did not rely on the details but only the abstract interface, this ought to be possible. Parametrcicty sort of stuff helps guarantee this transport will work ahead of time.
- Tarski style universes using quote, eval, and python strings as codes. t-strings

Dealing with universes of polymorphism is tough because it's hard to have a finite number of types. I could make some universe cutoff like I did before. Is the different between things that can go in the family and otherwise the different between parameters and indices?

In the taint model is it important that the taint values kind of represent the context? It can't be some fixed single taint. It's glued in aliens? A free lattice of taint.

An interesting feature of defining lifting / thinning on keys of a dict is you need to supply the data of how to do so. This is unlike the functional combinators where I can delay the thinning inside a closure until they are used.

Named thinnings for records. The evidence of a subrecord relationship is a named thinning.

This is perhaps related to another confusion of mine, which is "what is a propositional / first-order / higher-order logic". I thought a higher order logic was a logic that supports the syntactic feature of lambda terms, but I now think this is true. What Is closer to true I think is that whether some syntax is such-and-such kind of logic actually depends on your _choice of definition_ of what it even _means_ for some other thing to be a model of the syntax. If you pin the connectives like and,or,implies to the standard meanings, you get a propositional logic. If you pin the meanings of forall / exists you get a first order logic and if you pin the meaning of application and abstraction to function application you get a higher order logic. If you pin `=` to the "normal meaning" of equality, you'll get equational logic. If you don't pin this meaning, non standard models will show up. This definition of semantics is going to be conceptually intertwined with what you think the axioms or inference rules of the logic should be.

I've been playing with functional combinators for weakening for the purposes of have a story for alpha invariance in e-graphs.

In fact, we are perhaps better off just not giving the thing on the right hand side any meaning. A very related thing that does have meaning is `[[[] |- Yada]]` , were you place `Yada` in an empty context `[]`. If `[[Yada]]` has any meaning it just this.

I like trying to finitize things.

At the outset, many type theories bring in the full integers. You're already kind of screwed at this point.

If you only have finite enums like bools and -> and tuples, you're a bit better off. If you also want to start talking about polymorphism, you are again kind of screwed, because -> and tuple let you have an infinite number of interesting types. Perhaps this can be finitized by indexing your universes.

Context maps are the meaning of substitutions?

Trie compression (like bdd) might give you auto weakening to strongest context.

<https://carloangiuli.com/papers/type-theory-book.pdf>

Bidirectional type checking might obviate the need for some explicit weakening. Doing explicit weakenings yourself is somewhat painful.

intensional vs extensional <https://types.pl/@sandmouth/116291094930841679> Two AVL tree based sets or dicts can extensionally hold the same elements, but structurally are different because of different insertion orderings. Is this an accurate analogy for intensional vs extensional equality in type theory?

<https://types.pl/@bentnib/114587130921412422> "Another way to look at it is as if a setoid was a category (equalities are morphisms, reflexivity is identity, transitivity if composition), families are then functors from setoid-as-category into the category of all setoids."

This is a strange looking combinator to my eye. It is often possible to undo certain operations to get out their parts. I don't think I usually see a rule like this.

```python
"""
  G, x : A |- 
 --------------
  G |- A type
"""
def proj_family(F : Ctx) -> Family:
    return {subctx : {ctx[-1] for ctx in ctxs}  for subctx, ctxs in itertools.groupby(sorted(F), lambda ctx: ctx[:-1])}
proj_family()


```python
42
{() : 42}

def dictthunk(v):
    return {() : v}
dictthunk(42)
```

```python
def Arr(A : Family, B : Family) -> Family:
    assert proj_ctx(A) == proj_ctx(B)
    return {ctx : {    }  for ctx,A in A.items()}
```

Context maps as substitutions. Is this the right thing? Are substitutions a restriction of all possible context maps?

```python
type CtxMap = dict[Env, Env]

def comp(f : CtxMap, g : CtxMap) -> CtxMap:
    return {env1 : f[env2] for env1, env2 in g.items()}
def idmap(ctx : Ctx) -> CtxMap:
    return {env : env for env in ctx}
def inctx_map(x : InCtx[object], t : CtxMap) -> InCtx[object]:
    return {env1 : x[env2] for env1, env2 in t.items()}

```

```python
import itertools
def Pi(T : Family) -> Family:
    return {subenv : {itertools.product(* )e for e,v in f} for subenv, f in itertools.groupby(
        sorted(T.items()),
        key=lambda kv: kv[0][:-1],
    )}
Pi(UnitBool)

    # assert A == { {c[-1] for c in fullctx}  for ctx, fullctx itertools.groupby(proj_ctx(B), key=lambda ctx: ctx[:-1])}

```

      Cell In[20], line 3
        return {subenv : {itertools.product(* )e for e,v in f} for subenv, f in itertools.groupby(
                                              ^
    SyntaxError: Invalid star expression

```python

"""
 Gamma  |-
 ------------------
 Gamma |- Bool Type
"""



def Bool(ctx : Ctx):
    assert is_ctx(ctx)
    return {env : frozenset([True, False]) for env in ctx}
def Unit(ctx : Ctx):
    assert is_ctx(ctx)
    return {env : frozenset([()]) for env in ctx}
Bool = {() : frozenset([True, False])}
Unit = {() : frozenset([()])}
def wrap0(T0 : PreType) -> Family:
    return {() : T0}




type Section = dict[Env, object]

def true(ctx : Ctx) -> Section:
    assert is_ctx(ctx)
    return {env : True for env in ctx}

true1 = {() : True}
false1 = {() : False}

def false(ctx : Ctx) -> Section:
    assert is_ctx(ctx)
    return {env : False for env in ctx}

def tt(ctx : Ctx) -> Section:
    assert is_ctx(ctx)
    return {env : () for env in ctx}


# Do we keep t and T coupled or no?
# Perhaps this is a church vs curry kind of thing.
# G |- t : T
true1 = {() : (True, {True, False})}


import itertools
# non dependent product
def Tuple(T1 : Family, T2 : Family) -> Family:
    assert proj_ctx(T1) == proj_ctx(T2)
    return {env : {frozenset(itertools.product(s1, T2[env]))} for env, s1 in T1.items()}
"""
It is however somewhat annoying to manually reconcile the contexts


"""
#def Arr()
"""
G, x : A |- B
------------
G |- Pi x : A. B
"""

def Pi(T : Family) -> Family:
    # no, it should be a frozenset of dicts
    return {subenv : {e[-1] : v for e,v in f} for subenv, f in itertools.groupby(
        T.items(),
        key=lambda kv: kv[0][:-1],
    )}
def Sigma(T : Family) -> Family:
    # Can you infer family 1 or no?
    return {subenv : frozenset([ (e[-1], v) for e,v in f ]) for subenv, f in itertools.groupby(
        T.items(),
        key=lambda kv: kv[0][:-1],
    )}

def Sigma2(T : Family, T2 :Family) -> Family:
    # not inferred version instead checks that is compatible
    # common context -> (set i, {i -> set j}) -> const -> (i, j)
    assert proj_ctx(T) == { env[:-1] for env in proj_ctx(T2)}
    # todo


```

Native frozendict is coming in python 3.15 btw.

```python

def thunk(v):
    return lambda: v
def dethunk(t):
    return t()
e3 = thunk(e1) # another way of writing e2
```

```python

```

```python
type Type = frozenset[tuple[object, frozenset[int]]]
# basically all taints are possible? as long as there is a pathway from the input type to final type
type Type = frozenset[tuple[int, object]] # type in context?
type CtxType = frozenset[tuple[int, frozenset[int], object]] # type in context with taint
# [[Gamma |- T]] = CtxType
type IsType = ...
type HasType = ...
type Family = HasType # [G |- A type] means A is a family of sets indexed by iterated domain G
type Family = dict[object, Family] | frozenset[object]  # trie of families. But should be equal length across all branches
type Ctx = tuple[object, ...]
type Family = dict[Ctx, frozenset[object]]
type Family = frozenset[tuple[Ctx, frozenset[object]]] # dicts are just functional sets of tuples

# you kind of want to know where the int cutoff is. Either as a Type() wrapper. Or perhaps as a just carried int

type Ctx = dict[object, Ctx] | None
type Family = tuple[Ctx, int] # how deep to put the turnsilte. Where to consider G vs A. G |- A. yes, Ctx and Family are very similar.

type Type = tuple[Ctx, typing.Literal[0]] # Type in empty context.
# kind of Type is what you might get from indexing Family.
type Type = Ctx # The remainder.

type Thinning = dict[object, Thinning] | None | tuple[None, Thinning] # How to interpolate into a new context.

def is_thin(bigctx : Ctx, littlectx : Ctx, thin : list[bool]) -> bool: ...
def subctx(bigctx : Ctx, littlectx : Ctx) -> list[bool] | None:
    # recurse through bihctx and littlectx.
    # see if returned thinnings match
    # see if current key space also matches?
    ...

type ctxobject0 = dict[object, ctxobject0] | object # since dict is object, not strictly speaking useful, but gets at something
type ctxobject = tuple[int, ctxobject0]
#type Ctx = tuple[int, ctxobject] # a projection off of an object in context. Kind of done lazily. No make it None at end

# a functor over contexts?
def ctxobjectmap(ctx : ctxobject, f):
    def worker(m, data):
        if m == 0:
            return f(data)
        else:
            return {k : worker(m-1, v) for k, v in data.items()}
    return worker(ctx[0], ctx[1])




def Thin(): ...
def Weak(): ...
    # weakening just in the front is easier

Bool0 = (0, {True: None, False: None})
Unit0 = 

def Bool(ctx : Ctx) -> Family:
    ctx.map(lambda x : {})


def Pi(B : Family) -> Family:
    nctx, data = B
    assert nctx > 0
    return (nctx-1, data)
    # group by context.
    #return {(ctx[1:],   for ctx, B in f}
#{True : }


from itertools import chain, combinations

def powerset(iterable):
    s = list(iterable)
    return chain.from_iterable(combinations(s, r) for r in range(len(s)+1))

def Void(ctx : int) -> Type:
    return frozenset()

def Unit(ctx : int) -> Type:
    return frozenset({((), ) for taint in powerset(range(ctx))})
# in empty context, Unit(0) ~ {()}

type Ctx = int

# the taint and the set are basically uncoupled.
# Except once you start talking about about functions
# twisted product? 
def proj(T : Type) -> Ctx:
    ...


def Arr(ctx : Ctx, T1 : Type, T2 : Type) -> Type: ...







```

```python
type Term = str
Bool0 : frozenset[Term] = {"True", "False"}
Unit0 : frozenset[Term] = {"()"}
Type0 = {"Bool", "Unit"}

type Code = str
def El(c : Code):
    assert c in Type
    return eval(c)

@dataclass(frozen=True)
class Code():
    code : str
    def __add__(self, other):
        if not isinstance(other, Code):
            other = quote(other)
        return Code(self.code + " + " + other.code)
    def __radd__(self, other):
        if not isinstance(other, Code):
            other = quote(other)
        return Code(other.code + " + " + self.code)
    def __mul__(self, other):
        if not isinstance(other, Code):
            other = quote(other)
        return Code(self.code + " * " + other.code)
    def __call__(self, *args):
        args = [arg if isinstance(arg, Code) else quote(arg) for arg in args]
        return Code(self.code + "(" + ", ".join(arg.code for arg in args) + ")")

def quote(x): # is quote really the right word? Reify?
    return Code(repr(x))


def quote_lam(f, n):
    names = [f"x{i}" for i in range(n)]
    body = f(*[Code(name) for name in names])
    return Code("lambda " + ", ".join(names) + ": " + body.code)
# I could discover n in an error loop. Cheeky. Or maybe inspect can determine?

def quote_lam(f):
    names = inspect.signature(f).parameters.keys()
    body = f(*[Code(name) for name in names])
    return Code("lambda " + ", ".join(names) + ": " + body.code)
# I could discover n in an error loop. Cheeky. Or maybe inspect can determine?

def quote(x):
    if isinstance(x, Code):
        return Code(repr(x))
    elif callable(x):
        return quote_lam(x)
    else:
        return Code(repr(x))


#quote_lam(lambda x,y: x, 2)
quote_lam(lambda x,y: x)

quote("hello")
quote(lambda x,y: x + 3 + 4)

assert quote(lambda x,y: 3 + 4 + x) == Code("lambda x, y: 7 + x") # a little normalization
assert quote(lambda x : [1,3,4] + [4,5,6] + x) == Code("lambda x: [1, 3, 4, 4, 5, 6] + x")

def pow(x, n):
    if n == 0:
        return 1
    elif n == 1:
        return x
    else:
        return x * pow(x, n - 1)

assert quote(Code("3")) == Code("Code(code='3')")
quote(lambda x: pow(x, 3))
```
