---
title: Semantic Refinement/Dependent Typing for Knuckledragger/SMTLIB Pt 1
date: 2025-08-04
---

It has been a question from the beginning how to emulate dependent types in Knuckledragger.

[Knuckledragger](https://github.com/philzook58/knuckledragger) is an interactive proof assistant designed as a python library very shallowly around [Z3py](https://ericpony.github.io/z3py-tutorial/guide-examples.htm). It can also be viewed as a minimal layer on top of [SMTLIB](https://smt-lib.org/) to make it scale as an interactive proof system.

The theory of Arrays in SMTLIB is a theory of first class functions and lambda notation was recently added to the standard although it's been available in Z3 for a while. This makes SMTLIB basically a higher order logic (HOL), although you shouldn't expect good things to happen if you get too funky with it.

SMTLIB is also basically a functional programming language.

The refinement typing approach, as exemplified by [Liquid Haskell](https://ucsd-progsys.github.io/liquidhaskell/), is a paradigm that can add annotations to a preexisting language in order to add verification capabilities <https://arxiv.org/pdf/1610.04641> . Basically you can add extra tags describing the subsets of the base types you expect to allow as inputs and emit as outputs of base language functions.

Since the appropriate subset of SMTLIB is a functional programming language, it makes sense to attempt to add refinement type to it. Why not? One can hope that this will actually be somewhat elegant, since Refinement typing is achieved in systems

The code of the post is extracted from the development [here](https://github.com/philzook58/knuckledragger/blob/9eca63380b52731e8eec5b71551e6837d0b02ba5/kdrag/contrib/telescope.py)

# Types as Subsets

Pretty much any syntactic logical system has to demonstrate how it can actually mean something, by giving examples of a semantics aka interpretations into something we're more familiar with. If I tell you a bunch of syntactic rules about "bleep" "blorp" and "bizzle", that won't hold your attention for long.

Dependent types and type systems are often presented syntactically. There is a syntax for terms, a syntax for types, and an operational semantics / baked in notion of definitional equality. Perhaps because they want to claim themselves as a foundation, models are somewhat under emphasized.

There are a number of possibilities for [models](https://www.cs.uoregon.edu/research/summerschool/summer14/rwh_notes/ssdt.pdf) of dependent type theory. In the most basic model, types are basically interpreted as sets <https://www.philipzucker.com/frozenset_dtt/> .  The (a?) subset model interprets types as a a pair of a set and a subset of that set. For example, the type `[[Pos]] = {x : Nat | x > 0}` is the pair of the Ints and the subset of Ints greater than zero.

I want to shallowly embed this model into SMTLIB. This is not an unknown thing and what I'm doing is probably closest in spirit to PVS's approach <https://www.csl.sri.com/papers/tse98/tse98.pdf> . Subsets can be represented in smtlib/HOL as [characteristic functions](https://en.wikipedia.org/wiki/Indicator_function) like `Pos = smt.Lambda([x], x > 0)`.  The set you're cutting the subset out of is implicitly there are the SMTLIB sort of the variable. It is perfectly possible to have a parametrized family of subsets like the set of all numbers greater than `n` `GE(n) = {x : Int | x >= n}` or in python as

```python
x = smt.Int("x")
def GE(n):
    return Lambda([x], x >= n)
```

## Telescopes

In ordinary z3/HOL metaprogramming, it was often useful to pass around a list of variables `[x, y, z]` as a notion of context. These lists are handed to the Z3py functions `ForAll` and `Exists` for example.

Generalizing this, the data of a dependent context (a telescope) can be given as a list of tuples of variables and what subset they are expected to be in. For example `[(x, Pos), (y, GE(x))]`. These telescopes can be given meaning into the logic of z3 by a combinator `TForAll` which interleaves applying `ForAll` of the variables and `Implies` for the subset constraint.

It is convenient to generalize this telescope to allow intermixing subsets, propositions, and no constraints (implicit `Lambda([x], True)`).  If you use proposition style, it looks like refinement typing `[(x, x > 0), (y, y >= x))]`. If you use subset style, it looks like dependent typing. They are very similar systems. Refinement typing systems a la Liquid Haskell are dependently typed in this sense and do bind variables to values in the type signature. This notation convenience can be normalized away by a function `normalize` which puts the more user pleasant form of the telescope into the propositional refinement form.

```python
type SubSort = smt.QuantifierRef | smt.ArrayRef
type Type = SubSort

"""
User telescope type.

Telescopes are dependent or refined contexts of variables.
They can tag variables with SubSet expressions or formulas that involve the bound variable.
Internally, the are normalized to _Tele, which is a list of (variable, formula) pairs.
"""
type Telescope = list[
    tuple[smt.ExprRef, smt.BoolRef] | tuple[smt.ExprRef, SubSort] | smt.ExprRef
]
# Internal normalized telescope
type _Tele = list[tuple[smt.ExprRef, smt.BoolRef]]


def normalize(xs: Telescope) -> _Tele:
    """
    Normalize a telescope to a list of (variable, formula) pairs.

    >>> x, y, z = smt.Ints("x y z")
    >>> normalize([x, y, z])
    [(x, True), (y, True), (z, True)]
    >>> normalize([(x, x > 0), (y, y > x), z])
    [(x, x > 0), (y, y > x), (z, True)]
    >>> normalize([(x, smt.Lambda([x], x > 0)), (y, smt.Lambda([y], y > x)), z])
    [(x, x > 0), (y, y > x), (z, True)]
    """
    res: _Tele = []
    for v in xs:
        if isinstance(v, tuple):
            (v, T) = v
            if T.sort() == smt.BoolSort():
                assert isinstance(T, smt.BoolRef)
                res.append((v, T))
            elif isinstance(T, smt.ArrayRef) or (
                isinstance(T, smt.QuantifierRef) and T.is_lambda()
            ):
                P = T(v)
                assert isinstance(P, smt.BoolRef)
                res.append((v, P))
            else:
                raise TypeError(f"Unsupported type for quantifier: {T}")
        else:
            res.append((v, smt.BoolVal(True)))
    return res

```

```python
def TForAll(xs: Telescope, P: smt.BoolRef) -> smt.BoolRef:
    """
    Dependent forall quantifier for a telescope of variables.
    Kind of like a proof irrelevant Pi type.

    Subtype / Refinement style usage

    >>> x, y, z = smt.Reals("x y z")
    >>> TForAll([(x, x > 0), (y, y > x)], y > -1)
    ForAll(x, Implies(x > 0, ForAll(y, Implies(y > x, y > -1))))

    "Dependent type" style usage

    >>> Pos = smt.Lambda([x], x > 0)
    >>> GT = lambda x: smt.Lambda([y], y > x)
    >>> TForAll([(x, Pos), (y, GT(x))], y > -1)
    ForAll(x, Implies(x > 0, ForAll(y, Implies(y > x, y > -1))))
    """
    for v in reversed(xs):
        if isinstance(v, tuple):
            (v, T) = v
            if T.sort() == smt.BoolSort():
                P = kd.QForAll([v], T, P)
            elif isinstance(T, smt.ArrayRef) or (
                isinstance(T, smt.QuantifierRef) and T.is_lambda()
            ):
                P = kd.QForAll([v], T(v), P)
            else:
                raise TypeError(f"Unsupported type for quantifier: {T}")
        else:
            P = kd.QForAll([v], P)
    return P

```

## Semantic Typing

The soundness of the model says that for each syntactic typing rule `|-`, there ought to be a theorem we can write for the model `|=` that follows along. The type system rules in the way can be seen as a higher level tactic system or macro rules for the model. This is the semantic approach to typing. One place you can see this is in papers on foundational proof carrying code. <https://link.springer.com/chapter/10.1007/978-3-540-32033-3_29> <https://www.cs.princeton.edu/~appel/papers/fpcc.pdf> <https://www.cs.princeton.edu/techreports/2000/629.pdf>

It appears that most facilities and combinators in knuckledragger can be generalized to have a telescoped counterpart (define, Proof, prove, axiom, ForAll, Exists, Lambda, Calc, Lemma, etc). I like the conceptual simplicity of the current core, so I think I am not inclined to make this telescoped form the default of the entire system yet.

An interesting tactic one can write is a `has_type` tactic. This tactic takes in a telescope `tele`, term `t`, and subset `T`, and tries to prove that `TForAll(tele, T[t])`. By having a registry of semantic types associated to `FuncDeclRef`, we can accumulate subset constraints from the body of `t`.

```python

def has_type(ctx: Telescope, t0: smt.ExprRef, T: SubSort, by=None) -> kd.Proof:
    """
    Tactic to check that an expression `t0` has type `T` in a context `ctx`.

    >>> x = smt.Int("x")
    >>> Nat = smt.Lambda([x], x >= 0)
    >>> has_type([(x, Nat)], x+1, Nat)
    |= Implies(And(x >= 0), Lambda(x, x >= 0)[x + 1])
    """
    tele = normalize(ctx)
    pctx = [P for _, P in tele]
    if by is None:
        by = []
    seen = set()
    todo = [t0]
    while todo:
        t = todo.pop()
        if smt.is_app(t):
            children = t.children()
            decl = t.decl()
            for c in children:
                if c not in seen:
                    todo.append(c)
                    seen.add(c)
            # TODO. Could recursively cut the children. Localize type error better.
            if decl.name() == "ann":
                try:
                    x, T = children
                    by.append(has_type(ctx, x, T, by=by))
                    # TODO: unfold ann. by.append(kd.kernel.defn)
                    # actually with new definition, ann is in _tsig
                except Exception as e:
                    raise TypeError(f"Invalid annotation {t} in context {ctx}", e)
            if decl in _tsig:
                by.append(_tsig[decl](*children))

    return kd.prove(smt.Implies(smt.And(pctx), T[t0]), by=by)
```

As written, `has_type` feels a little inelegant to me. I would like it to look more like bidirectional typing.  <https://arxiv.org/abs/2010.07763> <https://arxiv.org/abs/1908.05839> Currently it looks more like the "produce constraints and solve" style of type checking I associate with Hindley Milner systems because I just followed my nose. I could also has recursive calls to `has_type` rather than collecting a big old bag of lemmas. There is a funny incentive in Z3py metapgoramming that actually AST manipulationg through ctypes FFI is so slow you may be better off just handing a big of garbage to a Z3 solver than doing low level proof construction. I wish the z3 ffi python bindings were faster.

## Partial Definitions

Another interesting thing to do is generalize `define` to take a input telescope and an output subset. This puts some guard rails on partially defined functions. It also adds the typing annotations into the registry inside the body of `prove_sig`

```python
def define(
    name: str, args: Telescope, T: SubSort, body: smt.ExprRef, by=None
) -> smt.FuncDeclRef:
    """
    Define a function with a precondition given by a telescope of arguments
    and a postcondition given by a subset that output will lie in.

    Automatically

    >>> n = kd.kernel.SchemaVar("n", smt.IntSort())
    >>> m = smt.Int("m")
    >>> Nat = smt.Lambda([n], n >= 0)
    >>> Pos = smt.Lambda([n], n > 0)
    >>> inc = define("test_inc", [(n,Nat)], Pos, n + 1)
    >>> inc.pre_post
    |= ForAll(n!...,
        Implies(And(n!... >= 0),
            Lambda(n!..., n!... > 0)[test_inc(n!...)]))
    >>> pred = define("pred", [(n, Pos)], Nat, n - 1)
    >>> myid = define("myid", [(n, Nat)], Nat, pred(inc(n)))
    """
    P1 = has_type(args, body, T, by=by)
    tele = normalize(args)
    vs = [v for (v, _) in tele]
    for v in vs:
        if not kd.kernel.is_schema_var(v):
            raise TypeError(f"Arguments must be schema variables: {v}")
    f = kd.define(name, vs, body)
    prove_sig(f, args, T, by=[P1, f.defn(*vs)])
    return f
```

## Examples

Here is some mild usage of these tools. We can define functions `inc` and `pred` over these subsets. Inside of `define`, these definitions are being semantically type checked that they meet the appropriate subset conditions. Everything also takes an optional `by` parameter, allowing them to be handed useful extra lemmas in case Z3 can't do it all in one shot.

```python
from kdrag.contrib.telescope import *
from kdrag.all import *

x,n,m = kd.tactics.SchemaVars("x n m", smt.IntSort())
Nat = smt.Lambda([x], x >= 0)
Pos = smt.Lambda([x], x > 0)

n = kd.kernel.SchemaVar("n", smt.IntSort())
inc = define("test_inc", [(n,Nat)], Pos, n + 1)
inc.pre_post
pred = define("pred", [(n, Pos)], Nat, n - 1)
myid = define("myid", [(n, Nat)], Nat, pred(inc(n)))
```

Here is using Z3's built in notion of Sequence to make length indexed lists.  

```python
SeqInt = smt.SeqSort(smt.IntSort())
l,u,v = kd.tactics.SchemaVars("l u v", SeqInt)
Vec = smt.Lambda([x], smt.Lambda([l], smt.Length(l) == x))
# A Vector of Nat? Awkward

app = define("myappend", [(n,Nat), (m, Nat), (u, Vec(n)), (v, Vec(m))], Vec(n + m), 
                    smt.Concat(u,v))
has_type([(l, Vec(x)), (v, Vec(n)), (u, Vec(m))], 
        app(x, n + m, l, app(n, m, v, u)), 
        Vec(n + m + x))
```

It is somewhat awkward that `n` and `m` need to be explicitly passed in to `app`. This can be removed at least in this case by replacing the parameters by their constrained values manually.

```python
ulen = smt.Length(u)

app = define("myappend", [(u, Vec(ulen)), (v, Vec(smt.Length(v)))], Vec(ulen + smt.Length(v)), 
                    smt.Concat(u,v))
app.pre_post
```

A Pi combinator

```python
def Pi(tele0: Telescope, B: SubSort) -> SubSort:
    """
    Multiarity Pi. Dependent Function subsort
    B is a family because it may include parameters from tele0.

    >>> x, y = smt.Ints("x y")
    >>> GE = lambda x: smt.Lambda([y], y >= x)
    >>> Pi([(x, Nat)], GE(x))
    Lambda(f!...,
        ForAll(x, Implies(x >= 0, Lambda(y, y >= x)[f!...[x]])))
    >>> smt.simplify(Pi([(x, Nat)], GE(x))[smt.Lambda([x], x)])
    True
    """
    tele = normalize(tele0)
    vs = [v for v, _ in tele]
    # TB: SubSort = B(*vs)  # B is a family of sorts
    sorts = [v.sort() for (v, _) in tele]
    fsort = smt.ArraySort(*sorts, subsort_domain(B))
    f = smt.FreshConst(fsort, prefix="f")
    return smt.Lambda([f], TForAll(tele0, B[f(*vs)]))
```

An identity type combinator. It is a little weird to have a unit type that is basically irrelevant. More informative identity proof objects might be interesting.

```python
Unit = kd.Inductive("Unit")
Unit.declare("tt")
Unit = Unit.create()

def Id(x: smt.ExprRef, y: smt.ExprRef) -> SubSort:
    """
    >>> x, y = smt.Ints("x y")
    >>> p = smt.Const("p", Unit)
    >>> has_type([x], Unit.tt, Id(x, x))
    |= Implies(And(True), Lambda(p!..., x == x)[tt])
    >>> has_type([x, y, (p, Id(x,y))], Unit.tt, Id(y, x))
    |= Implies(And(True, True, x == y), Lambda(p!..., y == x)[tt])
    """
    p = smt.FreshConst(Unit, prefix="p")
    return smt.Lambda([p], x == y)
```

A hack to add annotation metadata like an interior `foo : T` annotation is to make special identity (or projection) functions that the metasystem knows to do something with. I saw something similar in the Lean typeclass mode annotations. The projection functions are pretty similar to EGraph ASSUME nodes. <https://arxiv.org/pdf/2205.14989> . Is there a better name for the semantic concept? Kind of they are similar to projection functions too, except I've chosen to leave being outside the range undefined rather than projecting into the subset (how would you project into an empty subset anyway?)

```python
@functools.lru_cache(maxsize=None)
def _gen_annotate(S: smt.SortRef):
    x, y = kd.tactics.SchemaVars("x y", S)
    T = kd.kernel.SchemaVar("T", smt.ArraySort(S, smt.BoolSort()))
    assert isinstance(T, smt.ArrayRef)
    return define(
        "ann",
        [(x, T), T],  # This is breaking telescoping rules. Is that ok?
        smt.Lambda([y], y == x),
        smt.If(T[x], x, smt.FreshFunction(S, S)(x)),
    )


def ann(x: smt.ExprRef, T: SubSort) -> smt.ExprRef:
    """
    Annotate an expression with a type.

    >>> x = smt.Int("x")
    >>> Nat = smt.Lambda([x], x >= 0)
    >>> ann(x, Nat)
    ann(x, Lambda(x, x >= 0))
    """
    return _gen_annotate(x.sort())(x, T)
```

# Schema Vars

On a slightly different tact, a new feature in Knuckledragger that I'm very excited about is Schematic Variables.

The big thing that SMT solvers need guidance on is quantifiers. By and large, they can deal with unquantified formula very well on their own.

So, Knuckledragger has some other inference rules bolted on. You can instantiate universally quantified proofs to eliminate forall.

```
|= forall x, P(x)
------------------- instan
      |= P(c)
```

To introduce forall is more complicated. Previously, I've been using a hebrandization axiom schema. Given any formula `forall x, P(x)` I can give you the axiom.

```
---------------------------------- herb
   |= P(c_fresh) => forall x, P(x)
```

Now if you can prove `P(c_fresh)`, you get the quantifier by modus ponens. This is [implemented](https://github.com/philzook58/knuckledragger/blob/9eca63380b52731e8eec5b71551e6837d0b02ba5/kdrag/kernel.py#L399) as a function that returns the fresh constant

```python
def herb(thm: smt.QuantifierRef) -> tuple[list[smt.ExprRef], Proof]:
    """
    Herbrandize a theorem.
    It is sufficient to prove a theorem for fresh consts to prove a universal.
    Note: Perhaps lambdaized form is better? Return vars and lamda that could receive `|= P[vars]`
    """
    assert smt.is_quantifier(thm) and thm.is_forall()
    herbs = fresh_const(thm)  # We could mark these as schema variables? Useful?
    return herbs, axiom(
        smt.Implies(smt.substitute_vars(thm.body(), *reversed(herbs)), thm),
        ["herband"],
    )
```

Knuckledragger is implemented in an LCF style, where inference rules correspond to python functions. The things above the horizontal line are inputs to the function and it produces the thing below the line in a protected datatype. These kernel functions can be seen as smart constructors for a protected `Proof` datatype that wraps the formula and other metadata.

A more natural rule for introducing is

```
   |= P(c_fresh)
-------------------
 |= forall x, P(x)
```

But there is an implementation problem here. What do we mean by `c_fresh` if I don't get to generate them? `|= P(c_fresh)` comes in as an input to my kernel function, so I don't get to pick it. One solution would be to insist that `c_fresh` is a different syntactic category of the formula, a schematic variable. This is not really possible because I'm using Z3's AST for my formulas, which I cannot change. Another solution is to explicitly add a context `Gamma |= P` to my proof judgements that tracks all the variables at play. This is a big change and complex.

What I realized on a walk the other day is that I need a new judgement `fresh` that you receive when you create a fresh variable. To some degree, the variable have a name with an exclamation point `foo!852` is suggestive that it was freshly generated, but this is more systematic.

```
   |= P(c)       c fresh
------------------------ generalize
 |= forall x, P(x)
```

This is the current implementation <https://github.com/philzook58/knuckledragger/blob/9eca63380b52731e8eec5b71551e6837d0b02ba5/kdrag/kernel.py#L517> of this rule.

```python
@dataclass(frozen=True)
class _SchemaVarEvidence(Judgement):
    """
    Do not instantiate this class directly.
    Use `SchemaVar`. This class should always be created with a fresh variable.
    Holding this data type is considered evidence analogous to the `Proof` type that the var was generated freshly
    and hence is generic / schematic.

    One can prove theorem using this variable as a constant, but once it comes to generalize, you need to supply the evidence
    That it was originally generated freshly.
    """

    v: smt.ExprRef


def is_schema_var(v: smt.ExprRef) -> bool:
    """
    Check if a variable is a schema variable.
    Schema variables are generated by SchemaVar and have a _SchemaVarEvidence attribute.

    >>> is_schema_var(SchemaVar("x", smt.IntSort()))
    True
    """
    if not hasattr(v, "schema_evidence"):
        return False
    else:
        evidence = getattr(v, "schema_evidence")
        return isinstance(evidence, _SchemaVarEvidence) and evidence.v.eq(v)


def SchemaVar(prefix: str, sort: smt.SortRef) -> smt.ExprRef:
    """
    Generate a fresh variable

    >>> SchemaVar("x", smt.IntSort()).schema_evidence
    _SchemaVarEvidence(v=x!...)
    """
    v = smt.FreshConst(sort, prefix=prefix)
    v.schema_evidence = _SchemaVarEvidence(
        v
    )  # Is cyclic reference a garbage collection problem?
    return v


def generalize(vs: list[smt.ExprRef], pf: Proof) -> Proof:
    """
    Generalize a theorem with respect to a list of schema variables.
    This introduces a universal quantifier for schema variables.

    >>> x = SchemaVar("x", smt.IntSort())
    >>> y = SchemaVar("y", smt.IntSort())
    >>> generalize([x, y], prove(x == x))
    |= ForAll([x!..., y!...], x!... == x!...)
    """
    assert all(is_schema_var(v) for v in vs)
    assert isinstance(pf, Proof)
    return axiom(smt.ForAll(vs, pf.thm), by=["generalize", vs, pf])

```

The `herb` rule was quite painful to use. I think this new rule is fairly straightforward and much easier. It should make just about everything work better as it's usage propagates though Knuckledragger, because now I can more easily explicitly instantiate quantifiers inside of my tactics instead of leaving it up to z3.

# Telescopes vs Sequents

There is something at odds here.

In a telescope, new variables come into context one by one and the type can only refer to previous variables. It corresponds to a formula of the form `forall x, T[x] => forall y, T1(x)[y] => ,,,`  with universal and implies alternating

A sequent is kind of similar `vs; hyps |- conc` with a context of variables and a context of hypotheses. The ordering of the hypotheses and variables is not linked. The hypotheses can refer to any variables. It corresponds to formulas of the form `forall x y... , And(P(x,y,...), Q(x,y,...), ...) => Conc(x,y,z)`. THis form is actually nicer to deal with in knuckledragger. I want to let z3 handle modus ponens, but deal with quantifiers manually, so it makes sense to have them all out front where I can get at them. Also Z3 supports multi-arity quantifiers and functions intrinsically, whereas most pencil and paper dependent type theories of telescopes use currying for multi argument object. I have `QForAll` combinators in Knuckeldragger for the "sequent" form.

On the other hand, the telescoping form is kind of neat and more familiar maybe to someone looking for DTT analogs.

I think I'm splitting the difference a little bit.

# Bits and Bobbles

It's a work in progress. I am not fully satisfied by my solutions but I think it is kind of neat even where it's at.

Cody's Boole work had a refinement typing system from the get go. I maybe was trying to avoid it merely on that principle.

Algebraic datatypes I don't have licked. A topic for another day. I think I need to register a refinement of the type of the recognizers and constructors. Implicit parameters is kind of a problem here.

Systems have the ability to make implicit arguments. I'm having a hard time seeing how to do this here in an elegant way.

I have been trying to cut along the pre-existing grain of SMTLIB. I'm very much constrained in a self imposed and defined sense of elegance.

FOLP <https://isabelle.in.tum.de/library/FOL/FOLP/index.html> I think is interesting as adding proof objects to first order logic.

Telescopes are more fundamental to dependent types than the dependent types themselves. Telescopes are a notion of a dependent context.

I'm no longer sold on the self evident necessity or desirability of dependent types. They are fun, just like many topics in logic and programming are fun, and that is good enough reason to play with them. I wonder what the most prominent forms of logic will look like in 100 years? The calculus of constructions may be a bygone fad, but we'll still have C.

I'm not 100% sure the distinction between refinement typing, liquid typing <https://goto.ucsd.edu/~rjhala/liquid/liquid_types.pdf> , and predicate subtyping <https://www.csl.sri.com/papers/tse98/tse98.pdf> . I think liquid proposes to have better inference?

While much attention has been paid to the proof objects the justify individual smt calls, relatively little attention has been paid to the big steps linking multiple calls. The thing people do try to do is export SMT proofs to their system (coq, lean, isabelle, metamath, etc) and then do the linking in that system. It seems to me it is at least worthwhile to attempt to remove this indirection. Indirections are often a lot of effort and cost to maintain.

Emphasizing `define-fun` and `define-fun-rec` makes SMTLIB look like a first order functional programming language <https://semantic-domain.blogspot.com/2020/02/thought-experiment-introductory.html> , a target that is not considered often enough, blowing right past to lambdas. Lambdas are the ultimate pain in the ass.

There's a class of systems which offer a logic and programming language deeply integrated with SMT solvers.

I would love if smtlib had built in Nats even though it's only an implicit constraint away from Ints. <https://theory.stanford.edu/~nikolaj/z3navigate.html> Talk about reduction of refinements types in z3 here. relax and restrict combinators.

Something interesting

<https://arxiv.org/abs/2010.07763> Refinement Types: A Tutorial

I've been interested in seeing how close I can get to mimicking interesting other logical systems in basically SMTLIB using a bit of trickery and squinting. For example, here I tried to do some temporal and separation logic <https://www.philipzucker.com/shallow_logic_knuckle/>

A related system is [F*](https://fstar-lang.org/) , which is a fresh language designed for SMT discharged dependent types from the outset.

Models involving collections of terms feel circularly motivated (is circulairty bad? Can motivation, like [sets](https://plato.stanford.edu/entries/nonwellfounded-set-theory/), be non-well founded?).

Automata hashing
Telescopes
Schema Vars
Automated Assembly 3
Quickcheck Types

## Older Notes

I've played around with different styles, like explicitly tagging terms with a attribute `ctx` to carry their intended context of usage. I'm not so sure this is a good idea.

We can also make an explicit new form of `Proof` called `TProof` which carries the approriate new judgement. Also not convinced this is a good idea. It felt good, but also was just bloating.

```python

```

<https://lean-lang.org/functional_programming_in_lean/Programming-with-Dependent-Types/The-Universe-Design-Pattern/#Functional-Programming-in-Lean--Programming-with-Dependent-Types--The-Universe-Design-Pattern>
finite universes

Indicdes vs parameters

```python
from kdrag.all import *
import kdrag.datatype as dt
n = smt.Int("n")
Vec = dt.InductiveRel("Vec", n)
Vec.declare("Nil",  pred = n == 0)
Vec.declare("Cons", ("tl", Vec), pred = lambda x: x.rel(n - 1))
Vec.create()

```

```python
def Pi(tele0 : Telescope, B : Family) -> SubSort: # Multiarity Pi
    tele = normalize(tele0)
    vs = [v for v, _ in tele]
    TB = B(*vs)  # B is a family of sorts
    sorts = [v.sort() for (v, _) in tele]
    fsort = smt.ArraySort(*sorts, sort_domain(TB))
    f = smt.FreshConst(fsort, prefix="f")
    return smt.Lambda([f], smt.TForAll(tele0, TB[f(*vs)]))

ann(smt.Lambda([x], x), Pi([(x, Nat)]), Nat)

def Sigma(): ...
    # Not good tupling in smtlib
```

```python
class TProof(NamedTuple):
    tele: _Tele
    conc: smt.BoolRef
    pf: kd.Proof

    def __repr__(self):
        return f"{self.tele} |= {self.conc}"

    @classmethod
    def from_proof(cls, pf: kd.Proof) -> "TProof":
        """
        Create a TProof from a kd.Proof.

        >>> x, y = smt.Ints("x y")
        >>> pf = kd.prove(smt.ForAll([x], x + 1 > x))
        >>> TProof.from_proof(pf)
        [] |= ForAll(x, x + 1 > x)
        """
        assert isinstance(pf, kd.Proof)
        return TProof([], pf.thm, pf)

    def __call__(self, *args): ...


class TGoal(NamedTuple):
    tele: _Tele
    conc: smt.BoolRef

    def __repr__(self):
        return f"{self.tele} ?|= {self.conc}"


class Lemma: ...


class Calc:
    tele: _Tele
    start: smt.ExprRef
    t: smt.ExprRef
    pf: kd.Proof

    def __init__(self, ctx: Telescope, start: smt.ExprRef):
        self.tele = normalize(ctx)
        self.start = start
        self.pf = TProof(self.tele, start, kd.Proof(start))

# but I want to allow dependencies in the signautre. Kind of the point
def FunctionAxiom(name, *args: SubSort) -> smt.FuncDeclRef:
    """
    Declare a function symbol to have a given signature axiomatically.

    >>> n = smt.Int("n")
    >>> Nat = smt.Lambda([n], n >= 0)
    >>> FunctionAxiom("inc", Nat, Nat).pre_post
    |= ForAll(c!..., Implies(c!... >= 0, Lambda(n, n >= 0)[inc(c!...)]))
    """
    sorts = [subsort_domain(T) for T in args]
    f = smt.Function(name, *sorts)
    tele: Telescope = [
        (smt.FreshConst(sort), T) for sort, T in zip(sorts[:-1], args[:-1])
    ]
    T = args[-1]
    vs = [v for v, _ in tele]
    P = kd.axiom(TForAll(tele, T[f(*vs)]), ["user_sig"])
    f.pre_post = P
    if f in _tsig:
        print("Warning: Redefining function", f)
    _tsig[f] = P
    return f
```

Maybe all open_binder should use SchmeaVar

wf attached to variables instead. Interesting.

(v, P) vs v.P

```python
def TSchemaVar(name, sort : smt.SortRef) -> smt.ExprRef:
    """
    Create a schematic variable with the given name and sort.
    """
    v = smt.FreshConst(sort, prefix=name)
    return SchemaVarEvidence(v)
```

Sequent style

```python
from kdrag.all import *
def seq_view(pf : kd.Proof) -> tuple[list[smt.BoolRef], smt.BoolRef]:
    """
    View a proof as a sequence of hypotheses and a conclusion.
    Implies(smt.And(hyps), conc)

    """
    assert isinstance(pf, kd.Proof)
    thm = pf.thm
    assert smt.is_implies(thm)
    hyps, conc = thm.children()
    assert smt.is_and(hyps)
    return hyps.children(), conc

def normalize_hyps(hyps : list[smt.BoolRef]) -> list[smt.BoolRef]:
    """
    Normalize a list of hypotheses by removing duplicates and sorting them.
    """
    return sorted(set(hyps), key=lambda t: t.get_id())

def seq_normalize(pf : kd.Proof) -> kd.Proof:
    """
    Normalize a theorem of the form 
    """
    hyps, conc = seq_view(pf)
    thm = smt.Implies(smt.And(normalize_hyps(hyps.children())), conc)
    if proof_mode:
        return kd.axiom(smt.Implies(smt.And(normalize_hyps(hyps), conc), by=["seq_normalize", pf]))
    else:
        return kd.prove(thm, by=[pf])

a,b,c = smt.Bools("a b c")
p = kd.prove(smt.Implies(smt.And(b, a, a, c), a))
seq_normalize(p)

def weakenL(pf : kd.Proof, hyps1 : list[smt.BoolRef]) -> kd.Proof:
    """
    Weaken a proof by adding additional hypotheses.
    """
    hyps, conc = seq_view(pf)
    return kd.axiom(smt.Implies(normalize_hyps(hyps + hyps1), conc), by=["weaken", pf, *hyps])


def forallI(pf : kd.Proof, vs : list[smt.ExprRef]) -> kd.Proof:
    """
    Introduce universal quantifiers for the given variables.
    """
    hyps, conc = seq_view(pf)
    kd.utils.free_in(hyps, vs)
    return kd.axiom(smt.Implies(hyps, generalize(conc, vs)), by=["forallI", pf, *vs])


def forallE(f : kd.Proof, x : kd.Proof):
    """
    Eliminate a universal quantifier by instantiating it with a proof.
    """
    hyps, conc = seq_view(f)
    hyps1, conc1 = seq_view(x)
    return kd.axiom(smt.Implies(smt.And(normalize_hyps((hyps - conc1) + hyps1)), conc), by=["forallE", f, x])

    

def impliesI(pf : kd.Proof, hyp : smt.BoolRef) -> kd.Proof:
    """
    Introduce an implication with the given hypotheses.
    """
    hyps, conc = seq_view(pf)
    assert hyp in hyps
    return kd.axiom(smt.Implies(smt.And(hyps - hyp), smt.Implies(hyp, conc), by=["impliesI", pf, hyp]))
#return kd.axiom(smt.Implies(smt.And(normalize_hyps(hyps + hyps1)), conc), by=["impliesI", pf, *hyps1])

def piI(pf : kd.Proof, vs : list[smt.ExprRef]) -> kd.Proof:
    """
    Introduce a pi quantifier for the given variables.
    """
    hyps, conc = seq_view(pf)
    kd.utils.free_in(hyps, vs)
    return kd.axiom(smt.Implies(hyps, smt.Pi(vs, conc)), by=["piI", pf, *vs])
```

```python
from kdrag.all import *

n = smt.Int("n")
x = smt.Real("x")
RVec = kd.InductiveRel("RVec", n)
RVec.declare("Nil", pred=n == 0)
RVec.declare("Cons", ("hd", smt.RealSort()), ("tl", RVec), pred=lambda hd, tl: tl.rel(n - 1))
RVec = RVec.create()
v = smt.Const("v", RVec)
# We want to turn off Call overloading on type
smt.DatatypeSortRef.__call__ = lambda self, n: smt.Lambda([v], v.rel(n))
smt.DatatypeSortRef.__getitem__ = lambda self, n: smt.Lambda([v], v.rel(n))
kd.simp(RVec(2)[v])
(v, RVec[n])
```

```python



```

Right I can register things for constructors and deconstructors.
Then I learn stuff going into branches

Vec

Maybe an accessor that is only well formed under the right cirumstrances

Hmm. It just reveal the definition of

But the recorgnizer doesn't have access to the current context (?)

I could just reveal the definition for ForAll() on the indices. Hmm.

```python
n, m = kd.tactics.SchemaVars("n m", smt.IntSort())
x = smt.Real("x")
RVec = kd.Inductive("RVec")
RVec.declare("Nil")
RVec.declare("Cons", ("hd", smt.RealSort()), ("tl", RVec))
RVec = RVec.create()

v = smt.FreshConst(RVec, prefix="v")
RVecP = smt.Function("RVecP", smt.IntSort(), smt.ArraySort(RVec, smt.BoolSort()))
RVecP = kd.define("RVecP", [n], smt.Lambda([v], kd.cond(
    (v.is_Nil,  n == 0),
    (v.is_Cons, RVecP(n-1)[v.tl])
)))

b = smt.Bool("b")
prove_sig(RVec.is_Cons, [(v, RVecP(n))], smt.Lambda([b], smt.Implies(b, RVecP(n-1)[v.tl])), by=[RVecP.defn(n)])

```

```python
from kdrag.contrib.telescope import *
from kdrag.all import *
import kdrag
def register_inductive(ctx : Telescope, dt : smt.DatatypeSortRef):
    x = kd.kernel.SchemaVar("x", dt) #smt.FreshConst(dt, prefix="x")
    tele = normalize(ctx)
    vs = [v for v, _ in tele]
    T = smt.Lambda([x], dt.rel(x, *vs))
    b = smt.Bool("b")
    for i in range(dt.num_constructors()):
        recog = dt.recognizer(i)
        #constr = dt.constructor(n)
        #accs = [dt.accessort(i,j) for j in constr.arity()]
        pf = dt.rel.defn(x, *vs)
        rhs = pf.thm.arg(1)
        prove_sig(recog, [(x, T)], smt.Lambda([b], rhs), by=pf) 
n, m = kd.tactics.SchemaVars("n m", smt.IntSort())
x = smt.Real("x")
RVec = kd.InductiveRel("RVec", n)
RVec.declare("Nil", pred=n == 0)
RVec.declare("Cons", ("hd", smt.RealSort()), ("tl", RVec), pred=lambda hd, tl: tl.rel(n - 1))
RVec = RVec.create()
RVec.rel.defn  

register_inductive([n], RVec)
kdrag.contrib.telescope._tsig

```

Ok, so we can replace implicits with Metaprogramming. Which is what it is.
If we can statically determine what it should be, just write that

```python

old_call = smt.FuncDeclRef.__call__
def call_and_propagate(self, *args):
    t = old_call(self, *args)
    t.ctx = frozenset.union(*[a.ctx for a in args])
    return t
FuncDeclRef.__call__ = call_and_propagate

# Get a context of only the variabnle appearing in t
def ctx_of(bigctx, t):
    todo = [t]
    ctx = {}
    seen = set()
    while todo:
        t = todo.pop()
        if t in seen:
            continue
        if t in bigctx:
            todo.extend(bigctx[t])
            ctx[t] = bigctx[t]
            seen.add(t)

def synth(ctx, t):
    if t in ctx:
        return kd.prove(smt.Implies(ctx[t], ctx[t]))
    

def check(ctx, t, subset):
    if t in ctx:
        return kd.prove(smt.Implies(ctx[t], subset[y]))
```

```python
class Section():
    ctx : _Tele
    terms : 

    def SchemaVar(self, name, sort : )

def ann(x, T):
    # identity function showing intended subset. A projection function.
    ann = kd.define("ann", [x], smt.If(T[x], x, smt.FreshConst(x.sort(), prefix="ann_undefined")))
    return ann(x, T)

```

def forallI(v, pf : kd.Proof) -> kd.Proof:
    """
    Introduce a universal quantifier for the given variable.
    """
    hyps, conc = seq_view(pf)
    #assert v.prop in hyps
    hyps = hyps - v.prop # we get to delete property from hypotheses
    assert kd.kernel.is_schema_var(v)
    assert kd.utils.free_in(hyps, v), "Variable must not be free in the hypotheses"
    return kd.axiom(smt.Implies(smt.And(hyps), smt.ForAll([v], smt.Implies(v.prop, conc))), by=["forallI", pf, v, v.prop])

```python

```

the two style of tagging info to variables.

open_binder now tags the property on the varible instead of returning telescope tuple.

type _Tele = list[smt.ExprRef]
prop = smt.True

The prop tag is not part of the trust.
It is just hidden instructions.

Styles:

1. TProof(tele, conc, pf)
2. TProof(hyps, conc)  and a to_proof axiom schema
3. TProof(tele, conc, reasons)
4. |= Implies(hyps, conc)  have to pack and unpack.

contexts as ordered lists vs sets. Sets has some convevnient properties for mergability. Not requiring exactly the same stuff. They only need to

1. Tagging. t.ctx  t.P
2. Tupling  (t, P)
3. Subclassing  
4. Wrapping
5. Registries

SchemaVars have prop _assumptions_
Terms have prop  _assertions_ which can be contextual (TProof)

man I have completely lost it

t.refine
t.wf

What is the most natural multi-arity form?
forall x y z, And(p(x), q(y), r(z)) => yada
forall x y z, And(p(x), q(x,y), r(x,y,z)) => yada . THis should be telescoped
forall x y z, And(p(x,y,z), q(x,y,z), r(x,y,z)) => yada
forall x y z, P(x,y,z) => yada

If you want

synth. if subterms all have prop, we can synth

ctx synth is easy. just collect constraints from pieces

t.ctx
t.prop

A third jduegment min_ctx

v |- v minctx
union G1 G2 G3  |- f(t1,t2,t3)   minctx

synth can use minctx. synth can turn into minctx

def synth(t):
   saynth is done during term construction

def check(t, P):
    if hasattr("prop", t):
        kd.prove(t.ctx, smt.Implies(t.Prop, P))
    t.ctx, P[t]

```python

Hom = DeclareFunction("Hom", [a, b])
#Hom = smt.Function("Hom", Ob, Ob)
DeclareFunction("id", [a], Hom(a, a))
DeclareFunction("comp", [a, b, Hom(a, b), Hom(b, c)], Hom(a, c))
DeclareFunction("comp", [(f, Hom(a, b)), (g, Hom(b, c))], Hom(a, c))
```

```python

def assume(x, T):


ann(ann(x,T1), T2) == ann(x, T1 && T2)
T1 <= T2, T1[x] ==> ann(x,T1) == ann(x,T2) == x
T1 <= T2, ann(ann(x, T1), T2) == ann(x, T1)

#using refinement egraph alongside Coward's assume nodes


def TLambda(ctx: Telescope, body: smt.ExprRef) -> smt.ExprRef:
    return smt.Lambda([v for v, _ in ctx], smt.If(smt.And([P[v] for v,P in ctx]), ann(body,T), smt.FreshConst(body.sort(), prefix="lambda_undefined")))


#x.ann(T)

# In has_type tactic, take has_type as recusrive subcalls 

def has_type():

    ...
    if name == "ann": # Ann are shifts from check and synth?
        by.append(has_type(ctx, args[0], args[1]))
```

```python
from dataclasses import dataclass
_axiom = True
@dataclass(frozen=True)
class TProof(kd.kernel.Judgement):
    hyps : frozenset[smt.BoolRef]
    conc : smt.BoolRef
    reasons : list

    def to_proof(self) -> kd.Proof:
        """
        Convert this TProof to a kd.Proof.
        """
        thm = smt.Implies(smt.And(self.hyps), self.conc)
        return kd.axiom(thm, by=["TProof", self])
    
    @classmethod
    def from_proof(cls, pf : kd.Proof) -> 'TProof':
        """
        Create a TProof from a kd.Proof.
        """
        hyps, conc = seq_view(pf)
        return cls(frozenset(hyps), conc, ["from_proof", pf])
    
    @classmethod
    def ax(cls, P : smt.BoolRef) -> 'TProof':
        """
        Create a TProof from a single proposition.
        """
        assert isinstance(P, smt.BoolRef), "P must be a boolean expression"
        return cls.from_proof(kd.prove(smt.Implies(smt.And(P), P)))
        return cls(frozenset(P), P, ["ax", P])

def prove(hyps : list[smt.BoolRef], conc : smt.BoolRef, by=None) -> TProof:
    """
    Prove a theorem with the given hypotheses and conclusion.
    """
    if by is None:
        by = []
    pf = kd.prove(smt.Implies(smt.And(hyps), conc), by=by)
    return TProof.from_proof(pf)

def forallE(pf : TProof,  x : TProof):
    # Do I refuie f to have empty context, equal contexts?

p = smt.Bool("p")
TProof.ax(p)
```

```python
def TSchemaVar(name : str, subtype : smt.ArrayRef = None):
    sort = subtype.domain()
    assert subtype.range() == smt.BoolSort(), "Subtype must be an array of booleans"
    v = SchemaVar(name, sort)
    v.prop = TProof.ax(subtype[v])  # P |= P
    #v.wf # kind of
    return v

def Refine(v : smt.ExprRef, prop : smt.BoolRef) -> smt.ExprRef:
    assert kd.kernel.is_schema_var(v), "v must be a schema variable"
    v.prop = TProof.ax(prop)
    return v

def HasProp(ctx : list[smt.BoolRef], t : smt.ExprRef, prop : smt.BoolRef, by=[]) -> smt.ExprRef:
    """
    Check if a term has a property.
    """
    t.prop = prove(ctx, prop, by=by)
    return t
```

```python
def forallI(pf : TProof, v : smt.ExprRef) -> kd.TProof:
    """
    Introduce a universal quantifier for the given variable.
    """
    assert kd.kernel.is_schema_var(v), "Variable must be a schema variable"
    hyps = kd.hyps.remove(v.prop)
    assert all(kd.utils.free_in(hyp, v) for hyp in hyps), "Variable must not be free in the hypotheses"
    return TProof(hyps, smt.ForAll([v], smt.Implies(v.prop, pf.conc)), ["forallI", pf, v, v.prop])

def forallE(f : TProof, t : smt.ExprRef) -> kd.TProof:
    assert isinstance(f, TProof), "f must be a TProof"
    assert isinstance(t.prop, TProof), "x must be an ExprRef"
    f.hyps - t.has_prop


def TLambda(vs : list[smt.ExprRef], body : smt.ExprRef) -> smt.ExprRef:
    t = smt.Lambda(vs, body)
    t.pre = [v.prop for v in vs]

def apply(f : smt.ExprRef, *args : list[smt.ExprRef], by=[]) -> smt.ExprRef:
    """
    Apply a function to the given arguments.
    """
    for pre, arg in zip(f.pre, args):
        prove(pre, )
        return f(*args)

def prove(ctx, prop, by=[]):
    return TProof.from_proof(kd.prove(smt.Implies(smt.And(ctx), prop), by=[p.to_proof() if isinstance(p, TProof) else p for p in by]))

def has_type(ctx, t, T, by=[]):
    t.has_prop = kd.prove(smt.Implies(smt.And(ctx), T[t]), by=by)
    t.has_prop.append(kd.prove(smt.Implies(smt.And(ctx), smt.ForAll([t], T(t))), by=by)) # multiple props. But then which ones...

def refine(ctx, t, prop, by=[]):
    t.has_prop = kd.prove(smt.Implies(smt.And(ctx), prop), by=by)

ProofS = smt.DeclareSort("ProofS")
# This is just a dummy thing to tag stuff onto
ProofS = smt.Datatype("Proof")
Proof.declare("MakeItSo")
Proof = Proof.create()


sort, subset = InductiveRel()
# subset is a funcdecl that returns a Set of sort.
# The _last_ argument should be 

Even = dt.InductiveRel("Even", n)
Even.declare("Zero", pred=lambda n: n == 0)

p = smt.Const("p", sort)
TForAll([n, (p, Even(n)), ]) ===>  ForAll(n, ForAll(p, Even(n)[p], ...))
            (p, Even.rel(n))

Even.rel(n)[p]

class TProof():
    vs : smt.ExprRef
    ctx : frozendict[int, smt.BoolRef] # all hypotheses are assoicated with some hypothesis.
    conc : smt.BoolRef

# Why does ordering even hurt us?
class TProof():
    tele : list[tuple[smt.ExprRef, smt.BoolRef]]
    conc : smt.BoolRef


class RefinedDecl(FuncDeclRef):
    #pre : list[SubSet]
    #post : SubSet
    pf : kd.TProof # |= forall arg0, T0[arg0], forall arg1, T1[arg1], ..., Tn[argn] => post(arg0, arg1, ..., argn)
    # forall a0 a1 a2, Implies(And(T0(a0), T1(a1), T2(a2)), post(T[f(a0,a1,a2)])))
    # The "Seqeunt" form is more natural since funcdecl are multiarity
    def __call__(self, *args):
        t = super().__call__(self, *args)
        t.pf = self.pf(*args)
        return t

class RefinedLambda(QuantiferRef):

```

```python
EqInt = dt.InductiveRel("EqInt", n)
EqInt.declare("Refl", ("m", smt.IntSort()), pred = lambda m: m == n)
EqInt = EqInt.create()
m = smt.Int("m")
p = smt.Const("p", EqInt)
EqIntSet = kd.define("EqIntSet", [n,m], smt.Lambda([p], smt.And(p.m == m, p.rel(n))))
# TEqInt
#[(p, EqIntSet(m,n))]
# so maybe I should rearrange how InductiveRel works? It should also define a predicate SetSort on the spine objects. The opposite currying of rel.
# it's impossible to use wf to auto infer a parameter version


```

```python
kd.NewType("Vec", smt.SeqSort(smt.IntSort()), pred=lambda v: smt.Length(v) == n)
# allow params?
kd.NewType1("Vec", , params=[n], pred=lambda x:  )

kd.SubSet("Vec", [n], smt.SeqSort(smt.IntSort()), pred=lambda v: smt.Length(v) == n)

smt.SortRef.__truediv__ = lambda x,y: SubSet()
SeqSort(smt.IntSort()) // smt.Lambda([n], smt.Length(n) == n)

## some kind of anonymous subset type
# use "refine" rather tha "wf"
x.refine
```

```python
def has_type(ctx, x, T): ...
    return TForAll(ctx, T[x])
def eq_type(ctx, T1, T): ...
    return TForAll(ctx, smt.And(T[x], T[y], x == y))
def def_eq(ctx, x, y, T): ...



type SetSort = ArraySortRef
type Family = Callable[[smt.ExprRef], SetSort]
def Pi(A : SetSort, B : Family):
    x = smt.FreshConst(A.domain(), prefix="x")
    f = smt.FreshConst(smt.ArraySort(A.domain(), B(x).domain()), prefix="f")
    return Lambda([f], kd.TForAll([(x, A)], B(x)[f(x)]))



# def Sigma

```

For any logic with an interpretation into Proof, we can do the same.
Separation logic (Iris?)

<https://rocq-prover.org/doc/v8.12/refman/language/extensions/match.html#matching-dependent>
<https://lean-lang.org/doc/reference/latest/Terms/Pattern-Matching/>

explicit motive annotations

```python
def open_tbinder(e : smt.QuantifierRef):
    tele = []
    while isinstance(e, smt.QuantifierRef):
        vs, body = kd.open_binder(e)
        assert len(vs) == 1
        v = vs[0]
        assert smt.is_implies(body)
        e = body.arg(1)
        tele.append((v, body.arg(0)))
        # predicate form as primary or not.
        # It feels like Lambdaifying it is just doing more work
        #tele.append((v, smt.Lambda([v], body.arg(0))))
    return tele, e

def open_qbinder(e : smt.QuantifierRef):
    assert isinstance(e, smt.QuantifierRef)
    vs, body = kd.open_binder(e)
    assert smt.is_implies(body)
    return vs, body.arg(0), body.arg(1)
```

```python
class TGoal():
    ctx : Tele
    t : 
    T : SetSortRef

class TProof(): # TAnswer? 
    ctx : Tele
    t : smt.ExprRef
    T : SetSortRef
    pf : kd.Proof

class TLemma():
    def __init__(self, thm):
        self.thm = thm
        self.lemmas = []

# recursors / induction principles for InductiveRel

# rec_define
def rec(x, T, f):
    S = x.sort()
    assert isinstance(S, smt.DatatypeSortRef)
    FreshFunction()
    for const in S:

from kdrag.all import *
type Telescope = list[tuple[smt.ExprRef, smt.BoolRef] | tuple[smt.ExprRef, smt.ArrayRef] | smt.ExprRef]
def TForAll(xs : Telescope, P : smt.BoolRef) -> smt.BoolRef:
    """
    Dependent forall quantifier for a telescope of variables.
    """
    for v in reversed(xs):
        if isinstance(v, tuple):
            (v, T) = v
            if T.sort() == smt.BoolSort():
                P = kd.QForAll([v], T, P)
            elif isinstance(T, smt.ArrayRef) or (isinstance(T, smt.QuantifierRef) and T.is_lambda()):
                P = kd.QForAll([v], T(v), P)
            else:
                raise TypeError(f"Unsupported type for quantifier: {T}")
        else:
            P = kd.QForAll([v], P)
    return P
x, y, z = smt.Reals("x y z")
kd.prove(TForAll([(x, x > 0), (y, y > x)], y > -1))
Pos = smt.Lambda([x], x > 0)
def GT(x):
    return smt.Lambda([y], y > x)
kd.prove(TForAll([(x, Pos), (y, GT(x))], y > -1))





def tinduct(x, P):

# what does a tmatch look like
def tmatch(x, cases, typ=None, params=None, motive=None):
    # typ is assumption about x
    # params are ?
    # motive is predicate about output?
def qmatch(x, )

def tpattern_match(t, pat, cond):


def tcond(): #? Does this make sense?


# isDefEq
def tunify(tele1, tele2): ...


```

```python
#Prop = kd.Enum("Prop", ["tt"])
# it shouldn't be prop. It's a proof object.
Proof = smt.DeclareSort("Proof")
refl = smt.Const("refl", Proof)
reflInt = smt.Function("reflInt", smt.IntSort(), Proof)
p = smt.Const("p", Prop)

[(p, x == y)] #==> forall p: x == y
def Eq(x,y):
    """
    Equality as a dependent type.
    """
    return smt.Lambda([p], x == y)
def Squash(b):
    p = smt.FreshConst(Prop)
    return smt.Lambda([p], b)

```

```python
n = smt.IntSort()
Nat = smt.Lambda([n], n >= 0)
Zero = smt.Lambda([n], n == 0)
Pos = smt.Lambda([n], n > 0)
Neg = smt.Lambda([n], n < 0)
Even = smt.Lambda([n], n % 2 == 0)
Odd = smt.Lambda([n], n % 2 == 1)

incr = kd.define("incr", [n], n + 1)
kd.pdefine("incr", [(n, Nat)], Nat, n + 1)
kd.pdefine("incr", [(n, Nat)], smt.Lambda([m], m > n), n + 1)

```

```python

```

<https://www.philipzucker.com/notes/Languages/ocaml/#universal-types>

<https://okmij.org/ftp/ML/trep.ml>

Boxing and unboxing.
My notes on "Any"  in knuckledragger

Hmm. Maybe I could do a single RecFunction for my universe levels. Then I do get to bake it in to z3.
Or for open recursion?

I do have existentials (?) Oh myyyyyy

Box = kd.Record("Box", (typ : 'a Code, val : TypeVar("a")))
Hmm. Yeah, I kind of need GADTs to use the tag trick.

def Get

<https://dl.acm.org/doi/10.1145/3649836> Persimmon: Nested Family Polymorphism with Extensible Variant Types. Poster at NEPLS

GADTs.

PInductive()
  pred=
  pred=

InductiveRel
wf
Why did I call it rel and not use the wf system?
That's weird.

```python
import kdrag.theories.seq as seq

def Vec(n, S):
    T = seq.Seq(S)
    x = smt.FreshConst(T)
    return smt.Lambda([x], smt.Length(x) == n)

def IVec(n):
    return Vec(n, smt.IntSort())
n = smt.Int("n")
Nat = smt.Lambda([n], n >= 0)
x,y = smt.Consts("x y", seq.Seq(smt.IntSort()))
tdefine("add", [(n, Nat), (x, IVec(n)), (y, IVec(n))],
smt.cond(
    (n == 0, Nil),
    default=Cons(x.head + y.head, add(n - 1, x.tail, y.tail) , 
    ), IVec(n)
)

#( add(n - 1, x.tail, y.tail) ,  Nat ))

TForAll([(n, Nat), (x, IVec(n)), (y, IVec(n))],   ? )

```

```python
# extensible sort of Codes
# Universes are an open type. Their codes are open
# This is exactly what the extensible tricks in ocaml are for. Keys. 'a tag

TypeCode = smt.DeclareSort("TypeCode")
# Code = smt.IntSort()
# El = OpenFunction()


def El(code):

```

```python
# Naaaaaah, doesn't really make sense.
def ann(x, T):
    undef = FreshConst(x.sort())
    smt.If(T(x), x, undef)

def Epsilon(T):
    FreshConst()
    smt.If(smt.Exists([y], T(y)) T(x), x, undef)

```

```python
def Pi(A,B): ...
def Pi(xA, B):
    (x,A) = xA
    #B(x, f(x)))) vs B(x)(f(x)) vs B(f(x))
    # Following prior conventions, B should just be a function expression that already contains x
    # B has to be a predicate. it can't contain it's variable.
    f = smt.FreshConst(smt.ArraySort(x.sort(), B(x).domain()))
    return smt.Lambda([f], TForAll([(x,A)], B(f(x))))
```

```python
type Type = smt.ArraySortRef | smt.QuantifierRef | smt.BoolRef

# domain cannot be inferred
def domain(A : TYPE):
```

Could record known substype and register different coercions

SHould All of these optionally take a Tuple?

def TForAll(vs, P):
    if isiinstance(P, tuple):
        P = P[1](P(0))

def tdefine(name, args, body):
    if isinstance(body, tuple):

```python
def subtype_dom(A):
    if isinstance(A, smt.QuantifierRef):
        return A.sort()

def is_subtype(A,B, by=[]):
    #x =
    return smt.Prove(A <= B, by=by)  #smt.IsSubSet()
    #return kd.prove(kd.TForAll([(x,A)], B(x)), by=by)
```

types are a syntactic discipline to enforce levels of abstraction

Type systems as tactic.

Homotopy type and transport and stuff probably says how to manually translate isomorphic based proofs. Which is what Talia was getting at?

Definitional equality checks use simp as subtactic.

```python


def TExists(xs : Tele, P : smt.BoolRef) -> smt.BoolRef:
    for v in reversed(xs):
        if isinstance(v, tuple):
            (v, T) = v
            if T.sort() == smt.BoolSort():
                P = kd.QExists([v], T, P)
            elif isinstance(T, smt.QuantifierRef) and T.is_lambda():
                P = kd.QExists([v], T(v), P)
            elif isinstance(T, smt.ArraySortRef):
                P = kd.QExists([v], T(v), P)
            else:
                raise TypeError(f"Unsupported type for quantifier: {T}")
        else:
            P = kd.QExists([v], P)
    return P

# TLambda
# TExists



def pdefine(name, args, out, body, by=[]):
    f = kd.define(name, args, smt.If(cond, body, undef))
    kd.prove(smt.TForAll(args, out(f(*args))))
    substypes[f] = SubTypeDefn(f, args, out, )

def subtype_tac(tele, P):
    # sweep though expression
    # prove TForAll(tele, P) via subtype abstractions.
    # Don't fail, output needed subproofs instead. Or raise with them?

subtypes = {}

# Gamma, x : T, Delta |- x : T
def refl_tele(tele, n : int) -> kd.Proof:
    (x,T) = tele[n]
    return kd.prove(smt.TForAll(tele, T(x)))




def synth(tele, t) -> tuple[Subsort, kd.Proof]:
    """
    Synthesize the type of an expression in a telescope.
    Returns a tuple of the type and a proof that the expression has that type.
    """
    if n := tele_vars(tele).find(t):
        return tele[n][1], refl_tele(tele, n)
    elif smt.is_app(t):
        decl, children = t.decl(), t.children()
        if t in subtypes:
            subtype_defn = subtypes[t]
            subproofs = [check(c, v) for c, v in zip(children, subtype_defn.tele)]
            kd.prove(smt.TForAll(subtype_defn.tele, subtype_defn.out(t(*t.children()))), by=subproofs + [subtype_defn.subtype_lemma])
            return subtype_defn.out, 
def check(tele, t, T) -> kd.Proof:


def ann(t,T):
    # refine
    # annotation is semantically an identity function. Or a refining function.
    x = FreshConst(t.sort())
    return kd.tdefine("ann", [(x,T)], T, x)

def ann(t, T):
    return has_type(?, t, T)

def restrict(f, T):
    # Can sensible annotate a term. If 
    xs = [smt.FreshConst(args) for arg in f.args]
    undef = smt.FreshFunction(*[x.sort() for x in xs], f.sort())
    return smt.Lambda([x], smt.If(T(f(*xs)), f(*xs), undef(*xs)))  # restrict f to the type T

def restrict(f, T, by=[]):
    if f in subtypes:
    # make new anonymous definition?
        return kd.tdefine(freshname, args, smt.And(T, Tf), f(), by=[f.subtype_lemma] + by)
    else:
        return kd.tdefine(freshname, args, T, f(args), by=by)

# i could tag metadata to kd.Proof objects. tele, vs. Or it could go in the reasons field... yikes.




def has_type(tele : Telescope, t : smt.ExprRef, T : smt.BoolRef, by=[], **kwargs):
    if n := tele_vars(tele).find(t):
        return refl_tele(tele, n)
    elif smt.is_app(t):
        decl, children = t.decl(), t.children()
        if decl in subtypes:
            subtype_defn = subtypes[decl]
            has_typ()


# Another case wherwe maybe my core Proof thing holding a context would be useful.
def has_type(tele : Telescope, t : smt.ExprRef, T : SubSort, by=[], **kwargs):
    # Tactic to prove TForAll(tele, T[t])
    # search through collecting up substypes.

    lemmas = [] # lemmas starts with tele somehow?
    todo = [t]
    # The let z3 handle it version.
    # The telescope character makes it annoying

    # get topological order of children and go bottom up?
    # compose ctx -> P ,  tele -> P1 moves
    # cut move   ctx -> P   ctx -> (P -> P1)  --->  ctx -> P1 
    # I need hilbert style combinators

    # Use BMC or horn solvers?
    # use consider axiom?
    while todo:
        t = todo.pop()
        if n := tele_vars(tele).find(t):
            lemmas.append(refl_tele(tele, n))

            #kd.prove(TForAll(tele, T(t)))

        if smt.is_app(t):
            decl, children = t.decl(), t.children()
            if decl in subtypes:
                subtype_defn = subtypes[decl]
                l = subtype_defn.subtype_lemma
                if len(children) > 0 and isinstance(l, smt.QuantifierRef) and l.is_forall():
                    l = l(children[0]) # One layer at least is easy
                lemmas.append(l)
                todo.extend(children)
        """
        if smt.is_app(t):
            decl,children = t.decl(), t.children()
            if decl in subtypes:
                subtype_defn = subtypes[decl]
                l = subtype_defn.subtype_lemma
                while smt.is_implies(l) or smt.is_forall(l):
                    if isinstance(l, smt.QuantifierRef) and l.is_forall():
                        c = children.pop()
                        l = l(c) # instantiate quantifier.
                    elif smt.is_implies(l):
                        goal = l.arg(0)
                        lemmas.append(kd.prove(goal, by=lemmas))
                        l = l.arg(1)
                for c in children:
                    kd.prove( )
                    l = l[c]
        """
    return kd.prove(smt.TForAll(tele, T(t)), by=by + lemmas, **kwargs) # unfold=1




```

idea: just using qforall would make the quantifer easier to instnatiate. Otherwise we need a
A => forall x, B    ---> A => B[t/x] rule

iterate uncurry and
A => forall x (B[x] => C)  ---> A => (B[t] => C) ---> and(A,B) => C

comp(acc, instan2(pf.arg(1), t)

Not all things of shape forall xs, A => B
can be easily turned into forall x0 A0 => forall x1 A1 => ,, (?)
Well. In some null sense forall x0 True, forall x1 True, ... forall xn A

Oh but I have that with compose instan2
    .  forall x phi(x) => phi(t)

QForAll([x], Nat(x), P) is fine.
But still would want to register.

Quantifiers are evil and implications are just whatever for smt. So it's not symmettric in that sense

What if cbs just get fired at the end and they delete non useful stuff.

What if GoalCtx was kept in sequent `forall xs, And(hyps) => P` normal form

Interesting... Use lemmas as a second stack. Does this work? It is lensy right? This is the trail.

Is there a way to do an earlier call to cbs?

maybe lemmas and cbstack

## Lemma callbacks

lemma : id -> [callback]
def add_lemma(p):
    pid = p.thm.get_id()
    cbs = lemma.get(p.thm.get_id())
    if isinstance(cbs, list):
        lemmas[pid] = p
        for cb in cbs:
            cb()
    elif isinstance(cbs, kd.Proof):
        pass
    else:
        raise UnExpcted

lookup proofs by get_id
Could also close branches by lookup up to see if already proven.
That's kind of interesting.

What if I put the callbacks on the goals stack. So then I call them as soon as the subgoals are done
Goals might be an iniaprrporatye name at this point.

goals.append(newgoal)
goals.append(cb)

t = self.subst[v]
        kd.kernel.abstract()

    goals.append(body)
    goals.append(cb)

class Lemma2
    def intros():
    def intro()

```python
Lemmas()
    self.lemmas = {}
    cbs: list[Callable[[], None]]

    def fixes(self):
        vs, ab = kd.kernel.herb(self.goals)
        def cb():
            a = lemmas[ab.thm.arg(0).get_id()]
            #a = lemmas.pop()
            #if p.thm.arg(0)
            pb = modus(ab, a)
            lemmas[pb.thm.get_id()] = pb
            lemmas.append(modus(a, ab))
        cbs.append(cb)
        cbs.append(lambda: self.lemmas.find(pf, t.arg(0)))
    def 

    def qed(self):
        for cb in reversed(cb):
            cb()
        return lemma.find(pf, self.topgoal)
```

also might help with eexists
subst[v] = whatever
And then cb can look for it

def eexists():
    vs, body = open_binder(goal)
    for v in vs:
        self.subst[v] = None
    def cb():

```python
from dataclasses import dataclass
from typing import Optional
from kdrag.all import *
from kdrag.notation import Telescope

type QCtx = tuple[list[smt.ExprRef], list[smt.BoolRef]]
type Telescope1 = list[tuple[smt.ExprRef, smt.QuantifierRef | smt.ArrayRef]]
type Telescope2 = 


@dataclass
class NormTele():
    vs : list[smt.ExprRef]
    pred : list[smt.ArrayRef | smt.QuantifierRef] # normalized into predicate form or normalize into Bool form?
    @classmethod
    def from_tele(cls, tele : Telescope) -> 'NormTele':
        vs = []
        pred = []
        for v in tele:
            if isinstance(v, tuple):
                (v, T) = v
                vs.append(v)
                if T.sort() == smt.BoolSort():
                    pred.append(smt.Lambda([v], T))
                elif isinstance(T, smt.ArrayRef) or (isinstance(T, smt.QuantifierRef) and T.is_lambda()):
                    pred.append(T)
                else:
                    raise TypeError(f"Unsupported type for quantifier: {T}")
            else:
                vs.append(v)
                pred.append(smt.Lambda([v], smt.BoolVal(True)))
        return cls(vs, pred)
    def precond(self):
        return smt.And(T(v) for v,T in zip(self.vs, self.preds))
    def eval(self, P):
        return smt.QForAll(self.vs, self.precond(), P)

#def tele_apply(pf : kd.Proof, *args) -> kd.Proof:
n,m,k = smt.Ints("n m k")
Nat = smt.Lambda([n], n >= 0)
NormTele.from_tele([(n, Nat), (m, m > 0), k])
```

```python

```

## Telescoped axioms

telescope normal form for Proofs forall x, p -> forall y, q -> ...

Qnormal form forall xs, ctx => A

```python
from kdrag.all import *
from kdrag.notation import Telescope, SubSort, TForAll, TExists
from typing import Optional
from dataclasses import dataclass

@dataclass
class SubTypeDefn():
    decl : smt.FuncDeclRef
    ctx : list[tuple[smt.ExprRef, smt.QuantifierRef | smt.ArrayRef]]
    T : Optional[smt.BoolRef]
    ax : kd.Proof # forall xs, tele(xs), out(f(xs))

def tele_vars(tele : Telescope) -> list[smt.ExprRef]:
    """
    Extract the variable names from a telescope.
    """
    return [v if isinstance(v, smt.ExprRef) else v[0] for v in tele]




def norm_tele(tele : Telescope) -> Telescope:
    acc = []
    for v in tele:
        if isinstance(v, tuple):
            (var, T) = v
            if isinstance(T, smt.ArrayRef) or (isinstance(T, smt.QuantifierRef) and T.is_lambda()):
                acc.append((var, T))
            elif T.sort() == smt.BoolSort():
                acc.append((var, smt.Lambda([var], T)))
            else:
                raise TypeError(f"Unsupported type for quantifier: {T}")
        else:
            acc.append((v, smt.Lambda([v], True)))
    return acc



def tele_cond(tele : Telescope) -> Optional[smt.BoolRef]:
    """
    Extract the condition from a telescope.
    """
    acc = []
    for v in tele:
        if isinstance(v, tuple):
            (v, T) = v
            if T.sort() == smt.BoolSort():
                acc.append(T)
            elif isinstance(T, smt.ArrayRef) or (isinstance(T, smt.QuantifierRef) and T.is_lambda()):
                acc.append(T(v))
            else:
                raise TypeError(f"Unsupported type for quantifier: {T}")
    if len(acc) == 0:
        return None
    elif len(acc) == 1:
        return acc[0]
    else:
        return smt.And(acc)

subtypes = {}

# allow synthesis of output Sort?
def tdefine(name, args : Telescope, T : SubSort, body, by=[]):
    """
    Define a subtype with a name.
    """
    tvars = tele_vars(args)
    body_lemma = kd.prove(TForAll(args, T(body)), by=by)
    undef = smt.FreshFunction(*[v.sort() for v in tvars], body.sort())
    cond = tele_cond(args)
    f = kd.define(name, tvars, smt.If(cond, body, undef(*tvars)))
    f.tele = norm_tele(args)
    f.subtype = T
    f.subtype_lemma = kd.prove(TForAll(args, T(f(*tvars))), by=[body_lemma, f.defn]) # I could do this more directly. It follows from a single unfold.
    subtypes[f] = SubTypeDefn(f, args, T, f.subtype_lemma)
    return f

n = smt.Int("n")
Nat = smt.Lambda([n], n >= 0)
incr = tdefine("incr", [(n, Nat)], Nat, n + 1)
incr.subtype_lemma
incr.subtype
incr.tele

def lookup(ctx : Telescope, v : smt.ExprRef) -> Optional[tuple[smt.ExprRef, smt.BoolRef]]:
    for v in ctx:
        if isinstance(v, tuple):
            (var, T) = v
            if var.eq(v):
                return (var, T)
        elif v.eq(v):
            return 

def check(ctx : Telescope, t : smt.ExprRef, T : SubSort) -> kd.Proof:
    S,pf = synth(ctx, t)
    if S.eq(T):
        return pf
    else:
        #kd.prove(smt.SubSet(S, T), by=[pf])
        return kd.prove(TForAll(ctx, T(t)), by=[pf])  # unfold=1


def synth(ctx : Telescope, t : smt.ExprRef) -> tuple[SubSort, kd.Proof]:
    """
    Check that an expression has a type in a telescope.
    """
    ctx = norm_tele(ctx)
    for (var, T) in ctx:
        if var.eq(t):
            return T, kd.prove(TForAll(ctx, T(var)))
    if smt.is_app(t):
        decl, children = t.decl(), t.children()
        if decl in subtypes:
            subtype_defn = subtypes[decl]
            T = subtype_defn.T
            subproofs = [check(ctx, c, T1) for c, (v, T1) in zip(children, subtype_defn.ctx)]
            return T, kd.prove(TForAll(subtype_defn.ctx, T(decl(*children))), by=subproofs + [subtype_defn.ax])
    else:
        raise TypeError(f"Could not synthesize type for {t} in {tele}")

synth([(n, Nat)], incr(incr(n) + 1))

```

```python
class FunSpec():
    decl : smt.FuncDeclRef
    #args : list[smt.ExprRef]
    #precond : smt.BoolRef
    #postcond : smt.BoolRef
    #bod
    thm : kd.Proof

fun_specs = {}

def qdefine(name, args, body, pre=None, post=None): # could make pre and post keyword args
    undef = smt.FreshFunction(*[v.sort() for v in args], body.sort())
    f = kd.define(name,   ,smt.If(precond, body, undef(*args)))
    kd.prove(smt.QForAll(args, precond, postcond), by=[body.defn] + 

def FunctionAxiom(name, *sorts, pre=None, post=None, by=[]): # Method ?
    f = smt.Function(name, *sorts)
    f.wf = kd.axiom(smt.QForAll(args, precond, postcond), by=[body.defn] + by)
    fun_specs[f] = FunSpec(f, f.wf)

Ob = smt.DeclareSort("Ob")
Arr = smt.DeclareSort("Arr")
Hom = smt.Function("Hom", Ob, Ob, smt.SetSort(Arr))
id_ = Function("id", Ob, Arr)
id_.wf = kd.axiom(kd.QForAll([a],Hom(a,a)(id_(a))))
fun_specs[id_] = FunSpec(id_, id_.wf)


comp = Function("comp", Arr, Arr, Arr, Arr)
comp.wf = kd.axiom(kd.QForAll([a,b,c,f,g], smt.Implies(smt.And(Hom(a,b)(f), Hom(b,c)(g)), Hom(a,c)(comp(f,g)))))
fun_specs[comp] = FunSpec(comp, comp.wf)

def lemmas(t):
    todo = [t]

def well_formed(vs, pre, t): # "synth"
    if t.decl() in fun_specs:
        spec = fun_specs[t.decl()]
        return kd.prove(smt.QForAll(vs, pre, spec.thm), by=[t] + lemmas(t))
    else:
        return kd.prove(smt.QForAll(vs, pre, smt.BoolVal(True)))

def qprove(vs, pre, P, by=[]): # "check" ?
    vs1, P1 = kd.kernel.herb(smt.QForAll(vs, pre, P))
    typ_lemmas

def qeq(vs, pre, t1, t2):
    lemmas = well_formed(vs, pre, t1)
    lemmas = well_formed(vs, pre, t2)


def wf_lemmas(t): #empty context
    res = []
    todo = [t]
    while todo:
        t = todo.pop()
        decl,children = t.decl(), t.children()
        if decl in fun_specs:
            spec = fun_specs[decl]
            res.append(spec.thm(*children))
            for c in children:
                res.extend(wf_lemmas(c))
    return res
        




```

```python
from kdrag.all import *
from kdrag.notation import Telescope, SubSort, TForAll, TExists
from typing import Optional
from dataclasses import dataclass

type QCtx = tuple[list[smt.ExprRef], list[smt.BoolRef]]
@dataclass
class SubTypeDefn():
    decl : smt.FuncDeclRef
    ctx : QCtx
    T : smt.QuantifierRef | smt.ArrayRef  # | smt.FuncDeclRef ?
    ax : kd.Proof # forall xs, precond, prop


def tele_to_qctx(tele : Telescope) -> QCtx:
    """
    Extract the condition from a telescope.
    """
    vs = []
    pred = []
    for v in tele:
        if isinstance(v, tuple):
            (v, T) = v
            vs.append(v)
            if T.sort() == smt.BoolSort():
                pred.append(T)
            elif isinstance(T, smt.ArrayRef) or (isinstance(T, smt.QuantifierRef) and T.is_lambda()):
                pred.append(T(v))
            else:
                raise TypeError(f"Unsupported type for quantifier: {T}")
        elif smt.is_const(v):
            vs.append(v)
            pred.append(smt.BoolVal(True))
        else:
            raise TypeError(f"Unsupported type for quantifier: {v}")
    return (vs, pred)

subtypes = {}

# allow synthesis of output Sort?
def tdefine(name, args : Telescope, T : SubSort, body, by=[]):
    """
    Define a subtype with a name.
    """
    vs,pred = tele_to_qctx(args)
    body_lemma = kd.prove(kd.QForAll(vs, *pred, T(body)), by=by)
    undef = smt.FreshFunction(*[v.sort() for v in vs], body.sort())
    f = kd.define(name, vs, smt.If(smt.And(pred), body, undef(*vs)))
    f.qctx = (vs, pred)
    f.subtype = T
    f.subtype_lemma = kd.prove(kd.QForAll(vs, *pred, T(f(*vs))), by=[body_lemma, f.defn]) # I could do this more directly. It follows from a single unfold.
    subtypes[f] = SubTypeDefn(f, (vs,pred), T, f.subtype_lemma)
    return f

n = smt.Int("n")
Nat = smt.Lambda([n], n >= 0)
incr = tdefine("incr", [(n, Nat)], Nat, n + 1)
incr.subtype_lemma
#incr.subtype
#incr.qctx


def has_type(ctx : Telescope, t : smt.ExprRef, T : SubSort, by=[], **kwargs):
    vs,pred = tele_to_qctx(ctx)
    def doit(vs1):
        todo = [smt.substitute(t, zip(vs1))]
        lemmas = []
        while todo:
            if smt.is_app(t):
                decl, children = t.decl(), t.children()
                if decl in subtypes:
                    subtype_defn = subtypes[decl]
                    lemmas.append(subtype_defn.ax(*children))
                    todo.extend(children)
        return lemmas
    return kd.prove(kd.QForAll(vs, pred, T(t)), by=by, instans=doit  ,**kwargs)

```

## qforall axioms

```
procedure test(x: Seq, y: Seq) returns (res: Seq)
requires NonEmpty(x) /\ NonEmpty(y);
ensures NonEmpty(res) {
  res := Append(x,y);
}
```

Boogie has intrinsic requires ensures stuff. Hmm.

Actually, should QForAll always / sometimes traverse the P term and get the well formedness conditions too?
QForAll([xs], precond, P)

TForAll([xs], T, P) #?
TForAll([xs], t, T) #?  HasType(xs, t, T)
WellFormed(ctx, pre, t)

That one partial function approach from nipkow reference suggested doing it at `==`

I feel like there is an assertion mode and checkingt mode? In one or the other

return tuple, vs return Anded Version inside quantifier.
def QForAll():
    objligations = wf(P)
    if len(obligations) == 0:
        return QForAll0
    return QForAll0([], cond, P) , QForAll([], cond, obl)
    vs return QForAll([], cond, And(P, oblig))
    vs return QForAll([], And(cond, oblig), P)

Quotients. Subsets ofg powerset stable wrt eq relation.
Set(IntSort()) |  lam A, forall x y, A[x], eq(x,y) => A[y]
def Quot(eq):
    T = eq.domain(0)
    S = SetSort(T)
    A = FreshConst(S)
    return smt.Lambda([A], QForAll([x,y], A[x], eq(x,y), A[y]))
Not higher order though.
def Quot(T : SubSet, eq):
    S = SetSort(T.domain())
    return smt.Lambda([A], QForAll([x,y], T[x], T[y], eq(x,y), A[x], A[y])
Hmm.

It is natural if I have QLambda and QForAll and QExists to also have qdefine.

Could match for QLambda . maybe associate the undefined false branch with the lambda.

if t == Lambda(, If(cond, , undef)):

```
# Just as a saniuty check
def QLambda(vs, *args, post=None)
    l = 
    if post 
    l.pf = kd.prove(QForAll( vs, cond, post())
```

This starts to feel more like Dafny.

If proof fails, explanation method could try to traverse don and see which preconditions fail.

From the subset typing persepctive. Dependent types are a methodology for deraling with partiality.

But so is precondition postcondition style reasoning.

What would be the analog of Q reasoning for other models of DTT?
Setoid Specs? Maybe a hoare logic style relational thing.
forall x0 y0, eq(x0,y0), => eq(f(x0),f(y0))
To always show representation independence

n = smt.Int("n")
[(n, Mod3)]
Obviously I can't have n == n % 3, because n is interpreted.

Or to show High Low security noninterference security properties
idefine([(n, High), (m, Low)], body,  Low)
Hmm.

or parametricity
DeclareSort("T")
TypeVar("T") ??? Uhh.
[(n, T), (m, S)]

The curried vs multiairty is a good analogy.
MultiArity Q form is like taking in a refinement tuple (x,y,z) : R(x,y,z)

QInductive is InductiveRel?

def QInductive():
    def create():
        dt = old_create()
        for i in d.num_constructors()
        fun_specs[d.constructor(i), kd.smt.QForAll(  )]
Q is sequent style basically.

class Sequent():
    vs : frozenset[smt.ExprRef]
    hyps : frozenset[smt.BoolRef]
    concs : frozenset[smt.BoolRef]

<https://fstar-lang.org/tutorial/proof-oriented-programming-in-fstar.pdf>

```python
def DepType(name, params, indices : list[smt.SortRef]): ...  # inductive name p[0] p[1] ... : ind[0] -> ind[1] -> Type
# first n positions have to match the index sorts. Can be constants to give implicit n == 3 constraint.

def TSchemaVar(name : str, subtype : smt.ArrayRef):
    sort = subtype.domain()
    assert subtype.range() == smt.BoolSort(), "Subtype must be an array of booleans"
    v = SchemaVar(name, sort)
    v.prop = subtype(v)
    #v.wf # kind of
    return v

def Refine(x : smt.ExprRef, prop : smt.BoolRef) -> smt.ExprRef:
    x.prop = prop
    return x

def TForAll():
    if hasattr("typ", v):
        p = v.typ

def tgeneralize(p : )

def open_binder(t : smt.QuantifierRef):
    """
    open binder tagging both variable and body with the context.
    We need the body tagged because to do recursive binder opening.
    """
    ctx = t.ctx
    [v], body = utils.open_binder(t)
    prop = body.args(0)
    ctx = ctx + [prop]
    v.ctx = ctx
    body = body.args(1)
    body.ctx = ctx
    return v, body
```
