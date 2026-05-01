---
title: Lifting and Lowering Functions with The Dump Calculus
date: 2026-05-01
---

I've been trying to think about how to make a nameless de bruijn-y e-graph and that has led me down a road to consider some interesting functional combinators for lifting and lowering functions.

These are an interesting set of combinators to kind of "first orderize" nearly trivial functional manipulations. By baking in the lifting with special support, I hope to get a nice, simple, efficient egraph that supports binders and alpha equivalence.

TLDR:

- Liftings add redundant arguments to functions
- Dumps partially apply functions to junk
- They are in a one-sided inverse relationship
- Co-de Bruijn is a normal form for lifting expressions by pulling them up maximally.

# Lifting

You can lift functions so that they can take more arguments. The thinning describes which arguments to drop. More on thinnings here <https://www.philipzucker.com/thin1/> . You can `thin` a tuple and use that combinator to contravariantly `lift` functions by thinning their arguments tuple.

```python
type Thin = list[bool]

def thin(t : Thin, l : tuple) -> tuple:
    # You thin a tuple
    assert len(t) == len(l), f"Expected {len(t)} arguments, got {len(l)}, with thin {t} and args {l}"
    return tuple(x for x, b in zip(l, t) if b)

def lift(t : Thin, f):
    # but you lift a function
    return lambda *args: f(*thin(t, args))

```

Here's some inputs and outputs

```python
thin([True, False, True], ("A", "B", "C"))
```

    ('A', 'C')

```python
lift([True, False, True], lambda x,y: x + y)("A", "B", "C")
```

    'AC'

I find Python friendly and concrete, but this operation can also be considered as a mathematical operation that takes one function into another, for example $ \{x,y,z \mapsto \sin(x)\} = lift_{100}(sin)$ where $lift_{100} : (\mathbb{R} \rightarrow \mathbb{R}) \rightarrow (\mathbb{R}^3 \rightarrow \mathbb{R})$

Note that two lifts can always be compressed into a single lift. $lift_k \cdot lift_l = lift_{k \cdot l}$. This is the composition of thinnings.

```python
lift([False, True, True], lift([True, False], lambda x: x + "Hi"))("a","b","c") == lift([False, True, False], lambda x: x + "Hi")("a","b","c") 
```

    True

# Dumping

But it seems also desirable / useful to have a notion of lowering functions too, a "dump".

There is more than one way of getting rid of arguments (more on this in later). One way you can lower functions by filling in some of the arguments with some kind of junk default.

The result of dump needs fewer variables. It partially applies `f` to junk values

You can `widen` a tuple and then use that combinator to contravariantly `dump` a function.

```python
def widen(t : Thin, l : tuple) -> tuple:
    assert sum(t) == len(l), f"Expected {sum(t)} arguments, got {len(l)}, with thin {t} and args {l}"
    it = iter(l)
    return tuple(next(it) if b else "JUNK" for b in t)

def dump(t : Thin, f):
    return lambda *args: f(*widen(t, args))
```

    ('A', 'JUNK')

```python
widen([False, True, False], ("A",))
```

    ('JUNK', 'A', 'JUNK')

```python
dump([True, False], lambda x,y: x + y)("A")
```

    'AJUNK'

dumping forms a one-sided inverse to lifting. <https://en.wikipedia.org/wiki/Inverse_element#Left_and_right_inverses>  `dump(t, lift(t, f)) == f` but not necessarily `lift(t, dump(t, f)) ?= f`.  
Lifting is an injective operation. If takes different inputs functions to different output functions. In one-sided inverses, on of the pair is injective and the other isn't, so it isn't a bijection.

# Lifted Identity is Variables

A nameless/semantic way to refer to variables is to use lifted identity functions. I did something similar here <https://www.philipzucker.com/z3_diff/> and the trick seems to show up again and again. It is also reminiscent of the perspective that on a manifold "x" "y" and "z" are just scalar functions from the manifold $M \rightarrow \mathbb{R}$.

```python
X = lift([True, False, False], lambda x: x)
Y = lift([False, True, False], lambda x: x)
Z = lift([False, False, True], lambda x: x)
```

```python
Y("A", "B", "C")
```

    'B'

```python
Z("A", "B", "C")
```

    'C'

# Partially Applied Composition for Functions

To actually work in this DSL, pre-existing functions need to have composition partially applied in order to take in functional arguments by `pcomp`. This is kind of a confusing point. There is both `sin : R -> R` but also `sin' : (T -> R) -> (T -> R)` where `sin' = sin .`. It can be confusing which one you are talking about if you're not careful.

This partial application of composition trick is what makes the ordinary functional notation like `lift(sin'(cos'(x)))` make sense since lift needs to be applied to a functional object, and `cos` is being applied to `x`, which is not a scalar, but instead of lifted identity function. Note that the composition is a little funky, since you compose with a tuple of functions `*gs`, not just one.

```python
def pcomp(f):
    return lambda *gs: lambda *args: f(*[g(*args) for g in gs])
```

Pre-existing constants need to be embedded as 0-arity functions by `const`.

```python
def const(x):
    #  embed constants as arity 0
    return lambda: x
import operator
inc = pcomp(lambda x: x + 1)
add = pcomp(operator.add)
pow = pcomp(operator.pow)
```

```python
e = add(inc(const(1)), const(2))
e # e is still thunked
```

    <function __main__.pcomp.<locals>.<lambda>.<locals>.<lambda>(*args)>

```python
e() # Invoke it to get the result
```

    4

```python
X = lambda x: x # In the single variable context X = Id
e = add(X, inc(X))
e(2) # e now takes an argument
```

    5

```python
X = lift([True, False, False], lambda x: x) # We are not in the three variable context
Y = lift([False, True, False], lambda x: x)

e = pow(X, Y)
e(2, 3, 600)

```

    8

```python
e1 = lift([False, True, True, True], e) # We can raise e to the 4 context
e1(4000, 2, 3, 600)
```

    8

```python
e1 = dump([True, True, False], e) # We don't need the last argument, so we can dump it
e1(2,3)

```

    8

In fact, since `e` does not use `Z`, we can `dump` and then `lift`  to get back the same function.

```python
lift([True, True, False], dump([True, True, False], e))(2,3,600) 
```

    8

This is reminiscent of Hughes lists (partially applied append), [Cayley representation](https://en.wikipedia.org/wiki/Cayley%27s_theorem) (partially applied group multiplication) and the [Yoneda embedding](https://en.wikipedia.org/wiki/Yoneda_lemma).

The following manipulation is kind of interesting as a way to think about converting from the pointful form to this goofy yoneda form. Kind of you can eta-long expand everything to ferry all arguments down and then turn the whole thing into the combinator version.

$ \{x,y \mapsto \sin(\cos(x)) \} = \{x,y \mapsto \sin(\{ a,b \mapsto \cos(\{ l,k \mapsto l \}(a,b)) \}(x,y)) \} = \sin '( \cos'(lift_{10}(id)))$

# Co-de Bruijn is Maximally Pulled Up Lifting

There a many redundant ways of writing the same function with liftings put in different spots. Can we pick a canonical place to put liftings? Yes.

Co-de Bruijn <https://arxiv.org/abs/1807.04085> is described as a method to deal with lambda binders, but my expression language does not contain lambdas at this point. In fact, Co-de Bruijn normalization makes sense in the absence of the lambda binders. If it basically noting that there is a normal form that pulls up any lifts as high as they will go. The entries of the `lift` kind of look like a free variable analysis.

The function `e1` below can be described in combinators

```python
e1 = lambda x,y,z : x*z + y
e1(2,3,4)
```

    11

```python
X = lift([True, False, False], lambda x: x)
Y = lift([False, True, False], lambda x: x)
Z = lift([False, False, True], lambda x: x)

mul = pcomp(lambda x,y: x*y)
add(mul(X,Z), Y)(2,3,4)
```

    11

But by keeping everything as thin as possible, this is a normal form. It is quite unpleasant to write manually though. In this form "everybody's got to be somewhere".

```python
Var = lambda x: x
add(lift([True, False, True], 
        mul(lift([True, False], Var), 
            lift([False, True], Var))), 
        lift([False, True, False], Var))(2,3,4)
```

    11

The core equality that makes this possible is "lift pushing" `lift(T, f(X,Y)) = f(lift(T, X), lift(T, Y))` and lift factoring / composition `lift(T1, lift(T2, X)) = lift(comp(T1, T2), X)` where thinning composition I have discussed in previous posts.

# Other Dump Operators

Rather than throwing in some default value (which I guess is working in pointed sets?) there are some other interpretations of dump. The other interpretations are kind of nice because they form a [galois connection](https://en.wikipedia.org/wiki/Galois_connection) / [adjunction](https://en.wikipedia.org/wiki/Adjoint_functors) to `lift`, but I dunno if that is useful.

Dump operations are often associated with binding forms

- `min_x` / `max_x` These form an adjoint pair with lifting using pointwise comparison of functions as the ordering on functions  `min_x {x,y |-> f(x,y)} <= g <-> f <= lift g`
- Expectation value `E_X`, integral, sum
- Partial functions have an ordering. We can define `dump` for partial functions such that either `dump_x(f)(y)` is undefined if the values of f do not agree for all values of x. This also forms a galois connection.

Substitution defines basically a family of `dump` operators, one per value you'd dump /partially apply into that argument. This gives you an algebra of partial application that is more flexible than just always partially applying the first argument. The `papply` operator has equational laws that interact with `lift` because if you are just throwing away an argument you don't have to continue partially applying it.

`Thicken` is still a proof object for how one list is a subsequence of another, but now it holds the missing bits from the smaller one in the right spots. It is `List<Option<T>>`

```python
type Thicken = tuple[object | None, ...]

def thicken(t : Thicken, l : tuple) -> tuple:
    it = iter(l)
    return tuple(next(it) if b is None else b for b in t)

def papply(t : Thicken, f):
    return lambda *args: f(*thicken(t, args))

```

```python
papply([None, 3], lambda x,y: x**y)(2)
```

    8

There might be an egraph that bakes in this kind of subst node or bakes in a fast subst eid. Substitution seems like it needs more juice to be pushed down than just rebuilding.

In a very peculiar way, lambda is also a kind of dump. It binds a variable and "gets rid of it" in some sense from the context. But it does so in a non destructive way by radically changing the type of the object under consideration and does not form a one-sided inverse with `lift`.

Making an adjunction is very tempting because lifting is basically [weakening](https://ncatlab.org/nlab/show/weakening+rule) and weakening is a member of one of the most famous adjunctions $\exists \dashv weak \dashv \forall$. Predicates are functions into some truth value and you can lift and dump them. <https://ncatlab.org/nlab/show/quantification#LawvereQuantifier> <https://ncatlab.org/nlab/show/hyperdoctrine> . I have not found such complex ideas useful to the task at hand and they are a distraction.

# Simple Generators for Lift and Dump

Lifting and dumping can also be presented using combinators that only lift a single argument at a time. I think it is important to show and emphasize the bulk form above though.

This is analogous to presenting permutations as dictionaries or some other normal form vs presenting them as compositions of swaps

These generators are like those for the common presentation of the simplicial category or simplicial sets like those here <https://en.wikipedia.org/wiki/Simplicial_set#Face_and_degeneracy_maps_and_simplicial_identities>

```python
def thin(i, l : tuple) -> tuple:
    return l[:i] + l[i+1:]
def thin(i : int, f):
    return lambda *args: f(*thin(i, args))

def wide(i, l : tuple) -> tuple:
    return l[:i] + ("JUNK",) + l[i:]
def dump(i : int, f):
    return lambda *args: f(*wide(i, args))

```

As a special case of lifting and dumping, we can only allow two sorts `R` and `FunR` and `lift : R -> FunR` and `dump : FunR -> R`. This is a particularly small lift/dump system. We could also cutoff at dimension 2.

You can see using property based testing to confirm how you push thin and dump through each other. Off by one errors are pretty easy to make. Basically they push through each other, but sometimes you have to increment or decrement an index.

This pushing around is perhaps the most what I'd call "The Dump Calculus"

Here I am using python cheekiness to have a tuple size polymorphic version of thin and wide.

```python
def thin(i,l):
    return l[:i] + l[i+1:]

def dump(i,l):
    return l[:i] + ["junk"] + l[i:]

import hypothesis.strategies as st
from hypothesis import given

# some examples
assert thin(1, thin(2,list(range(4)))) == thin(1, thin(1,list(range(4))))
assert thin(2, thin(1,list(range(4)))) == thin(2, thin(1,list(range(4))))

@given(st.integers(0,4), st.integers(0,4))
def thin_swap(i,j):
    l = list(range(8))
    if i < j:
        assert thin(i, thin(j,l)) == thin(j-1, thin(i,l))
    else:
        assert thin(i, thin(j,l)) == thin(j, thin(i+1,l))

thin_swap()

@given(st.integers(0,4), st.integers(0,4))
def dump_swap(i,j):
    l = list(range(8))
    if i <= j:
        assert dump(i, dump(j,l)) == dump(j+1, dump(i,l))
    else:
        assert dump(i, dump(j,l)) == dump(j, dump(i-1,l))
dump_swap()
```

# One Sided Inverses

It is known that you can add group annotations to a union find which sematically represent a group action. This let's you represent `g1(x) = g2(y)` and then solve for either `x` or `y`. `x = g1inv(g2(y))` or `y = g2inv(g1(x))`. This gives you a lot of flexibility.

It is sometimes mentioned that in fact you can derive that the left inverse is the same as the right inverse from the axioms of a group. You need the left and right identity to be distinct to not have this be the case.

In general, if we have a one-sided inverse relationship between `d` and `l`,  `d(l(X)) = X` then `p(X) = l(d(X))` is a projection operator in the sense it is idempotent. `p(p(X)) = l(d(l(d(X)))) = l(d(X)) = p(X)`

In the thinning union find post <https://www.philipzucker.com/thin_monus_uf/> , I led up to to thinnings by discussing positive offsest and integer factors. These operations do have one-sided inverses, saturating subtraction `x + n = y <->  x = y -. n` and floor division  `n * x = y <-> x = y // n`. To state that `x` is invariant under the "wrong way" composition `(x -. n) + n = x` is another way of stating that `x >= n` basically.

A related terminology to one-sided inverses is sections and retractions <https://ncatlab.org/nlab/show/retract>

Another related concept is that of the pseudo-inverse like the Moore-Penrose pseudo inverse <https://en.wikipedia.org/wiki/Moore%E2%80%93Penrose_inverse> .  This is a thing you can define for rectangular matrices, which cannot have both a left and right true inverse since the input and output vectors spaces are of differing dimensionality. If the matrix is full rank, then it is indeed a one-sided inverse.

# Lifting and Dumping in Knuth Bendix Completion

You can add equations for normalizing lift/dump operators to a knuth bendix complex and then some ground equations too. It seems to me like using an LPO seems appropriate and you want to have the lift and dump operators low in the order.

If you use atomic ground equations, you get a generalized union find.
If you use regular ground equations, you get a generalized congruence closure / egraph.

Likewise you can do the same for a group action.

There is something not quite desirable here with LPO in that I also fix the ordering of by constants `a`, `b`, `c`. This means the ordering will sometimes prefer `dump` and `lift` annotations on the right hand side of rules if it helps lower the constant. I'd prefer an ordering determined online that never has `dump` and `lift` appear on the right hand side, because this makes matching harder than a purely atomic right hand side.  

```python
%%file /tmp/liftdump.p

cnf(invinv, axiom, dump(lift(X)) = X).
cnf(ab, axiom, lift(a) = b).
cnf(bc, axiom, dump(b) = dump(c)).
cnf(ce, axiom, dump(c) = d).
```

    Writing /tmp/liftdump.p

eprover rulez. I love the new `--print-oriented-eqlits-as-rule` flag. I think I finally understand enough of the options to say that yes, this is an off the shelf fast knuth bendix engine.

```python
! eprover-ho -S -s -t LPO4 --precedence="d > c > b > a > lift > dump"  --print-oriented-eqlits-as-rules /tmp/liftdump.p
```

    % (lift_lambdas = 1, lambda_to_forall = 1,unroll_only_formulas = 1, sine = (null))
    
    % No proof found!
    % SZS status Satisfiable
    % Processed positive unit clauses:
    cnf(i_0_6, plain, (b->lift(a))).
    cnf(i_0_5, plain, (dump(lift(X1))->X1)).
    cnf(i_0_7, plain, (dump(c)->a)).
    cnf(i_0_8, plain, (d->a)).
    
    % Processed negative unit clauses:
    
    % Processed non-unit clauses:
    
    % Unprocessed positive unit clauses:
    
    % Unprocessed negative unit clauses:
    
    % Unprocessed non-unit clauses:
    
    

# Congruence Rules For Lifting and Dumping

Rudi has a nice way of presenting [slotted egraphs](https://dl.acm.org/doi/10.1145/3729326) as the regular congruence rules + a special renaming rule

```
t = s
-------------------
rename t = rename s
```

I have been thinking about different syntaxes for talking about the dump calculus. Every term implicitly has an arity associated to it. One could consider this arity as the type or as a kind of context. The claim is that any expression that uses variables should be careful in what context with what variables we are working in. Don't use `sin(x)`, instead use `x \mapsto sin(x)` which is a different thing from `x,y \mapsto sin(x)`.

The context is not a place where the term goes. The context (arity) _is_ a part of the term. The term does not make semantic sense with the context suppressed or forgotten.

lift has a congruence rule. It isn't that different from the congruence of other symbols except that it changes the context.

```
n |-> e1 = e2        n = cod(t)
------------------------------------ lift_cong
dom(t) |-> lift(t, e1) = lift(t, e2)
```

A curious rule is that we can push a lift into a dump. This is sort of a solving move. What this is implying is that if

```
cod(t) |->   e1  = lift(t, e2)
------------------------------- shift_lift
dom(t) |->   dump(t,e1) = e2
```

This isn't all though. We can also infer that for applying to `e1` , `lift . dump` is an identity (it usually isn't). This means that `e1` lives in the not destroyed subspace of the projection operator `lift . dump`

```
cod(t) |->   e1  = lift(t, e2)
------------------------------- proj_lift
cod(t) |->   lift(t,dump(t,e1)) = e1
```

We may or may not also require that you need to know `e1` is a lift of something before you can even know it is well formed to dump it. Sometimes this is a sensible, sometimes not. I often take the stance that the egraph is nice for representing partial functions or expressions with well formedness conditions, and the mere fact of being in the egraph is a way of noting that a term is well formed.

```
cod(t) |->  e1  = lift(t, e2)
------------------------------- dump_wf
dom(t) |-  dump(t,e1) 
```

There is also perhaps `dump_cong`

```
n |-> e1 = e2        n = dom(t)   [ dom(t) |-  dump(t,e1)     dom(t) |-  dump(t,e2)   optional]
------------------------------------------------------------ dump_cong
cod(t) |-> dump(t, e1) = dump(t, e2)
```

All of this shows up in the horrible problem `1 |-> x*lift(0) = lift(0)`. This is where the slotted e-graph has "redundancies" and something like the above congruence rules are what enables a normalizing union find to work. The number of "public slots" goes down, which here is noted by a field/analysis saying what `dumps` are allowed on an eid.

I sometimes like `|->` notation and sometimes `|-`. They trigger different parts of my brain. Much of my discussion of context and ideas are ultimately sourced from the semantics of type theory. Kind of I'm just ignoring / de-emphasizing the type part. In type theory, I've recently kind of realized that the "semantic" thing that goes in the semantic brackets is the _entire_ judgement, including the context `[[Gamma |- t : A]]` has the meaning of a function from Gamma variables to the set `A`, where `t` is the expression.  `[[t]]` doesn't even make any sense, nor does `[[t : A]]`. You always need at least an empty context.

# Bits and Bobbles

This is the latest in this series of blog posts:

- <https://www.philipzucker.com/thin_egraph/> Putting it all together as an egraph
- <https://www.philipzucker.com/thin_hash_cons_codebruijn/> making a co de bruijn hash cons based on thinnings
- <https://www.philipzucker.com/thin_monus_uf/> thinning union finds
- <https://www.philipzucker.com/thin1/> Discussing thinnings at all

Lift and dump combinators also work on dicts. Boolean dicts are kind of interesting. Relationship of lift/dump normal forms to bdds? An unused variable should get lifted away.

Thinnings are basically a semi-simplicial category. <https://en.wikipedia.org/wiki/Simplex_category> . It's interesting to consider actually representing the data of the category of cubes as some kind of bitvector mish mosh. <https://ncatlab.org/nlab/show/category+of+cubes> <https://amelia.how/posts/cubical-sets.html> These are probably also combinators for manipulating functions with distnguished endpoints (paths, proofs). Perhaps a cool way of internalizing proofs into egraphs?

Dumping is related to the slotted e-graph's notion of redundancy. The normal form of every expression is to be as thin as possible. This is nice because it achieves more sharing between different contexts.

Sometimes you learn for semantics reasons, like in `1 |- x*0 = 0`, that something that syntactically had some variables is thinner than you thought. You need to fix some things up with dumps in that case.

e-matching is still kind of confusing. Is it ok to just return a single solution or should more lift and dump searching be happening?
Does e-matching find the context needed or is a fixed context an input to the problem? `?n |- t = pat(?x,?y)` vs `n |- t = pat(?x, ?y)`. We can determine higher contexts in which a lifting is related to the query term t, but also we could return the dumped term.

The thinning egraph is baking in lift and dump. It kind of makes sense to make dump an enode. Kind of a skolem enode that represents that dumping is ok to do on that eid.

How exactly the push down of things that have been determined to be dumpable will work I'm a bit confused on. I guess rebuilding should do it without change?

I was also considering "partial thinnings" which are a pair of a thinning and a widening. This let's you describe ordered wires between ordered ports where neither input nor output have to be fully connected. It is analogous to an SVD decomposition and it's what you need to make thinnings pseudo invertible without changing their type.

We are trying to figure out how to have a rigid notion of variables added to equational logic. Equational logic already has variables in the form of universals `X`. The rigid variables are something else entirely.

|                |   Rigid  | Instantiable |
|----------------|----------|--------------|
| Backward Goal   | forall | exists         |
| Forward Theorem | exists | forall         |

Dump sounds like poop, so it is funny.

```python
def thin(i,l):
    return l[:i] + l[i+1:]

def dump(i,l):
    return l[:i] + ["junk"] + l[i:]

import hypothesis.strategies as st
from hypothesis import given

assert thin(1, thin(2,list(range(4)))) == thin(1, thin(1,list(range(4))))
assert thin(2, thin(1,list(range(4)))) == thin(2, thin(1,list(range(4))))

@given(st.integers(0,4), st.integers(0,4))
def thin_swap(i,j):
    l = list(range(8))
    if i < j:
        assert thin(i, thin(j,l)) == thin(j-1, thin(i,l))
    else:
        assert thin(i, thin(j,l)) == thin(j, thin(i+1,l))

thin_swap()
#thin(1, thin(0,list(range(5)))), thin(0, thin(2,list(range(5))))

@given(st.integers(0,4), st.integers(0,4))
def dump_swap(i,j):
    l = list(range(8))
    if i <= j:
        assert dump(i, dump(j,l)) == dump(j+1, dump(i,l))
    else:
        assert dump(i, dump(j,l)) == dump(j, dump(i-1,l))
dump_swap()
#l = list(range(8))
#dump(2, dump(6,l)), dump(7, dump(2,l))
#dump(4, dump(4,l)), dump(5, dump(4,l))
```

The labelled union find paper is interesting. I don't think they "derive" the group constraint. It becomes an assumption?

You are representing relations. So edge annotations could a priori have a meet and join
You have a constraint graph, but one can generate new nodes to allow solution? That seems to be required for

Looking at the labelled union find paper again. It's interesting that in the first bit, they discuss a more general picture of representing some relational domain on the edges. They talk about doing meet and join over these labels.  This is a pretty interesting perspective
You have a constraint graph that can be solved without losing information into a tree. Then somehow they derive (?) or assume the labels must form a group.
I think two ingredients that may not be being considered is

There can be new fresh  nodes inserted into the constraint graph if that helps solving it into a tree
There can be the self loop projectiony lattice-like thing at the root which relaxes the need for a unique label to be on the edges since all you  ever care about is edgelabel . selfloop not edgelabel alone. Rudi has commented that the edge labels are kind of just non unique representatives of a set of group elements. So it is perhaps useful not to consider the root lattice and edge label as independent but communicating things.
Philip Zucker: "By studying the conjunction of these two constraints (Section 4), we discover that our labeledunion-find data structure represents injective transformations between equivalence classes"
But maybe it only has to be injective in one direction, ie a section/retraction pair / one -sided inverse

```python
def args()
```

```python

def lift_dict(t : Thin, A : set, d : dict) -> dict:
    return {thin(t, k): v for k, v in d.items() if thin(t, k) in A}
```

 n : Int, m : Int, l : Int, A : Matrix(n,m) , B:Matrix(m,l) |-

```
 n |-  t = lift s
-------------- shift_thin
n-1 |- dump t = s

n |-  t = lift s
----------------- proj_lift
n |- lift dump t = t


----------- zero_wf
0 |- zero`


n |- t
------ lift_wf
n+1 |- lift t


n |- t = s
------------- lift_cong
n+1 |- lift t = lift s


n |- t = s
------------- bad rule? dump_cong. Does dumping need dignificatoin?
n-1 |- dump t = dump s

n |- s = lift t
---------------
n-1 |- dump s

lift_l  . lift_k = lift_{l . k}
```

Group uf in atomic ground knuth bendix terms has built in inv(inv()) laws. Any solved group presentation with a way of normalizing probably can be put in this

Rudi brought up a cool point about what tossing the right sided inverse thing into twee would look like. Completed atomic equations = union find. atomic equations + normalizing rewrite system = a generlized union find. I think actually have LPO makes for something that looks more like how a group union find does, because you can force the group stuff to be low in the order, so that the rules looke like a -> g(b) rather than g(a) -> b . Fiddling with the KBO weights probably won't do this.

There is some intuition that the order of symbols in LPO should follow something like "definition ordering" or call graph ordering. It does kind of feel right that if the group action symbols are very "primitive" they should be low in the ordering

```python
%%file /tmp/liftdump.p

% going up to 2-d
cnf(invinv, axiom, d10(l00(X)) = X).
cnf(invinv, axiom, d10(l1(X)) = X).
cnf(ab, axiom, l(a) = b).
cnf(bc, axiom, d(b) = d(c)).
cnf(ce, axiom, c = dump(d)).
```

```python
%%file /tmp/liftdump.p

cnf(invinv, axiom, dump(lift(X)) = X).
cnf(ab, axiom, lift(a) = b).
cnf(bc, axiom, dump(b) = dump(c)).
cnf(ce, axiom, dump(c) = d).

```

    Overwriting /tmp/liftdump.p

It seems like I want lift and dump less than a,b,c,d in order to pull it to the right.
Actual function symbols (enodes) should go to the left.

Hmm. dump(dump(d)) doesn't even type check. Ah, yes I put in something that doesn't type check.

hmm.
dump(c) -> d
... Hmm.
Maybe I'm wrong about lpo working.
Making the worst term better.

```python
! eprover-ho -S -s -t LPO4 --precedence="d > c > b > a > lift > dump"  --print-oriented-eqlits-as-rules /tmp/liftdump.p
```

    % (lift_lambdas = 1, lambda_to_forall = 1,unroll_only_formulas = 1, sine = (null))
    
    % No proof found!
    % SZS status Satisfiable
    % Processed positive unit clauses:
    cnf(i_0_6, plain, (b->lift(a))).
    cnf(i_0_5, plain, (dump(lift(X1))->X1)).
    cnf(i_0_7, plain, (dump(c)->a)).
    cnf(i_0_8, plain, (d->a)).
    
    % Processed negative unit clauses:
    
    % Processed non-unit clauses:
    
    % Unprocessed positive unit clauses:
    
    % Unprocessed negative unit clauses:
    
    % Unprocessed non-unit clauses:
    
    

```python
! eprover-ho -S -s -t LPO4 --precedence="a > b > c > d > dump > lift"  --print-oriented-eqlits-as-rules /tmp/liftdump.p
```

    % (lift_lambdas = 1, lambda_to_forall = 1,unroll_only_formulas = 1, sine = (null))
    
    % No proof found!
    % SZS status Satisfiable
    % Processed positive unit clauses:
    cnf(i_0_8, plain, (c->dump(d))).
    cnf(i_0_5, plain, (dump(lift(X1))->X1)).
    cnf(i_0_9, plain, (a->dump(dump(d)))).
    cnf(i_0_6, plain, (b->lift(dump(dump(d))))).
    
    % Processed negative unit clauses:
    
    % Processed non-unit clauses:
    
    % Unprocessed positive unit clauses:
    
    % Unprocessed negative unit clauses:
    
    % Unprocessed non-unit clauses:
    
    

```python
! eprover-ho -S -s -t LPO4 --precedence="lift > a > b > c > d > dump"  --print-oriented-eqlits-as-rules /tmp/liftdump.p
```

    % (lift_lambdas = 1, lambda_to_forall = 1,unroll_only_formulas = 1, sine = (null))
    
    % No proof found!
    % SZS status Satisfiable
    % Processed positive unit clauses:
    cnf(i_0_8, plain, (c->dump(d))).
    cnf(i_0_5, plain, (dump(lift(X1))->X1)).
    cnf(i_0_7, plain, (dump(b)->dump(dump(d)))).
    cnf(i_0_9, plain, (a->dump(dump(d)))).
    cnf(i_0_6, plain, (lift(dump(dump(d)))->b)).
    
    % Processed negative unit clauses:
    
    % Processed non-unit clauses:
    
    % Unprocessed positive unit clauses:
    
    % Unprocessed negative unit clauses:
    
    % Unprocessed non-unit clauses:
    
    

```python
! eprover-ho -S -s -t LPO4 --precedence="dump > a > b > c > d > lift"  --print-oriented-eqlits-as-rules /tmp/liftdump.p
```

    % (lift_lambdas = 1, lambda_to_forall = 1,unroll_only_formulas = 1, sine = (null))
    
    % No proof found!
    % SZS status Satisfiable
    % Processed positive unit clauses:
    cnf(i_0_8, plain, (dump(d)->c)).
    cnf(i_0_6, plain, (lift(a)->b)).
    cnf(i_0_5, plain, (dump(lift(X1))->X1)).
    cnf(i_0_9, plain, (dump(b)->a)).
    cnf(i_0_7, plain, (dump(c)->a)).
    
    % Processed negative unit clauses:
    
    % Processed non-unit clauses:
    
    % Unprocessed positive unit clauses:
    
    % Unprocessed negative unit clauses:
    
    % Unprocessed non-unit clauses:
    
    

```python
%%file /tmp/neguf.p

cnf(invinv, axiom, neg(neg(X)) = X).
cnf(ab, axiom, neg(a) = b).
cnf(bc, axiom, neg(b) = neg(c)).
cnf(ce, axiom, c = neg(d)).
%cnf(neg_a, negated_conjecture, true != false).

```

    Overwriting /tmp/neguf.p

```python
! eprover-ho  --silent --print-oriented-eqlits-as-rules  --term-ordering=LPO4 --precedence="a > b > c > d > neg" --print-saturated /tmp/neguf.p # --print-strategy
```

    % (lift_lambdas = 1, lambda_to_forall = 1,unroll_only_formulas = 1, sine = (null))
    
    % No proof found!
    % SZS status Satisfiable
    % Processed positive unit clauses:
    cnf(i_0_8, plain, (c->neg(d))).
    cnf(i_0_5, plain, (neg(neg(X1))->X1)).
    cnf(i_0_9, plain, (a->d)).
    cnf(i_0_10, plain, (b->neg(d))).
    
    % Processed negative unit clauses:
    
    % Processed non-unit clauses:
    
    % Unprocessed positive unit clauses:
    
    % Unprocessed negative unit clauses:
    
    % Unprocessed non-unit clauses:
    
    

```python
! eprover-ho -S -s -t LPO4 --precedence="a > b > c > d > neg"  --print-oriented-eqlits-as-rules /tmp/neguf.p
```

    % (lift_lambdas = 1, lambda_to_forall = 1,unroll_only_formulas = 1, sine = (null))
    
    % No proof found!
    % SZS status Satisfiable
    % Processed positive unit clauses:
    cnf(i_0_8, plain, (c->neg(d))).
    cnf(i_0_5, plain, (neg(neg(X1))->X1)).
    cnf(i_0_9, plain, (a->d)).
    cnf(i_0_10, plain, (b->neg(d))).
    
    % Processed negative unit clauses:
    
    % Processed non-unit clauses:
    
    % Unprocessed positive unit clauses:
    
    % Unprocessed negative unit clauses:
    
    % Unprocessed non-unit clauses:
    
    

```python
! twee /tmp/neguf.p --complete
```

    RESULT: Satisfiable (the axioms are consistent).

Ground contextual equational logic
Explicit lift moves.

Like Rudi's slotted explanation with renaming moves

```
     x,z |- t
----------------------
x,y,z |- lift(101, t)


G |- t1   G |- t2
-----------------
G |- app(t1,t2)


----------
v |- v


G |- t1=t2      G |- app(t1,t3)     G |- app(t2,t3)  
-------------------------------
    G |- app(t1, t3) = app(t2,t3)

and the other side

symm
refl

G |- t
------ refl
G |- t = t

G |- t1 = t2     lift(b,G) |- lift(b, t1)   lift(b,G) |- lift(b, t2)
--------------------------------------------------------------------
                 lift(G) |- lift(b, t1) = lift(b, t2)


v = ? seems like it shouldn't happen
Maybe a Sigma of known equations


Unnamed form

G |- t  judgement is that term t makes sense in at least scope G.


?G |- lhs(?x,?y) = rhs(?x,?y)


Pattern matching as a inference system akin to unification
What would ground knuth bendix look like in this system?


G |- t is kind of the strucutred eid


```

Try makoing the little congruence proof kernel

A big brain blast was the Bool is nothing on it's own
You need Gamma |- Bool.. Everything is a function, some things are 0-airty functions.
The thing that needs interpreting in DTT is the whole judgement
I wonder how this interacts with LFDTT?

Proof objects without going to DTT
groupoids and slotted?
G | - refl : t = t   is a judgement, not persay a typing judgement because I'm not so sure t=t should be consiered a type. The whole thing is unityped. Alyhough are refl the same thing as t?

equational logic with free variables. It's a different thing than pattern matching variables

Explicit weakening calculi
<https://hal.science/hal-00384683/document>  A lambda-calculus with explicit weakening and explicit
substitution
René David, Bruno Guillaume

<https://arxiv.org/abs/2412.03124> explicit weakening wadler

<https://arxiv.org/abs/1812.10008> Alpha-conversion for lambda terms with explicit weakenings
George Cherevichenko . This actually seems the closest to what I am doing

Draw egraph diagram with ports
draw thinning diagram with ports
Draw egraph in union find as dotted arrows style. Then union find is _also_ thin annotated. Solid color bands. Ordered Ports on the nodes.

Explicit thinnin rewrite rules

Many explicit lambda calculus don't batch the entire weaking into a single entity.

|              |   Rigid  | Instantiable
---------------------------------

Backward Goal   | forall | exists
--------------------------

Forward Theorem | exists | forall  

There is a missing box in equtional lgoic, this is prior to lambda calculus

priority queues.

```
        n |- lift_k(t1) = lift_l(t2)     m,k',l' = wct(k,l)
-----------------------------------------------------------
        m |- lift_k'(t1) = lift_l'(t2)
```

named weakening lift_{xy}( )
lift_{z - xy}  denote kept ones too?

```python
@dataclass
class App:
    f : str
    args : list[Term]

@dataclass
class Lift:
    thin : thin
    t : Term

@dataclass
class Var:
    pass
```

f:thin

What if we used a regular union find, but every constant had a thinning analysis attached to it of the thing it can be thinned to
It starts as

minctx stores a thinning instead of just a number.
No, I think the union find still needs.

union(f,g) / unode : semantics : bring to least common thinning by throwing junk into non shared arguments.
IF they don't agree, return junk

The sin, +, *, 0, 42, pi model.

G |- sin : n -> m

G |-
judgement we can derive a new weakest usable point for function foo.

minctx : Vec<Thin>

- uncontrolled union find that can have lowering edges.
We can learn how much it is acceptable to lower an id as a lattice

The unions may need to be between loweered versions of ids   low(t2,a) -t1> low(t3,b)  

This is the "groupification" of Thinning. +- offset doubling -> lower/raise thinning.

Is Raise . Lower = a pure lower or pure raise?

converse(Raise(t)) = Lower(t)

Id is really common anyway

project(thin, f)

sin is kind of size polymorphic yes or no. We don't ever refer to sin on it's own. [[sin]] isn't a thing we do.
[[n |- sin(t)]] is a thing we do
x,y |- sin(v)

I was a total mind blown thing the realize that the semantic entity is the full contextual judgement, not the
right hand side with some goofy gamma there for no reason.
[[Bool]] does not have to be a thing, but if it is it is defined to be [[[] |- Bool]]
[[ G |- Bool]] yea doesn't have to be true/false. Because it's functions, so duh.
[[ x:Bool |- Bool]] is more likely 1 of 4 possibilitys. But even then I'm not so sure.

Would `lift_(sin(lift_(v))) : R^n -> R`  be a better notation than `n |- sin(lift(...))`
But it's the "meta type" that I'm talking about.
R^n |- sin(x) : R

smart constructors makes add_term simple
It also makes pattern matching simple right? I'll just return in the context at the head.

Partial thinnings

If we want to have both windeings and hinnings in the saem category, when they compose they make projections.
These are howevever _ordered_ projections, where dumping still makes you shift one
type PThin = list[bool | None]
type InvThin = tuple[thin? : bool, PThin]
Widenings and thinnings aren't _invertible_.

We can think of them as matrices

another normal form might be U^T V, a wide thin pair, where we project into the SVD subspace kind of.
type InvThin = (Wide, Thin)

This is getting much closer to simplex category, which is non-strict and allows duplicates.
Also a perfectly reasonable combinator with a bit more expressive power.

Another persecptvie is to create the free combination of wide and thin,
but then note their action on identifiers which have projections of relevant variables. (a lattice)
We can the compress the lists of wide and thin into a single one.
This is a bit more subtle an idea.

The is all getting closer to kind of  C-semilattice kind of thing. as a generalization of G-semilattice.

sin((x-y)/sqrt(2)) is also a natural way to convert sin(x) to a higher dimensional function.
Rotations are a continuous form of permutations
Is there a continuous version of ordered maps? Some cone of rotations? Lower diagonal... ?

Baking in different

Subspaces of Lie groups / algebras. A rotationally symmetry function.

Something something noether

Multiplying by zero has nontrivial semantic behavior in regards to lift and junk/lower

junk_1(sin(v)) = sin(junk)
lower_1(sin(v)) = sin(junk)

lower_1(lift_0(42)) = 42
You can push junk through lift if it doesn't use it.

Category of pointed sets. A special junk value

Full simplex category also allows ordered duplication (or implements junk via duplication?), Fat points, fat edges (degenerate triangles)

Cubical category has a 0 default and 1 default

Simplex category has monoidal product. So does thinnings.

Proof trees. Lift combinators. cong_f(p1,p2,p3)
cong_app(p1,p2)
comp(p1,p2) = p_{l.m} ?
refl_t

equational proof trees has structural properties akin to lift/lower combinators.
Normal form uses as many cong as possible(?) or as few.

groupoid model of paths in a graph
Ports on vertices.
A 0 and 1 common connected src/dst?
Graphs in different contexts?

hypothetical eq proofs?
Proof functions that take in proofs?

Cody says the intersection property of contexts is kind of like interpolation. Huh. Many things are. The shared variables though.
That's interesting.

Mcbride coproduct and product. Maybe combining thinnings with the product and coproduct values?

coporudct analysis - a way of having abstractly defined lattices combined with concrete ones?

semi-simplicial category <https://ncatlab.org/nlab/show/semi-simplicial+set> delta sets
<https://en.wikipedia.org/wiki/Delta_set>

<https://algebraicjulia.github.io/CombinatorialSpaces.jl/dev/simplicial_sets/>

<https://arxiv.org/abs/0809.4221> elementary intro to simplical sets
Kan Complex - the horn condition. Filling in triangles... Hmm.

Rudi says store partial thinning as Map basically. a pair of ordered lists. or tuples of ordered lists. u8?
input : [1,2,3,4] # gaps are partiality. But then could be bitvec
output : [1,2,3,7] # gaps are also partiality?
n,m

Could be pair of bitvecs?
  [True, False, True, ...] lengh of n. True = nonpartial, not take
  [True, False, True]  length of m

  [true, false, true, true]
  [true, true, true] # if out is all true then this is just a regular thinning

  This can also be seen as thinning and widening.
  THinnings always were partial strict monotone maps? Now we just also allow gaps in output.

  Can  m > n? sure. why not? They do need to have the same number of True though.

  Swap them

Thin()
Wide()

Hmm. There might be a notion of composition that keeps the inner size? Like if I wanted to do mutable compose? Eh.

Garbage value interpretation vs repeating value

Thinnings are rectangular triangular 0-1 matrices.
Pthinnings allow all zero rows.

Thin, Wide is an SVD. U^T V

Dict vectors would allow named / slotted perspective.

Ordered user equalities ? User equalities are kind of alien. Opaque. They are ordered by time.
Prefer equations that come first for proof ordering?
Bake in administrative manipulations
lift_101(proof over 2)
p0 : a = b, p2 : b = c, p3 : c = d |- foo() : a = d
But namelessly refer to p0 etc. Huh. But I don't have that much problem making names for proofs...
Colored context? Anonymous hypothetical proofs

patterns are multibinders (lambda case as primitive construct?  
case()
)

lower / lift ---> shift(pthin, t)
The canonical form can be the lift of a lowering.

[True, False],[False, True]  is this possible? yes
comp(thin([True, False]), wide([False, True]))

meet(pt1,pt2)

join(pt1,pt2)

ordered graphs. Proof objects on ordered graphs as ordered lists. Ther

Perhaps using a adjoint dump gives us a way to talk in a limmited way about inequalities. f(a) = b -> f a <= b -> a <= g b

retracts and sections. One-sided inverse.
f(g(X)) = X

Particular groups have normal forms that are somewhat obvious.
Finitely presented groups can be encoded as a(b(X)) = . ainv(a(X)) = X  and a(ainv(X)) = X. Full right associated.
If we only care about ground systems otherwise, perhaps this can be specailized to a(ainv(groundt)) = groundt.

lift operators cut off at some upper limit?

A particular one-sided inverse system could have normal forms that are somewhat obvious.

In a shallow manner, lift destroys binding in current context. It is better said to be "thin" then.
Fiddling with your local env is kind of interesting. locals() ~ callcc() in terms of weirdness.

x = 7 is kind of let, it is dump / subst / wide. Pavel had a point about let being kind of the inverse of his other de bruijn opps. succ.

subst is a family of dump. Instead of a default value to dump with, we could dump with any value dump(x, a, e) = subst = papply(x, a, e). We can partially apply at spots other than the first

partial application -> partial evaluation?

modal type theory -> clocks and guards. Hm

Consider python dictionaries over bools. Then there is dump_true, dump_false

```python
def lift(n : int, d):
    return {**{ k[:n] + (True,)  +  k[n:] : v  for k,v in d.items()},
            **{ k[:n] + (False,) +  k[n:] : v  for k,v in d.items()}}


id = {(k,) : k for k in [True, False]}
thin(0, id)


def dumpt(n : int, f):
    return {k[:n] + k[n+1:] : v  for k,v in f.items() if k[n]}
def dumpf(n : int, f):
    return {k[:n] + k[n+1:] : v  for k,v in f.items() if not k[n]}

assert dumpt(0, thin(0, id)) == id
```

```python
def lift(n : int, f):
    return lambda *args: f(*(args[:n] + args[n+1:]))
def papply(n : int, x : object, f):
    return lambda *args: f(*(args[:n] + (x,) + args[n:]))

assert papply(1, 2, lambda a,b: a**b)(5) == 25 #  lam x, x ** 2
assert papply(0, 2, lambda a,b: a**b)(8) == 256 # lam x, 2 ** x

assert papply(1, 435, lift(1, lambda a: a))(3) == 3
assert papply(0, 435, lift(1, lambda a: a))(3) == 435
```

Widening are clumping of substitution / partial application operations. You don't _have_ to apply only at the first argument. From the persepctive of de bruijn indices, we don't always substitute in at db index 0.

If a widening hits a thinning, the thinning is kind of a free variable analysis, so we know we can stop substitution at that point.

(Thin, int) eid and explicit Dump/Wide node
Just try making them all nodes? but search for dump/dump, thin/dump, dump/thin, thin/thin patterns

Maybe the least exotic thing would just make a built in sort for thin and wide with the appropriate built in functions.
Widenings _can_ contain eids, sure. Container rebuilding.

I don't think a pattern would ever explicitly look for substitution operations (?) which makes it different from AC. Looking for a subst would convert it into higher order matching? Looking for a thin is kind of more like miller matching

```python
# widening a sublist requires a list requires us to know what to put in
type Wide = list[object | None]

def wide(w : Wide, l : list) -> list:
    res = []
    i = 0
    for x in w:
        if x is None:
            res.append(l[i])
            i += 1
        else:
            res.append(x)
    return res


assert wide([None, None, None], [1,2,3]) == [1,2,3]
assert wide([None, 0, None], [1,3]) == [1,0,3]
assert wide([0, None, None], [2,3]) == [0,2,3]
assert wide([0, None, 0], [2]) == [0,2,0]
```

The one-sided inverse picture.

add_7 ssub_7 aturating substition
x + 7 - 7 = x  <-> x >= 7 if saturating subst
Likewise for multiplication and floor division

x - 7 = 0 <-> x <= 7   -- this is related to galois connection of sat sub.

Or we could switch into partial functions if we don't like the arbitrariness of floor / saturation. They _aren't_ arbitrary in the sense they give us galois connections.

g f x = x  <->  g f x <= x, g f x >= x  <->

Connections between tree-like partial orders and one-sided inverses?

restriction categories?

Galois connections. If we take the analysis as primary.  anal(x) = l. in egglog analysis are the results of "regular" functions that merge by meet. Abstract eid lattices? Using the value union find?
anal2(x) = k
k and l could be related by a galois connection.
A functor is of form `q /\ _`? That functor also has meet structure.
Could this be a way to view equality as a kind of lattice analysis? It's not _just_ galois, it's a two way galois
This is crazy talk

if we could pick a default value per sort
0 |- dump(1 |- v) = 435

1 = |- lift(subst(x, 435, x*0)) == x* 0 = lift(0)

So we actually have a theory of a distinguished substitution.

[true, false]  [Some(42). None, ]  # none correspond to old "true"

lift(0, subst(0, 42, e))

substitution and lifting can be coalesced. A coalesced substitution is kind of similar to an env

So the widening is kind of a lattice analysis of Known/Unknown pieces of environment.... kind of, but not really.

dump felt arbitrary was the problem.
The adjoint definitions of dump remove arbitrariness, but are harder to implement. They give inequality processing in addition to one-sided inverse processing.

```python

```

```python
import inspect
def lift(x, e):
    stack = inspect.stack()
    if len(stack) > 2:
        caller_frame = stack[2]
        frame = caller_frame.frame
        del frame[x]
    return e # yea, but e is already evaluated so this doesn't work
"""
lift("x", x) should fail 
lift("x", 3) ok. 3 is evaluated in smaller context.
"""

locals()

def lift(x):
    stack = inspect.stack()
    if len(stack) > 1:
        caller_frame = stack[1]
        frame = caller_frame.frame
        del frame.f_locals[x]
thin = lift

x = 3 # read as let
thin("x")
x

"""
let x = 3 in
let () = lift("x") in
x
"""
```

    ---------------------------------------------------------------------------

    NameError                                 Traceback (most recent call last)

    Cell In[141], line 26
         24 x = 3 # read as let
         25 thin("x")
    ---> 26 x
         28 """
         29 let x = 3 in
         30 let () = lift("x") in
         31 x
         32 """


    NameError: name 'x' is not defined

```python
def thin(i,l):
    return l[:i] + l[i+1:]

def dump(i,l):
    return l[:i] + ["junk"] + l[i:]

import hypothesis.strategies as st
from hypothesis import given

assert thin(1, thin(2,list(range(4)))) == thin(1, thin(1,list(range(4))))
assert thin(2, thin(1,list(range(4)))) == thin(2, thin(1,list(range(4))))

@given(st.integers(0,4), st.integers(0,4))
def thin_swap(i,j):
    l = list(range(8))
    if i < j:
        assert thin(i, thin(j,l)) == thin(j-1, thin(i,l))
    else:
        assert thin(i, thin(j,l)) == thin(j, thin(i+1,l))

thin_swap()
#thin(1, thin(0,list(range(5)))), thin(0, thin(2,list(range(5))))

@given(st.integers(0,4), st.integers(0,4))
def dump_swap(i,j):
    l = list(range(8))
    if i <= j:
        assert dump(i, dump(j,l)) == dump(j+1, dump(i,l))
    else:
        assert dump(i, dump(j,l)) == dump(j, dump(i-1,l))
dump_swap()
#l = list(range(8))
#dump(2, dump(6,l)), dump(7, dump(2,l))
#dump(4, dump(4,l)), dump(5, dump(4,l))
```

```python
def thin(n,i,l):
    assert len(l) == n+1
    return l[:i] + l[i+1:]

def dump(n,i,l):
    assert len(l) == n-1
    return l[:i] + ["junk"] + l[i:]

import hypothesis.strategies as st
from hypothesis import given

@given
thinthin(3,2,[0,1,2,3])
```

    [0, 1, 3]

```python
class UF():
    uf  :


```

maybe rudi's right and the index form is much easier to think about

```python
def comp(a,b):
    ta, wa = a
    tb, wb = b
    for 
```

```python
def comp(a, b):
    ta,wa = a
    tb,wb = b
    tout = []
    j = 0
    for i in ta:
        if i:
            while not wa[j]:
                j += 1
            tout.append(tb[j])
            j += 1



```

```python
type Thin = list[bool]
type Wide = list[bool]
type PThin = tuple[Thin, Wide]

def comp(pt1, pt2):
    #assert len([i for i in t1 if i]) == len([i for in w1 if i])
    assert valid(pt1)
    assert valid(pt2)
    assert cod(pt1) == dom(pt2)
    i,j = 0,0
    t1,w1 = pt1
    t2,w2 = pt2
    to, wo = [],[]
    for b in t1:
        print(i, j, to, wo)
        print(t2,w1,w2)
        if i >= len(t2) or i >= len(w1) or j >= len(w2):
            print("breal")
            break
        else:
            c = b and w1[i] and t2[i] and w2[j] # strand makes it through
            to.append(c)
            if t2[i]:
                wo.append(c)
                j += 1
            i += b
    while len(to) < len(t1):
        to.append(False)
    while len(wo) < len(w2):
        wo.append(False)
    assert sum(to) == sum(wo) # number of trues should match
    return (to, wo)

def valid(pt):
    return sum(pt[0]) == sum(pt[1])
def id(n):
    return ([True]*n, [True]*n)
def thin(t):
    return (t, [True]*sum(t))
def wide(w):
    return ([True]*sum(w), w)
def dom(pt):
    return len(pt[0])
def cod(pt):
    return len(pt[1])
def pinv(pt):
    return (pt[1], pt[0])
def proj(p):
    return (p, p)
assert comp(id(2), id(2)) == id(2)
assert thin([True, False]) == ([True, False], [True])
assert comp(id(2), thin([True, False])) == thin([True, False])
assert comp(thin([True, False]), id(1)) == thin([True, False])
assert comp(wide([True, False]), id(2)) == wide([True, False])
assert comp(id(1), wide([True, False])) == wide([True, False])
assert comp(wide([True, False]), pinv(wide([True, False]))) == id(1)
assert comp(pinv(thin([True, False])), thin([True, False])) == id(1)
assert comp(thin([True, False]), pinv(thin([True, False]))) == proj([True, False])
assert comp(proj([True, False]), proj([False, True])) == proj([False, False])

# is ([True, False], [False, True]) possible?


```

    0 0 [] []
    [True, True] [True, True] [True, True]
    1 1 [True] [True]
    [True, True] [True, True] [True, True]
    0 0 [] []
    [True, False] [True, True] [True]
    1 1 [True] [True]
    [True, False] [True, True] [True]
    breal
    0 0 [] []
    [True] [True] [True]
    1 1 [True] [True]
    [True] [True] [True]
    breal
    0 0 [] []
    [True, True] [True, False] [True, True]
    0 0 [] []
    [True] [True] [True, False]
    0 0 [] []
    [True, False] [True, False] [True]
    0 0 [] []
    [True, False] [True, False] [True]
    0 0 [] []
    [True] [True] [True, False]
    1 1 [True] [True]
    [True] [True] [True, False]
    breal
    0 0 [] []
    [False, True] [True, False] [False, True]
    1 0 [False] []
    [False, True] [True, False] [False, True]

```python
def comp(pt1, pt2):
    t1, w1 = pt1
    t2, w2 = pt2
    assert len(w1) == len(t2)

    i = 0   # index into w1 / t2
    j = 0   # index into w2
    tout = []
    wout = []

    for b in t1:
        if not b:
            tout.append(False)
            continue

        c = w1[i] and t2[i] and w2[j] # makes it through?
        tout.append(c)

        if t2[i]:
            wout.append(c)
            j += 1

        i += 1

    wout.extend([False] * (len(w2) - len(wout)))
    return tout, wout
assert comp(id(2), id(2)) == id(2)
assert thin([True, False]) == ([True, False], [True])
assert comp(id(2), thin([True, False])) == thin([True, False])
assert comp(thin([True, False]), id(1)) == thin([True, False])
assert comp(wide([True, False]), id(2)) == wide([True, False])
assert comp(id(1), wide([True, False])) == wide([True, False])
```

```python
def comp(left_pt, right_pt):
    left_t, left_w = left_pt
    right_t, right_w = right_pt
    assert len(left_w) == len(right_t)

    input_ix = 0
    output_ix = 0
    t_out = []
    w_out = []

    for live in left_t:
        if not live:
            t_out.append(False)
            continue

        survives = left_w[input_ix] and right_t[input_ix] and right_w[output_ix]
        t_out.append(survives)

        if right_t[input_ix]:
            w_out.append(survives)
            output_ix += 1

        input_ix += 1

    w_out.extend([False] * (len(right_w) - len(w_out)))
    return t_out, w_out

```

```python
def comp(pt1, pt2):
    assert len([i for i in t1 if i]) == len([i for in w1 if i])
    i1,j1,i2,j2= (0,0,0,0)
    t1,w1 = pt1
    t2,w2 =pt2
    to, wo = [],[]
    for b in t1:
        c = b and w1[i] and t2[i] and w2[j] # strand makes it through
        to.append(c)
        i += b
        j += t2[i]
    while j < len(w2):
        j += 1
        wo.append(False)

    return (t0, w0)



    for b in w2:

 #if t2[i]:
        #    j += 1
        #    wo.append(c)
        #if b:
        #    i += 1
    #for b in w2:
    #    c = b and w[i] and t2[i] and t1[j]



```

```python
Thin { inputs : Vec<bool>, outputs : Vec<bool>}

id(n) = ([True]*n, [True]*n)
comp(f,g) = ...


```

```python
def path_lift(p, f):
def path_proj(p, f):
```

```python
enum Thin {
    Id,
    Lower(Thin0/Vec<Bool>),
    Raise(Thin0)
}
```

```python

```
