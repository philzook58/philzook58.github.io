---
date: 2025-09-15
title: A Slotted Hash Cons for Alpha Invariance
---

Slotted e-graphs <https://dl.acm.org/doi/10.1145/3729326> are a data structure that compactly stores many equivalent terms in an alpha invariant aware way. I've been very excited by them but also very confused by them.

There is a useful concept pump going in the different ways between [union finds, hash conses and e-graphs](https://www.philipzucker.com/egraph-1/).

- Union Find + Hash Cons ---> E-Graph
- E-Graph - Compound Terms ---> Union Find
- E-Graph - Equality Assertion ---> Hash Cons

There are sometimes existing versions of fancy e-graphs, fancy union find, and fancy hash conses for which the other counterparts is not discussed or kept implicit. For the slotted e-graph, there must surely be a slotted union find and a slotted hash cons simplification should you choose to not use those capabilities.

I do think I somewhat understand a story about how one might arrive at a Slotted Hash Cons as a solution to a variant of the hashing modulo alpha problem.

- <https://arxiv.org/abs/2105.02856> Hashing Modulo Alpha-Equivalence
- <https://arxiv.org/abs/2401.02948> Hashing Modulo Context-Sensitive α-Equivalence

Basically, it is easy to normalize terms with alpha variables in them by labelling them by a traversal. This is non compositional and requires resweeping when you build new terms out of old ones, which sucks for hash consing. By lazily retaining the permutations required when something becomes a subterm (the variables order in the traversal changes), you can get something compositional that does not require resweeping the subterms.

# Beta vs Alpha

Alpha invariance is noting that the actual names of variables don't matter in some (usually subtle) sense.

People have a tendency to go right for lambda and [beta normalization](https://en.wikipedia.org/wiki/Lambda_calculus#%CE%B2-reduction) (beta is substituting into the body of a lambda), but this is a curse. Lambda is the Ultimate Pain in the Ass (LUPITA). There is a design philosophy that suggests that baking in full beta reduction into some automated reasoning systems is too much to ask. The canonical thing I have in mind is [higher order unification](https://en.wikipedia.org/wiki/Unification_(computer_science)#Higher-order_unification), for which the full beta normalizing higher order unification is undecidable (although not that bad in practice so I dunno).

Two restricted variations of higher order unification that are decidable and in fact fast are:

- Miller/Beta0/"higher order pattern" Unification
- Nominal Unification

These restrictions more or less deal with a notion of unification modulo alpha equivalence.

There is also something to note that a distinction can be made between "scoped" alpha invariance (like lambda terms mod alpha) and "unscoped" alpha invariance (like resolution clauses or einstein notation).

If you introduce an ordered binder for your alpha invariant variables, canonizing these terms is easy by examining the binding site. Just label the variables according to the order they show up in the binder. `canon(a [x,y,z]. f(x,y,z)) =  a [v0,v1,v2]. f(v0,v1,v2) = canon(a [p,q,r]. f(p,q,r))`

Another way perhaps of distinguishing these two concepts is to consider ordered multi-arity binders  `a [x,y,z]. f(x,y,z)` vs a set-like multi-arity binder. `a {x,y,z}. f(x,y,z)`. The set-like character makes it a priori hard to figure out how to number your variables and you need to traverse into the term to tie break them, since the variables can have no structure in and of themselves without breaking alpha invariance. A "binderless" alpha invariant term could be seen as a implicit set-like binding at the top of the term. `f(x,y,z) ~> a {x,y,z}. f(x,y,z)`  

I would claim that free variables as they show up in the locally nameless technique are binderless / set-bound because you kind of want a set like implicit variable environment. Likewise as they show up in einstein notation, resolution clauses, and prolog terms.

# Normalizing Alpha Terms

<https://www.philipzucker.com/hashing-modulo/> One method to hash something modulo a theory is to have a method for building a structurally canonical form and then hash that using regular structural hashing. For example, hashing a set of integers as represented by non canonical AVL trees or red-black trees (many AVL trees represent can represent the same underlying set) can be achieved by turning the set into a deduplicated sorted list or a trie. This is not the only possible method.

In prolog and automated reasoning, there are mechanisms for storing terms with variables such that "variants" are deduplicated or seen as equal <https://www.swi-prolog.org/pldoc/man?section=tabling-subsumptive> <https://www.swi-prolog.org/pldoc/man?predicate=%3D@%3D/2>

It is actually easy to find an alpha canonical form. Just pick any deterministic method to traverse the tree and number variables as you find them. A preorder traversal works. `f(v0, g(v1, v0))`. This is what the prolog predicate `numbervars` does <https://www.swi-prolog.org/pldoc/man?predicate=numbervars/3>

```python
! swipl -g "T = f(X,g(Y,X)), numbervars(T,0,_), write_canonical(T), halt."
```

    f('$VAR'(0),g('$VAR'(1),'$VAR'(0)))

We can do it ourselves on a simple tuple based ast. It's not so complicated.

User facing names (a string like `"X"` let's say) and the canonical variables ids (an int) are completely different types and should be represented by different constructors.

Canonization converts a term with user names to an alpha equivalent shape term and a mapping from user names to canon ids.

Here `term` is a non normalized thing that contains user names, but `shape` is a similar thing that only contains int ids. `alpha_canon` converts between the two and also returns a `rename` dictionary of evidence as to how the substitution was done. We can completely reconstruct any alpha non invariant `term` from the `cterm` which is a tuple of the renaming and the shape. The two types are isomorphic to each other.

```python
type term =  tuple["uvar", str] | tuple[str, term, ...] # not proper python type syntax but whatever
# smart constructors
def var(s : str) -> term:
    return ("uvar", s)
def app(f : str, *args : term) -> term:
    return (f, *args)
from typing import Literal
type rename = dict[str, int]  # user variable renaming to ids
type shape = tuple[Literal["cvar"], int] | tuple[str, shape, ...]
type cterm = tuple[rename, shape]
def alpha_canon(t : term) -> cterm:
    env = {}
    def worker(t):
        match t:
            case ("uvar", x):
                if x not in env:
                    env[x] = len(env)
                return ("cvar", env[x])
            case (f, *args):
                return (f, *map(worker, args))
            case _:
                raise ValueError("ill formed", t)
    return env, worker(t)
f = lambda *args: app("f", *args)
g = lambda *args: app("g", *args)
X,Y,Z,P,Q = var("X"), var("Y"), var("Z"), var("P"), var("Q")

alpha_canon(f(X, g(Y, X)))
```

    ({'X': 0, 'Y': 1}, ('f', ('cvar', 0), ('g', ('cvar', 1), ('cvar', 0))))

Two alpha equivalent terms are not structurally equal

```python
f(X, g(Y, X)) == f(P, g(Q, P))
```

    False

But their canonized forms are

```python
alpha_canon(f(X,g(Y,X)))[1] == alpha_canon(f(P, g(Q, P)))[1] 
```

    True

Exhibiting the isomorphism. `to_term` is the inverse of `alpha_canon`

```python
def to_term(t : cterm) -> term:
    rename, shape = t
    env = {n : x for x,n in rename.items()}
    def worker(t):
        match t:
            case ("cvar", n):
                return var(env[n])
            case (f, *args):
                return app(f, *map(worker, args))
            case _:
                raise ValueError("ill formed", t)
    return worker(shape)

to_term(alpha_canon(f(X, g(Y, X))))
```

    ('f', ('uvar', 'X'), ('g', ('uvar', 'Y'), ('uvar', 'X')))

# Hash Consing

The issue with hash consing these is that this variable ordering method can't be compositional. When a previously hash consed term is used as an argument of another term, a sweep from the top of this new turn may change the canonical numbering of the variables. You can sweep then term again and reintern but this kind of stinks.

We can fix this problem in the slotted style by adding an [indirection](https://en.wikipedia.org/wiki/Fundamental_theorem_of_software_engineering
). In between every parent and it's subterms we can retain a permutation of ids that you'll need to recollect when you traverse down into a canonized term.
Instead of eagerly permuting the ids, we keep a note at the term to lazily do this permutation.

You don't _really_ need to traverse into the term. You already know the order you will find the variables. It's been done. It's in the renaming map.

So instead of traversing the subterms, we can just traverse the renaming maps in order. We'll find some permutation of canonical ids that would need to be applied to each argument. This is a canonical permutation applied to a canonical shape. We don't actually need to eagerly do it either. We can just note the permutation at that node of the shape to lazily apply later. In this manner, variables still have a cost, but it is proportional to the number of variables in play rather than the size of the subterms.

It may be desirable to also compress this permutation representation and only store the things that need to be changed. A more memory efficient version would not note `v0 -> v0` for example

```python
table = {}
def hashcons(x : tuple[...]) -> tuple[...]:
    """
    hashcons returns the actual memory of a canonical tuple assuming that all subterms have already been hashconsed.
    Now one can use `is` to compare canonical terms for equality, which is pointer equality and fast.
    """
    assert isinstance(x, tuple)
    key = tuple(id(t) if isinstance(t, tuple) else t for t in x) # avoids recursion into inner tuples during hashing and equality check internal to table.get
    res = table.get(key)
    if res is None:
        table[key] = x
        return x
    return res

type rename = dict[str, int]  # user variable renaming to ids
type perm = tuple[tuple[int,int], ...] # permutation of variable ids as a sorted tuple of pairs
type shape = tuple["cvar", int] | tuple[str, pshape, ...] 
type pshape = tuple[perm, shape] # pshape is an argument 
type cterm = tuple[rename, tuple[str, pshape, ...]]
def var(s : str) -> cterm:
    return ({s : 0}, hashcons(("cvar", 0)))
def app(f : str, *args : cterm) -> cterm:
    # kind of folded pieces of alpha_canon in here
    env = {}
    cargs = []
    # Go through arguments in order and figure out new toplevel renaming
    for rename, shape in args:
        perm = {}
        for x,i in sorted(rename.items(), key=lambda x: x[1]): # do in traversal order, i increasing
            if x not in env:
                env[x] = len(env)
            perm[i] = env[x]
        # canonize and hashcons the permutation as a list
        # perm should already be sorted, but just in case let's do it again.
        cperm = hashcons(tuple(hashcons((i,j)) for i,j in sorted(perm.items())))
        cargs.append(hashcons((cperm, shape)))
    return env, hashcons((f, *cargs))

app("f", var("X"), var("Y"), var("X"))
f = lambda *args: app("f", *args)
g = lambda *args: app("g", *args)
X,Y,Z = var("X"), var("Y"), var("Z")

assert f(X, g(Y, X))[1] is f(Z, g(Y, Z))[1]
assert f(X, g(Y, X))[1] is not f(X, g(X, X))[1]

f(X, g(Y, X))
```

    ({'X': 0, 'Y': 1},
     ('f',
      (((0, 0),), ('cvar', 0)),
      (((0, 1), (1, 0)),
       ('g', (((0, 0),), ('cvar', 0)), (((0, 1),), ('cvar', 0))))))

To traverse back down the term, really you want a kind of view into it where you collect up the lazy permutations as you go along. The function [`unapply`](https://stackoverflow.com/questions/18468786/understand-how-to-use-apply-and-unapply) does this. `unapply` and `app` are basically inverses.

```python
def unapply(t : cterm) -> tuple[str, cterm, ...]:
    rename, (f, *pshapes) = t
    args = [({ x : dict(perm).get(i,i)  for x,i in rename.items()}, shape) for perm,shape in pshapes]
    return (f, *args)
unapply(f(X, g(Y,X)))
```

    ('f',
     ({'X': 0, 'Y': 1}, ('cvar', 0)),
     ({'X': 1, 'Y': 0}, ('g', (((0, 0),), ('cvar', 0)), (((0, 1),), ('cvar', 0)))))

```python
g(Y,X)
```

    ({'Y': 0, 'X': 1}, ('g', (((0, 0),), ('cvar', 0)), (((0, 1),), ('cvar', 0))))

# Bits and Bobbles

If I went whole hog on unapply, maybe python pattern matching could be overloaded to work?

In a subtle way, what I have described solves a different problem than the hashing mod alpha papers.
Variables never "go away" like they do for de bruijn indices. They aren't intrinsically scoped. I don';t have a mechanism to trnalsate between free and scoped vars like in locally nameless. There may be a way to fix this. Slotted egraphs seems to have this capability.

Tensor canonicalization <https://www.philipzucker.com/canon_search/> <https://www.stephendiehl.com/posts/tensor_canonicalization_rust/> is very much related to the slotted egraph in my opinion.

Is perm really usefully thought of as a permutation? Or is it just an invertible id to id mapping. Tomato tamato maybe.

You want to hash cons shapes, not names. names are ephemeral kind of. They exist and are important for local use but ultimately go away. This is the story i told in egraphs modulo theories <https://arxiv.org/abs/2504.14340> . For some use cases you don't want to hash cons polynomials. You want to hash cons the variables of the polynomials.

Slotted hash cons
Atomic slotted knuth bendix

foo(x,y) = bar(x)

f(x,y) != foo(z,w)   this is not the case.

It really does come from a naively named persepctive.

Multiarity by keyword lambdas.

hmmm groupoid rename is neater than perm because I don't need to double everything.

We relly are talking about names
names = slots?

Alpha cnaonization

Traversal can go any direction

<https://en.wikipedia.org/wiki/Coxeter_group>

<https://www.cl.cam.ac.uk/~amp12/papers/nomlfo/nomlfo-draft.pdf> swappings to permutation (gi gi+1)**3 = 1
(a a') (b b') =

symmettry classes
symmettry nodes

A new kind of indrection?

Bottom up ematching is also nondet if we have symmettries? If the structured eids are themselves sets is that a problem? So seid isn't renamed eid maybe it's more like renamed _symmettry group set_

invariance of e-nodes to symmettries

f(t,t1) = f(t - t1)
f(x) = f(|x|)

covariance
v(Rx) = Rv(x)

Succ() Pred() V
swap(x, body)  # permute what is at 0 on "stack" with what is at named location x.
<https://pavpanchekha.com/blog/egg-bindings.html> He points out let as a quais inverse to succ. That's intriguing.

hash cons modulo symmettries?
i + j  and j + i should hash to same thing.
Still no egraph which is nice.
hash cons mod alpha vs hash cons mod symmetry vs both.
i + i + j considered as flat node
v0 + v0 + v1
or
v1 + v1 + v0
"slot" permuations vs name permutations. This was the thing in tensor canonization.
canonization by search while you're hash consing.

Slotted union find ~ tensor monomial canonization

```python
type rename = dict[str, int]  # user variable renaming to ids
type perm = tuple[tuple[int,int], ...] # permutation of variable ids as a sorted tuple of pairs
type shape = tuple["cvar"] | tuple[str, tuple[perm, shape], ...] 
type cterm = tuple[rename, tuple[str, shape, ...]]
```

```python
import functools

@functools.cache
def hashcons(x):
    # hashing does a traversal, which is not ideal. But it does give us object identity
    return x
```

```python
# hmm I need perm hashconsed too. That's annoying
table = {}
def hashcons(x : tuple[...]) -> tuple[...]:
    assert isinstance(x, tuple)
    key = tuple(id(t) if isinstance(t, tuple) else t for t in x)
    res = table.get(key)
    if res is None:
        table[key] = x
        return x
    return res

x = hashcons(("cvar", (1,)))
y = hashcons(("cvar", (1,)))
assert x is not y
#hashcons(("cvar", (1,))) is hashcons(("cvar", (1,)))
x = hashcons(("cvar", hashcons((1,))))
y = hashcons(("cvar", hashcons((1,))))
assert x is y

type perm = dict[int, int]  # permutation of ids

```

## Slotted Union Find aka Monomial Tensor Knuth Bendix

`a(i,j) = b(j)`
`a(i,j) = a(j,i)`
`a(j,j) = b(j)`
`a(i,j) = c(j,i)`

a compact

equlity is symmettricand set like

`{a(i,j), b(j)}` canonize this set.

It's very evocative of superposition / knuth bendix, but variables aren't Unification variables. They are rigid. ??? Is that true?

Maybe I don't want to canonize atoms out of context of the equality. There is almost no point? If we fuse the two renamings, we get a permutation

The group/groupoid union find

inequality union find
arguably maybe only one direction should be allow? Eh. Nah
a(i,j) -> b(j)

def union()

We need to look up the canonical form of the atom

subsumptive matching.
subsumptive uf = Inequality union find + variant union find

There is an implicit up set in terms of all narrowings.

```python
type uatom = tuple[str, names, ...]
type shape = tuple[str, int, ...]
type catom = tuple[rename, shape]
def unname(uatom) -> catom:
    env = {}
    inds = []
    for x in uatom[1:]:
        if x not in env:
            env[x] = len(env)
        inds.append(env[x])
    return env, (uatom[0], *inds)
def to_atom(catom) -> uatom:
    rename, shape = catom
    env = {n : x for x,n in rename.items()}
    names = [env[i] for i in shape[1:]]
    return (shape[0], *names)


uf = {}
def find(x : uatom) -> catom:
    rename, shape = unname(x)
    while shape in uf:
        perm, shape = uf[shape]
        rename = {k : perm[v] for k,v in rename.items() if v in perm}
    return to_atom((rename, shape))

def union(x : uatom, y : uatom):
    x = find(x)
    y = find(y)
    if x != y:
        rx, sx = unname(x)
        ry, sy = unname(y)


    



```

```python

```

```python
def fuse(rename1, rename2): # a join basically? No. This sucks and is wrong
    return {k : rename2[v] for k,v in rename1.items() if v in rename2}

```

```python
# consider the equality relation
eq = [(1,2), (1,2), (2,1), (2,1)] # silly yea?
set(eq) # better
{tuple(sorted(ab)) for ab in eq} # better yeah?

```

```python
type shape = tuple[str, tuple[int, ...]]
type uind = str
def atom(name : str, *args : uind) -> shape:
    rename = {n : i for i,n in reversed(enumerate(args))}
    return rename, (name, tuple(rename[arg] for arg in args))

```

```python

```

```python
class SlottedUF():
    
```

```python
swap(x,y,t) == swap(y,x,t)
swap(x,y,swap(x,y,t)) == t
swap(x,y,swap(v,w,t)) == swap(v,w,swap(x,y,t)) if x != v and x != w and y != v and y != w
swap(x,y,var(x)) == var(y)
swap(x,y,var(w)) == var(w) if w != x and w != y
swap(x,y,f(t)) == f(swap(x,y,t)) # for all function symbols f
# and maybe there's some interesting equation on a shred var? 
# swap(x,y, swap(y,z,t)) == swap(?)

```

```python
[1,2,3].index(2)
```

    1

```python
def alpha_canon(t):
    env = []
    def worker(t):
        match t:
            case ("var", n):
                if n in env:
                    return ("var", env.index(n))
                else:
                    env.append(n)
                    return ("var", len(env) - 1)
            case (f, *args):
                return (f, *map(worker, args))
            case _:
                raise ValueError("ill formed", t)
    return env, worker(t)
def var(n): return ("var", n)
def add(x,y): return ("add", x, y)
alpha_canon(add(var("x"), var("y")))


```

    (['x', 'y'], ('add', ('var', 0), ('var', 1)))

```python
def reconcile(env1, env2):
    env = env1.copy()
    fiddle = []
    for n,x in enumerate(env2):
        if x in env:
            fiddle.append(env.index(x))
        else:
            env.append(x)
            fiddle.append(len(env) - 1)
    return env, fiddle

reconcile(["x", "y"], ["y", "x"])

def reconcile(envs):
    totenv = []
    fiddles = [] # shapes?
    for env in envs:
        fiddle = []
        for x in env:
            if x in totenv:
                fiddle.append(totenv.index(x))
            else:
                totenv.append(x)
                fiddle.append(len(totenv) - 1)
        fiddles.append(fiddle)
    return totenv, fiddles


reconcile([["x", "y"], ["y", "x"], ["z", "x"]])



```

    (['x', 'y', 'z'], [[0, 1], [1, 0], [2, 0]])

```python
def alpha_canon(t):
    def worker(t):
        match t:
            case ("var", n):
                return  [n], ("var",0)
            case (f, *args):
                envs, args = zip(*map(worker, args))
                totenv, fiddles = reconcile(envs)
                return  totenv, (f, *zip(fiddles, args))
    return worker(t)

env, shape = alpha_canon(add(var("y"), add(var("x"), var("y"))))
env, shape1 = alpha_canon(add(var("z"), add(var("q"), var("z"))))
shape == shape1
```

    True

```python
def inv(perm):
    res = [0]*len(perm)
    for n,i in enumerate(perm):
        res[i] = n
    return res

def comp(p1,p2):
    
```

```python
class EGraph():
    def __init__(self):
        self.uf = []
        self.enodes = {}
```

Renaming knuth bendix. Whats the ordering?

```python
class UF():
    def __init__(self):
        self.uf = []
        self.perm = []
    def find(self, x):
        rename, e = x
        while self.uf[e] == e:

        rename *  

    #def union(self, x, y):

```

```python
type rename_id = tuple[dict,int]

def overlap(t1 : rename_id, t2: rename_id) -> Optional[dict]:
    if t1[1] != t2[1]:
        return None
    

```

```python
import functools

@functools.cache
def hashcons(x):
    # hashing does a traversal, which is not ideal. But it does give us object identity
    return x

x = (1,2)
y = (1,2)
assert x is not y

x = hashcons((1,2))
y = hashcons((1,2))
assert x is y
```

```python
table = {}
def hashcons(x):
    if x in table:
        return table[x]
    else:
        table[x] = x
        return x

type rename = dict[object, object]
type renamed = tuple[rename, object]
def var(x : str) -> renamed:
    return {0 : x}, hashcons(('var', 0))

def app1(f : str, x : renamed) -> renamed:
    rename, x1 = x
    return rename, hashcons((f, x1))
type perm = dict[int, int]

def app2(f : str, x : renamed, y : renamed) -> renamed:
    rename, x1 = x
    rename2, y1 = y
    inv =  {v: k for k, v in rename.items()}
    inv2 = {v: k for k, v in rename2.items()}
    swaps_xs = set(rename2.values()) - set(rename.values())
    nfv_x = len(rename)
    vs = set(rename.values()) |  set(rename2.values())
    for n in range(len(vs)):
        
    #perm = nfv_x :  len(swap_xs)

    perm = {}
    renameout = rename.copy()
    curr = len(rename)
    for n in range(len(rename1)):
        yv = rename2[n]
        if yv in swap_xs:
            perm[curr] = n
            curr += 1

        #yv is in y but not in x:

    perm = { len(rename)}

    if rename is rename2:
        return rename, hashcons((f, x1, y1))
    else:
        new_rename = rename.copy()
        new_rename.update(rename2)
        return new_rename, hashcons((f, x1, y1))





```

# Inj Thinning

Evocative of `DeclareSort("Var")` Also the simplicial category of those simplciial sets. Also cat;ab C-sets.

<https://types.pl/@AndrasKovacs/114938134631356899>
 Nom, [Inj, Set] and [Thinning, Set]  
 "For the benefit of others in the thread, let me zero in on a point regarding logical principles. There are several toposes that are worth thinking about here:

1. [Fin, Set]
2. [Inj, Set]
3. Sh(Inj, J[atomic]) == Nom

These are all places where you can study some kind of abstract syntax. They are also classifying toposes for certain geometric theories, of which the "type of names" is the generic model.

1. [Fin, Set] classifies the theory with a single sort but no other geometric features. So in this world, variables are totally structureless. So, one thing you can't do is compare variables for equality — indeed, it is actually the case that "forall x, y: Var, not(not(x=y))" holds. So it is always possible that two variables could become equal — this corresponds to FinSet being _cartesian_ monoidal, so it has contractions/diagonals.

2. [Inj, Set] classifies the theory of a single sort + decidable equality. In this world, variables are mostly structureless but they have decidable equality.

3. Nom classifies the theory of a single decidable sort that is _infinite_ in the sense that for any finite set of names there exists another name that is distinct from those.

As Zhixuan alludes to, these toposes are all related to each other in monadic ways. Sam Staton has a very nice PhD thesis about this."

What's useful about nominal sets compared to [Inj, Set] should be the additional logical principles that nominal sets validate. In Sam Staton's this paper (<https://dl.acm.org/doi/10.1007/978-3-642-12032-9_5>), he said in Section 6 that the principle (x , y : X) -> [𝔸](x = y) -> (x = y) that is valid for nominal sets X but not in general for [Inj, Set] greatly simplified his completeness proof <https://dl.acm.org/doi/10.1007/978-3-642-12032-9_5>

"Let me give some context for what I'm trying to do. I'd like to do metaprogramming with useful induction principles over object syntax and as much higher-order syntax as I can get. Simply typed object syntaxes would be fine. One of the longer term goals is to support proof tactic programming over simply-typed syntax, which still needs to be post-hoc kernel-checked but which affords some safety.

I've looked at Nom, [Inj, Set] and [Thinning, Set] so far. I'd like to have an internal TT for one or more of these, which is computationally adequate and reasonably expressive.

So far I have not seen such system. James Cheney's "Dependent Nominal Type Theory" comes closest but it's rather barebones. Also, is there any source about metaprogramming in [Thinning, Set]? We get decidable total ordering of variables there, which means that we get efficient set and map data structures of variables, which might turn out to be very important in real-world usage.

Right now I don't have a good understanding of what practical benefit Nom would get me compared to [Inj, Set], and I also don't have a grasp of how to do computationally adequate things in Nom.

I looked at Mitchell Riley's tiny modality too, which looks like a high-powered way to  handle "fresh variables", but

It's complicated.
As described in the paper it only works with structural binders, so with [Subst, Set] and [Fin, Set], but not with [Inj, Set] or [Thinning, Set], although this could be fixable.
I have no idea how it could work with type-annotated variables.
So I started to hack on my own TTs for [Inj, Set] and [Thinning, Set]. It looks promising but half-baked currently.
"

# Old

<https://www.philipzucker.com/union-find-groupoid/>

<https://www.philipzucker.com/canon_search/>

I was fiddling with a canonized for for z3 get_id. FOr a second I thought it might be easy?

f(X,Y,X) can be relablled by a traversal.
g(t1,t2) where t1 and t2 have been traversal labelled may need relabelling. Traversals are non compositional.

Be lazy pushing the relabellings down. Maintain label permutations at nodes.

Now different uses can share the same "shape". When you recurse into the term, your can collect up permutations along the way.

["x", "y", "z"]

But is this a cup game? What do you actually do

can you make a slotted hash cons?
Do you have to have the union find piece?
Maybe you do.

I guess everything has alpha symmettry, so you can always pull permutation through to normalize a node. Like a rotational symmettric function.

f((p1,x1), (p2,x2))  -->  p f((1, x1), (p2', x2), )

Variable are represented as
0<->2, Vva

eids are   (ident, [1,4,2]) tuples?

Sequences can be acted upon by variable permutations and slot permuations, which are interrleated
(ident, [1,4,2]) =P,Q= (ident, [6,2,4])

(v, [1])

(v, [2,3,4]) ???

I don't see the point of slot permutations then. I guess they boil down to different naming strategies on a particular term.
(v, [1,2,3])

(P, v, [x,y,z])

e(i,j,k) = f(e1(i,j), e2(k,m))
I don't feel like there is an issue here.

Oh, if normal form is expensive to produce, then top down actually might have it cached for you in a nice way. Hmmm.

ground KB using miller matching / equality. beta0
You need beta zero to flatten

The ordering of flat form doesn't matter because e is always less than symbols. So you are always decreasing in size. Kind of a weird transformation? Or very normal? Make new definitions, new system may be easier to orient. Dependency pair method invented symbols. hmm. Is there a relationship?

P1 @ e(1,2,3) = P2 @ f(P3 @ e1(7,5) , P4 @ e2(3,4))

or

e(i,j,k) = (lam x y z, f(e1(x,y), e2(y,z)))(i,j,k)

a bit more uninform. eta expanded. let expanded?

e(i,j,k) = let x = i let y = j let z = k in f(e1(x,y), e2(y,z))

```ocaml
type slot_term = 
    | Var
    | Fun of string * args
and args = (slot_term * int list) list

type term = {vs : int list; t : slot_term}

let var n : term = {vs = [n]; t = Var}
let fun (head : string) (args : term list) : term = 

let children (t : term) : term list =



type slot_term = 
    | Var
    | Fun of string * term list
and term = {vs : int list; t : slot_term}

```

terms are not hash consed. They are dealth with structurally.
or two types of term. One hash consed the ther not?

typesafe modular hashconsing

```
type 'a slot_term = 
    | Var
    | Fun of string * 'a list
and 'a term = {vs : int list; t : 'a slot_term}

```

```
type slot_term = 
    


```

I had an ast for HOpatterns

```
type miller = 
    | Var of int (* de bruijn var *)
    | App of miller * int list  (* multi appl)
    | Lam of int * miller (* multiarity lambda *)
    | Const of string * miller list


```

<https://jesper.sikanda.be/posts/1001-syntax-representations.html>

```
(* intersperse succ inside. Oleg style. Also Pavel post. Also explicit subtitution? *)
type float_db = 
  | Succ of float_db (* instead of Var int *)
  | Zero
  | App of float_db * float_db
  | Lam of float_db

```

arxiv.org/abs/2412.16206 information aware telescopic constraint rewess Cowderoy
 <https://arxiv.org/abs/1807.04085> everybody gotta be someherre
  <https://arxiv.org/abs/2105.02856> hash modulo alpha

```ocaml
type vmap = 
  | Left of vmap
  | Right of vmap
  | Both of vmap * vmap
  | Here
  (* | None ? *)

| None
| Here
| Node of vmap * vmap


type co_db = 
    | Var
    | App of co_db * co_db
    | Lam of vmap * co_db

type open_term = {vs : (string * vmap) list; t : co_db}

let var (name : str) : term = {vs = [name , Here]; t = Var} -- Hmm.
let app f x = {vs = map app_combine f.vs x.vs ; t = App (f.t, x.t)}
let lam name body = {vs = remove name body.vs; t = Lam (lookup name body.vs, body.t)} 


(* more interspersed? This feels better for egraph since we need nodes entangled *)
type co_db2 = 
    | Var of list vmap
    | App of list vmap * co_db2 * co_db2
    | Lam of vmap * list vmap * co_db2
```

```python
from kdrag.all import *

def alpha_canon(e):
    todo = [e] \
    # seen = set()
    vs = []
    while todo:
        e = todo.pop()
        if smt.is_var(e):
            if e not in vs:
                vs.append(e)
                return 
        else:
            todo.extend(reversed(e.children())) # reversed? doesn't really matter.
    return vs
# smt.substitute_var(e, *vs)

# but you can also do this while you're constructing

def Var(n):
    return [smt.Var(n)], smt.Var(0)
def apply(decl, *args):
    newvs = []
    cs = []
    for vs, c in args:
        for v in vs:
            if v not in newvs:
                newvs.append(v)
        cs.append(smt.substitute(c, *newvs)) # sometyhing here. Not this
    newvs, decl(*cs)
    




```

```python
(e, [])
```

```python

```

```python
from dataclasses import dataclass

@dataclass
class Perm():
    data : dict
    def __init__(self, data):
        assert set(data.keys()) == set(data.values())
        self.data = {k : v for k,v in data.items() if k != v} # compress away self mappings
    def __matmul__(self, other):
        p1 = self.data
        p2 = other.data
        meets = set(p2.values()).intersection(set(p1.keys()))
        ip2 = ~p2
        pass2 = { k : v for k,v in p2.items() if v not in meets }
        pass1 = { k : v for k,v in p1.items() if k not in meets }
        compo = {ip2[m] : p1[m]  for m in meets}
        return Perm({**pass1, **compo, **pass2})
    def __invert__(self):
        return Perm({v : k for k, v in self.data.items()})
    def support(self):
        return set(self.data.keys())
    #def __call__(self, x):
id_ = Perm({})

def Var(n):
    return (Perm({0 : n, n : 0}), "VAR")

Var(3)

def Const(x):
    return (id_, x)


def Fun(f, *args):
    pf = Perm({})
    norm_args = []
    for p,x in args:
        unfixed_vars = p.support() - pf.support()
        
        norm_args.append(( , x))

    return (id_, (f, args))


def min_perm(p, vs):
    # given permuation p and permutable variables vs, find a minimum permutation that only moves non-vs ? Is this cogent?

```

    (Perm(data={0: 3, 3: 0}), 'VAR')

We can replace (P, eid) pairs everywhere.
f applied to `(p1, eid)` `(p2, eid)`
p3, f((p1',eid), (p2',eid))

1. compress to 0,1,2,3
2. search over all permutations.
3. apply them to (p1, p2) pair. Take least one.

This is not the traversal algorithm.

```python
(perm, eid)
```

I'm trying to lex minimize a sequence of permutations.

nat -> nat, maybe permutations could be seen as multisets
But I want id to be minimal.
I want smaller support to be smaller
And I want the support

maybe I do need to have number of vars at play to not be implicit.

search over all permutations? maybe this is close to an intractable problem.

Yea, I feel like we're pushing the traversal up. We don't actually have to sweep the term. We can just work on the permutations.
So the first n vars

If you do hashconsing of actual sweeping, you need to relabel the term when you come down again. Or you could cache it I suppose.
But why store both. Really you should store the swept term + a relabeling. Does the relabeling have to be a permutation?

Nominal hash consing

Leaving a term partially un hashconsed. Some symbols are not hashconsed and become part of the identifier. That's EMT - union find. HashCons Modulo Theories.
This is basically the msart constructor idea. You don't intern until you know the rewrite rules are done.

ground tags is nice optimization

Find the relabelling. Don't do it though. carry it up. Isomorphic kind of to just storing canonical and noncanonical form.

Maybe take the hash cons out.
PermTerms

Maybe I do need to pass the vars down to subargs? Another level of Perm indirection?

@dataclass
class Fn(Term):
    name : str
    args : tuple[tuple[Perm,Term],...]

lam x,y,z. f(e1(x,y), e2(y,z))

lam x,y. e1(x,y) = lambd x1, y1. f(e3(x1))

Non ground, But at pretty special positions.
e(X,Y) = f()
Hmm.
what about protecting with a v constructor. v constructors have no rules...
v(X)
But I want v(X) != v(Y) for alpha... Rigidity.
X != Y -> v(X) != v(Y) injectivity.

collect ineq constraints.
X != Y | f(v(X), v(Y))
~$distinct(X,Y,Z) |
If we leave off distinct, the v fail to be rigid. Which makes them less like free vars and more like schmatic vars.
This might work. An encoding of a notion of nominality.
v always being at the leaves means some overlaps can't happen. And it all Vars occurs in v, then it is is quasi ground in a sense.
app(lam(v(X), v(X)), E) = E
Nah. This isn't going to work. We need to somehow know about renaming, and we don't get that we are distinct from some other thing... right?

SHould these be capable of overlap or not? ... Yessss.... ?
f(v(X)) = p
f(v(Y)) = q

constructor-ground. All non grounds are surrounded by constructors?
This might be terminating.

X != Y ->
v(X) = v(Y). This can't be oriented.
plus(V(X), V(Y)) = plus(V(Y), V(X)). This can't be oriented.
But ground completeable
X < Y -> plus(v(Y), v(X)) --> plus(v(X), v(Y))

resolution provers have _some_ method baked in to deal with var symmettries.

what about de bruijn. What's wrong with that?
app(lam(v0), x) = x

app(app(lam(lam(vs(vz)))),p,q) = q

```python
@dataclass
class Term:
    perm : Perm

@dataclass
class Fn(Term):
    name : str
    args : tuple[Term,...]

@dataclass
class Var(Term):
    pass    

def V(n):
    return Var(Perm({n : 0, 0 : n}))
V(3)



```

    Var(perm=Perm(data={3: 0, 0: 3}))

```python
class DoubleTerm():
    uncanon
    canon
```

```python
class Fn():
    _instances = {}
    def __init__(self, name, *args):
        self.name = name
        self.args = args
    def __new__(cls, name, *args):
        if (name, args) in cls._instances:
            return cls._instances[(name, args)]
        else:
            instance = super(Fn, cls).__new__(cls)
            cls._instances[(name, args)] = instance
            return instance
    # maybe this is defulat?
    def __hash__(self):
       return hash(id(self)) #return hash((self.name, self.args))
    def __eq__(self, other):
        return self is other
    def __repr__(self):
        return f"Fn({self.name}, {self.args})"

x = Fn("F")
y = Fn("F")
assert x is y
z = Fn("F", 1)
w = Fn("F", 1)
assert z is w
assert not z is y
q = Fn("F", x, x)
q2 = Fn("F", x, x)
assert q is q2
```

```python
from kdrag.all import *
from dataclasses import dataclass

def inv(p):
    return {v : k for k, v in p.items()}    

def comp(p1,p2):
    meets = set(p2.values()).intersection(set(p1.keys()))
    ip2 = inv(p2)
    pass2 = { k : v for k,v in p2.items() if v not in meets }
    pass1 = { k : v for k,v in p1.items() if k not in meets }
    compo = {ip2[m] : p1[m]  for m in meets}
    compo = {k : v for k,v in compo.items() if not k.eq(v)} # compress away self mappings
    return {**pass1, **compo, **pass2}

def act(p, t):
    return smt.substitute(p, *t.items())

a,b,c,d,e,f,g,h = smt.Ints("a b c d e f g h")

p1 = {a : b, b : c, c : a}
p2 = {d : e, e : f, f : d}
assert comp(p1,p2) == {**p1, **p2}
p3 = {a : d, d : a}
assert comp(p1,p3) == {b : c, c : a, d : b, a : d}

comp(inv(p1),p1)
```

    {}

The set of keys and values have to be the same right? Yes.

but what if then further canon make x be self mapped?

maybe no compress.
Just brute force the entire space of the current 0-n

<https://en.wikipedia.org/wiki/Group_action>

slotted egraphs may be using both extended enodes and extended eids.

```python
import itertools
# permutations of 0.len(p) represented as dense lists.

def mul(p1, p2): # multiply
    return trim([p1[j] if j < len(p1) else j for j in p2] + p1[len(p2):])

def act(p,q):
    return mul(p,q)
#def act(p, q):
#    return mul(mul(p, q), inv(p))
# conjugate?

def inv(p):
    q = [0]*len(p)
    for i,j in enumerate(p):
        q[j] = i
    return q

def id_(n):
    return list(range(n))

act(id_(1), id_(3))
act([1,0], [1,0,2])


def trim(p):
    # removed tail which is just identity permutation
    p = list(p)
    while p and p[-1] == len(p)-1:
        p.pop()
    return p

def swap(i,j):
    if i == j:
        return []
    else:
        p = list(range(max(i,j)+1))
        p[i], p[j] = j, i
        return p

trim(id_(3))
trim([1,0,2])

# sup = len(trim(p))

def canon(*ps):
    ps = [trim(p) for p in ps]
    sup = max(len(p) for p in ps)
    return trim(min(itertools.permutations(range(sup)), key=lambda a: [act(list(a), p) for p in ps]))

act(canon([2,0,1]), [2,0,1]) # This should always be the identity.
# in turn, we can always make the first argument the identity. THen the rest have to search over things that make the first invariant.

```

    []

```python
table = {}
nodes = []
def hashcons(t):
    if t in table:
        return table[t]
    else:
        e = len(nodes)
        table[t] = e #len(nodes)
        nodes.append(t)
        return e

def fn(name):
    def res(*args):
        ps = [arg[0] for arg in args]
        a = canon(*ps)
        args = tuple((tuple(act(a,p)),eid) for p,eid in args)
        return (a, hashcons((name, args)))
    return res
def var(n): # maybe make these negative?
    return swap(0,n), hashcons(None)
def const(x):
    return (), hashcons(x)

v0,v1,v2 = [var(x) for x in range(3)]
a,b,c = [const(x) for x in "abc"]

v0
v1
v2
f = fn("f")
f(v1,v0,v1)
table
#f(a,b,c)
def arg(pid, n):
    p, eid = pid
    name, args = nodes[eid]
    (q, argid) = args[n]
    return act(p,q), argid

assert arg(f(v1,v0,v1), 0) == v1
assert arg(f(v1,v0,v1), 1) == v0
assert arg(f(v1,v0,v1), 2) == v1

print("102", f(v1,v0,v2)) #== 
print("210", f(v2,v1,v0))
print(f(v0, v1, v2))
print(f(v0,v0,v0))
print(f(v1,v1,v1))
print("001", f(v0,v0, v1))
print("110", f(v1,v1,v0))
table
```

```python
ps = [v0[0], v1[0], v2[0]]
c = [[act(list(a), p) for p in ps]  for a in itertools.permutations(range(3))]
print(min(c))
c
```

    [[], [1, 0], [2, 1, 0]]





    [[[], [1, 0], [2, 1, 0]],
     [[0, 2, 1], [2, 0, 1], [1, 2, 0]],
     [[1, 0], [], [2, 0, 1]],
     [[1, 2, 0], [2, 1, 0], [0, 2, 1]],
     [[2, 0, 1], [0, 2, 1], [1, 0]],
     [[2, 1, 0], [1, 2, 0], []]]

```python
ps = [v1[0], v2[0], v0[0]]
c = [[act(list(a), p) for p in ps]  for a in itertools.permutations(range(3))]
print(min(c))
c
```

    [[], [2, 0, 1], [1, 0]]





    [[[1, 0], [2, 1, 0], []],
     [[2, 0, 1], [1, 2, 0], [0, 2, 1]],
     [[], [2, 0, 1], [1, 0]],
     [[2, 1, 0], [0, 2, 1], [1, 2, 0]],
     [[0, 2, 1], [1, 0], [2, 0, 1]],
     [[1, 2, 0], [], [2, 1, 0]]]

```python
inv([1,0,2])
```

    [1, 0, 2]

```python
swap(1,2)
swap(3,4)
```

    [0, 1, 2, 4, 3]

```python
def canon(G):
    N = max(max(e) for e in G) + 1 # number of vertices
    return min([act(perm,G) for perm in itertools.permutations(range(N))]) 
```

```python
def compress(p):
    return {i : k for i,k in enumerate(p.keys())}

p * q * inv(p) # compresses to 0-n


```

# Hash cons

```python
table = {}
nodes = []
def hashcons(t):
    if t in table:
        return table[t]
    else:
        e = len(nodes)
        table[t] = e #len(nodes)
        nodes.append(t)
        return e

def fn(name):
    def res(*args):
        return hashcons((name, args))
    return res
def var(n): # maybe make these negative?
    return hashcons(n)

a,b,c = [hashcons(x) for x in "abc"]
f = fn("f")
f(a,b,c)



```

    3

eids are now pairs of (perm, id)

Yes I've acehive nothing.
(perm, id, perm)  ?

```python
table = {}
nodes = []
def hashcons(t):
    if t in table:
        return table[t]
    else:
        e = len(nodes)
        table[t] = e #len(nodes)
        nodes.append(t)
        return e

def fn(name):
    def res(*args):
        ps = [arg[0] for arg in args]
        a = canon(*ps)
        args = tuple((tuple(act(a,p)),eid) for p,eid in args)
        return (a, hashcons((name, args)))
    return res
def var(n): # maybe make these negative?
    return swap(0,n), hashcons(None)
def const(x):
    return (), hashcons(x)

v0,v1,v2 = [var(x) for x in range(3)]
a,b,c = [const(x) for x in "abc"]

v0
v1
v2
f = fn("f")
f(v1,v0,v1)
table
#f(a,b,c)
def arg(pid, n):
    p, eid = pid
    name, args = nodes[eid]
    (q, argid) = args[n]
    return act(p,q), argid

assert arg(f(v1,v0,v1), 0) == v1
assert arg(f(v1,v0,v1), 1) == v0
assert arg(f(v1,v0,v1), 2) == v1

print("102", f(v1,v0,v2)) #== 
print("210", f(v2,v1,v0))
print(f(v0, v1, v2))
print(f(v0,v0,v0))
print(f(v1,v1,v1))
print("001", f(v0,v0, v1))
print("110", f(v1,v1,v0))
table
```

    102 ([1, 0], 5)
    210 ([2, 1, 0], 6)
    ([], 7)
    ([], 8)
    ([1, 0], 8)
    001 ([], 9)
    110 ([1, 0], 9)





    {None: 0,
     'a': 1,
     'b': 2,
     'c': 3,
     ('f', (((), 0), ((1, 0), 0), ((), 0))): 4,
     ('f', (((), 0), ((1, 0), 0), ((2, 0, 1), 0))): 5,
     ('f', (((), 0), ((1, 2, 0), 0), ((2, 1, 0), 0))): 6,
     ('f', (((), 0), ((1, 0), 0), ((2, 1, 0), 0))): 7,
     ('f', (((), 0), ((), 0), ((), 0))): 8,
     ('f', (((), 0), ((), 0), ((1, 0), 0))): 9}

A slotted hash cons. ()

```python
table = {}
def hashcons(c):
    if c in table: # This part is doing an unnesarily slow recursive hashing
        return table[c] # and this
    else:
        table[c] = c
        return c

x = (4,(8,6))    
y = hashcons(x)

z = (4,(8,6))
assert not z is y
q = hashcons(z)
assert q is y





```

```python
id_table = {}
child_table = {}
def hashcons(c):    
    v = id_table.get(id(c), None)
    if v is not None:
        return v
    else:
        v = child_table.get(tuple(id(child) for child in c))
        if v is not None:
            return v
        else:
            id_table[id(c)] = c
            child_table[tuple(id(child) for child in c)] = c
            return c


```

```python
child_table = {}
def hashcons(c):    
    v = child_table.get(type(c) + tuple(id(child) for child in c))
    if v is not None:
        return v
    else:
        child_table[tuple(id(child) for child in c)] = c
        return c
```

<https://www.geeksforgeeks.org/object-interning-in-python/> This is also kind of reminiscent of "typeclasses"

```python
class MyClass:
    _instances = {}
    def __new__(cls, value):
        if value in cls._instances:
            return cls._instances[value]
        else:
            instance = super().__new__(cls)
            cls._instances[value] = instance
            return instance

    def __init__(self, value):
        self.value = value
a = MyClass(20)
b = MyClass(50)
print(a is b)
```

```python
class HashTuple(tuple):
    
    def __hash__(self):
        for 
```

```python
x = (1,2,3)
x.interned = True
```

    ---------------------------------------------------------------------------

    AttributeError                            Traceback (most recent call last)

    Cell In[31], line 2
          1 x = (1,2,3)
    ----> 2 x.interned = True


    AttributeError: 'tuple' object has no attribute 'interned'

```python
table = {}
def hashcons(c):
    p,x = c
    if x in table: # This part is doing an unnesarily slow recursive hashing
        return p, table[x] # and this
        # p1,x = table[x]
    else:
        table[x] = x
        return p, x

x = (4,(8,6))    
y = hashcons(x)

z = (4,(8,6))
assert not z is y
q = hashcons(z)
assert q is y


```

```python
class Testo():
    def __hash__(self):
        print("hashcheck")
        return object.__hash__(self)
    
x = Testo()
p = {x : 1}
print("done")
p = {(x,(x,x)) : 1}
(x,(x,x)) in p
```

    hashcheck
    done
    hashcheck
    hashcheck
    hashcheck
    hashcheck
    hashcheck
    hashcheck





    True

```python
smt.Sum(a*b, b*c, c*a).num_args()
```

    3

```python
def flatten(t):
    todo = [(smt.FreshConst(t.sort(), prefix="eid"), t)]
    res = []
    while todo:
        eid, t = todo.pop()
        fresh = [smt.FreshConst(c.sort() , prefix="eid") for c in t.children()]
        res.append(eid == t.decl()(*fresh))
        todo.extend(zip(fresh, t.children()))
    return res

flatten(a * b + c)

# unionfind of eids

```

    [eid!0 == eid!1 + eid!2,
     eid!2 == c,
     eid!1 == eid!3*eid!4,
     eid!4 == b,
     eid!3 == a]

```python
class Perm(dict):
    def __matmal__(self, other):
        return comp(self, other)
    def __invert__(self):
        return inv(self)
    def __add__(self, other):
        return comp(self, other)
    def __negate__(self):
        return inv(self)
    
id_ = {}

class GroupUF:
    uf : []
    grp : []

    def find(self, px):
        (p,x) = px
        while self.uf[x] != x:
            p = p + self.grp[x]
            x = self.uf[x]
        return (p, x)
    def union(self, px1, px2):
        (p1,x1) = self.find(px1)
        (p2,x2) = self.find(px2)
        if x1 != x2:
            self.uf[x1] = x2
            self.grp[x1] = (-p2) + p1
        elif x1 == x2 and p1 != p2:
            raise Exception("Inconsistent union")


class EGraph:
    enodes :
    eclasses : 
    
```
