---
title: Extensional and Intensional Equality of Thinning Dicts
date: 2026-11-15
---

Extensional vs Intensional equality is something that occurs in type theory and it is a bit confusing.

Extensional equality is about input output behavior for functions, or what elements are in a set.

Intensional equality retains more distinctions due to how you constructed or represented or described the thing.

This blog post is about a similar (identical?) phenomenon in map data structures and using them in a [finite dict model of type theory](https://www.philipzucker.com/dtt_python_family/) to notice taint-like distinctions between different ways of writing the terms `x |- if x then True else True` and `x |- True`. In Lean etc one might expect one to be stuck and the other not stuck, but nevertheless be able to prove them equal

(I guess that is more of the definitional vs propositional equality distinction rather than intensional/extensional distinction. Maybe I'm fundamentally confused but the two distinction seem kind of related to me. Extensional type theory's definitional equality is allowed to search through propositional equalities).

# Multiple Equality Notions of Map and Set Datastructures

A more mundane example of an extensional and intensional equality distinction occurs in the majority of Map and Set data structures that are commonly used.

Structural equality of the data structures is like an intensional equality in that it has more distinctions than the extensional semantic equality.

It can observe more than input-output behavior and often records history of how the thing was made. (history independent data structures is an atypical subclass of data structures <https://theory.stanford.edu/~vteague/STOC01.pdf>)

Most map data structures are not structurally canonical for the data they hold. The way the buckets are filled ([hash table](https://en.wikipedia.org/wiki/Hash_table) ) or the tree is balanced ([avl tree](https://en.wikipedia.org/wiki/AVL_tree) etc) or the list is ordered depends on the manner in which you constructed it, not exclusively on the data held.

The most simple and obvious example of this is using lists or association lists as sets and dicts. Duh, two different orderings can represent the same set. As is often the case, this example is so obvious it is almost confusing.

```python
x = [4,1,5,2]
y = [1,5,4,2] # x and y are same "set" but different lists

def set_eq(a : list, b : list) -> bool:
    return all(x in b for x in a) and all(x in a for x in b)
    #also return set(a) == set(b) works, but that is almost feels like cheating?

assert not x is y   # not pointer equal, that's for sure
assert not x == y   # not structurally equal
assert set_eq(x, y) # but yes, same considered as sets
assert set(x) == set(y)
assert sorted(x) == sorted(y) # soring helps, although doesn't solve duplicated. Just sorted is canonical for multisets

```

But lists are some silly ass sets right?

Well, the same sort of thing is true of python's built in dicts. The order that elements fill the backing hash tables buckets depends on the order you filled data in there. A shadow of this can be be found in just examining the dict's size.

If you can tell the difference between two representatives, how "equal" are they really? Only for some purposes, which is _fine_. But it is not a priori clear you can replace one for the other in every possible situation. And maybe sometimes it isw interesting or useful to notice the differences.

```python
import sys

fresh = {}
used = dict.fromkeys(range(1000))
for key in range(1000):
    del used[key]

assert fresh == used
print(sys.getsizeof(fresh), sys.getsizeof(used))  # 64 36952 here
```

    64 36952

# Thinning Dicts

The [thinning](https://www.philipzucker.com/thin1/) dict is a dictionary wrapper that has even more redundancy in its representation. The main motivation was to model a shadow of type theory's notion of stuckness (as we'll get to next), but I think the thinning dict is self motivating as a nice data structure for representing total maps from a tuple where you expect some of the elements of the tuple to never matter. You should keep those parts of the key factored out.

It's a conceivable optimization to just record which elements of the tuple matter and only store an inner private dict on those pieces. In the best case, this can lead to exponential savings (in the length of the tuple) compared to a dense dict. In the worst case, you are just storing a dense dict with a couple more steps.

```python
from dataclasses import dataclass, field
import itertools
@dataclass
class ThinDict:
    dom : list[set]   # the domain sets for each index
    thin : list[bool] # which parts of the key tuple actually matter
    data : dict[tuple, object] # keys are only tuples from sets that matter

    def __getitem__(self, id : tuple):
        assert len(id) == len(self.dom) and all(x in A for x, A in zip(id, self.dom))
        key = tuple(x for x,take in zip(id,self.thin) if take) # prune to relevant key parts
        return self.data[key]
    #def __setindex__(self, id, value): ...
    def to_dict(self):
        return {key: self[key] for key in itertools.product(*self.dom)}
    def ext_eq(self, other):
        return self.to_dict() == other.to_dict()
    def __le__(self, other): # A partial / refinement order on thin dicts. Kind of interesting.
        return self.ext_eq(other) and all(a <= b for a, b in zip(self.thin, other.thin))
    @staticmethod
    def of_dict(d : dict):
        assert len(d) > 0 and all(isinstance(k, tuple) for k in d.keys())
        dom = list(map(set, zip(*d.keys())))
        thin = [True] * len(dom)
        data = {tuple(key): value for key, value in d.items()}
        return ThinDict(dom=list(dom), thin=thin, data=data)
    @staticmethod
    def const(dom : list[set], value) -> Self:
        thin = [False] * len(dom)
        data = {(): value}
        return ThinDict(dom=dom, thin=thin, data=data)
    def weak(self, thin : list[bool], newdom : list[set]):
        assert self.dom == [d for d, take in zip(newdom, thin) if take] 
        t = iter(self.thin)
        thin = [next(t) if take else False for take in thin] # thinning composition
        return ThinDict(dom=newdom, thin=thin, data=self.data)
    @staticmethod
    def id_(d : set):
        return ThinDict([d], [True], {(k,) : k for k in d})
    @staticmethod
    def proj(dom : list[set], i : int):
        d = dom[i]
        return ThinDict.id_(d).weak([j == i for j in range(len(dom))], dom)
    def map(self, f):
        return ThinDict(dom=self.dom, thin=self.thin, data={k: f(v) for k, v in self.data.items()})
    def __mul__(self, other): # Kind of applicative / liftA2. 
        # kind of pair constructor?   G |- t ,  G |- s  ===> G |- (t, s)
        assert self.dom == other.dom
        common = [a or b for a, b in zip(self.thin, other.thin)]
        thina = [a for a,b in zip(self.thin, common)  if  b]
        thinb = [a for a,b in zip(other.thin, common) if b]
        data =  {key : ( self.data[tuple(k for k,take in zip(key, thina) if take)],
                        other.data[tuple(k for k,take in zip(key, thinb) if take)]) 
                 for key in itertools.product(*[T for T,take in zip(self.dom, common) if take])}
        return ThinDict(dom=self.dom, thin=common, data=data)



Void = set()
Unit = {()}
Bool = {True, False}
Color = {"red", "green", "blue"}

ctx = [Bool, Color, Unit]
d = ThinDict.const([Bool, Unit], True)
d.weak([True, False, True], [Bool, Color, Unit])

d.id_(Bool).weak([True, False, False], [Bool, Color, Unit])[(False, "red", ())]


ThinDict.proj([Bool, Color, Unit], 1)  * ThinDict.proj([Bool, Color, Unit], 2)


```

    ThinDict(dom=[{False, True}, {'blue', 'green', 'red'}, {()}], thin=[False, True, True], data={('blue', ()): ('blue', ()), ('green', ()): ('green', ()), ('red', ()): ('red', ())})

Fully expanding into a dict and then converting back into a thin dict may change the thinning attached while retaining the extensional behavior.

```python
d1 = ThinDict.const([Bool,Color], 42)
d2 = ThinDict.of_dict({(a,b) : 42 for a in Bool for b in Color})
assert not d2 == d1   # thinnings are different
assert d2.ext_eq(d1)  #  they are extensionally equal
assert d1 <= d2       #  d1 is a refinement of d2
assert d2 == ThinDict.of_dict(d1.to_dict())
```

```python
small = ThinDict.const([Bool, Color], 42)
expanded = ThinDict.of_dict(small.to_dict())

assert small.data == {(): 42}
assert len(expanded.data) == 6
assert small != expanded
assert small.ext_eq(expanded)

x = ThinDict.proj([Bool], 0)
lifted_x = x.weak([False, True], [Color, Bool])

assert lifted_x.thin == [False, True]
assert lifted_x.data is x.data
assert lifted_x["red", True] == x[True,]
```

# A more type theory looking version

If we insist on also storing the codomain set and make some type synonyms, we can make thinning dicts look like a type theory interpretation (into finite sets).

I've really enjoyed and felt edified by modelling dependent type theory combinators using python dicts. <https://www.philipzucker.com/dtt_python_family/>

I was approaching it in a highly extensional way, where expressions should mean the dictionary they represent.

An idea I was exploring was if there was some way to use taint of the inputs to distinguish in a finite way some extensional vs intensional character of programs without bringing in the entire machinery of syntax trees (which is an infinite space immediately and not easily finitized into a dict).

There is an intensional difference between `(fun x => True)` and `(fun x => if x then True else True)`. It is possibly for the latter to get stuck, and that is because it needs to examine `x` to proceed.

But this phenomeonon also occurs in taint analysis <https://en.wikipedia.org/wiki/Taint_checking> (where this would be an instance of over taint, but I'm interested in it here for exactly this property). The taint is kind of a compact record or shadow retaining some information about how a result was computed.

I couldn't get this to work however, but I ended up at the extensional/intensional dict idea which feels almost confusingly straightforward.

I have said that thinnings are kind of like a free variable analysis (in that they can point out which vars are used or not), but likewise they are kind of like a taint analysis in that you know which expressions get tainted by which variables.

I'm also trying to do bidirectional typing combinators according to McBride's discipline where introductions should be check and eliminations should be synth and explicit `emb : Synth -> Check` and `ann : Check -> Ty -> Synth` combinators.

- <https://www.youtube.com/watch?v=mLoEgiiFFc8>  MSP 101: Bi-directional Typing (Conor Titania McBride)
- <https://www.youtube.com/watch?v=bcjq9Y0JVYE>  SPLV 2024 - Type Theory 1 (Conor McBride)
- <https://pigworker.wordpress.com/2018/08/06/basics-of-bidirectionalism/> basics of bidirectionalism
- <https://arxiv.org/abs/1908.05839> Bidirectional Typing Jana Dunfield, Neel Krishnaswami
- <https://arxiv.org/abs/2607.09564> Bidirectional Elaborators à la Carte

I'm kind of intrigued that because I'm not being syntactic, it is more compelling that there is not a choice here. I am used to the idea that some things can push and some things can pull. `A -> Bool` and `List A` are both sets, but to convert from the indicator function form to the enumerated form, you kind of need to be able to filter out of a known positive space. Somehow the bidirectional style is doing kind of a similar thing.

In the Mcbride presentation, preterms are also separated into Synth and Check mutually defined BNFs / ADTs. It is not clear if these preterms have a semantics, but almost a "null" or free semantics comes from the curried application of the synth and check functions to them. Here I am directly shallowy expressed the preterms in terms of their python functional meaning. But perhaps you could also put some

It appeared to me in some futzing around that the conversion rules of preterms were necesarily assymmetric or lax or refinement flavored rather thna equality flavored. Obviously? More things might type check as you reduce the term and remove untypeable junk? So the "Optionness" of definedness is going up? `if true then true else x` is overtainting in kind of a silly way that does not model stuckness

```python
"""
This form kind of feels like it's empahsizing the bidirectional synth check stuff and less pointing out the interesting data strucutre

"""

from dataclasses import dataclass, field
import itertools
from typing import Callable

type Ty = set
type Ctx = list[Ty]

@dataclass
class Term[V]: # G |- t : T
    ctx : Ctx
    thin : list[bool]
    data : dict[tuple, V]
    ty : Ty
    @staticmethod
    def const(val : V, ty : Ty):
        assert all(val in s for s in ty.cod.values())
        return Term(ty=ty, data={tuple(): val})
    def __getitem__(self, key):
        return self.data[tuple(k for k, take in zip(key, self.thin) if take)]
    def to_dict(self):
        return {k: self[k] for k in itertools.product(*self.ctx)}
    def ext_eq(self, other : "Term[V]") -> bool:
        return self.ty == other.ty and self.to_dict() == other.to_dict()



type Synth = Callable[[Ctx], Term]
type Check = Callable[[Ctx, Ty], Term]

def checkconst(v) -> Check:
    def res(ctx : Ctx, ty : Ty) -> Term:
        assert v in ty
        return Term(ctx=ctx, thin=[False]*len(ctx), data={tuple(): v}, ty=ty)
    return res

def var(n : int) -> Synth:
    def res(ctx : Ctx) -> Term:
        assert 0 <= n < len(ctx), ("n", n, "is out of bounds for context", ctx)
        ty = ctx[n]
        thin = [i == n for i in range(len(ctx))]
        data = {(x,) : x for x in ty}
        return Term(ctx=ctx, thin=thin, data=data, ty=ty)
    return res

Void : Ty = set()
Unit : Ty = {()}
Bool : Ty = {True, False}
Color : Ty = {"red", "green", "blue"}

tt : Check = checkconst(())
true : Check = checkconst(True)
false : Check = checkconst(False)


def ite(cond : Check, tyres : Ty, t : Check, e : Check) -> Synth:
    def res(ctx : Ctx) -> Term:
        c : Term = cond(ctx, Bool)
        tval : Term = t(ctx, tyres)
        eval : Term = e(ctx, tyres)
        common = [t0 or t1 or t2 for t0, t1, t2 in zip(c.thin, tval.thin, eval.thin)]
        data = {tuple(k for k,take in zip(key,common) if take) : 
                tval[key] if c[key] else eval[key] 
                for key in itertools.product(*ctx)}
        return Term(ctx=ctx, thin=common, data=data, ty=tyres)
    return res



def ann(t : Check, ty : Ty) -> Synth:
    def res(ctx : Ctx) -> Term:
        return t(ctx, ty)
    return res

def emb(s : Synth) -> Check:
    def res(ctx : Ctx, ty : Ty) -> Term:
        term = s(ctx)
        assert term.ty == ty, ("term", term, "term.ty", term.ty, "doesn't match ty", ty)
        return term
    return res



ctx1 : Ctx = [Bool, Color, Unit]
var(0)(ctx1)


# ite(true, Bool, true, false)([Bool, Bool])
# ite(true, Bool, emb(var(0)), false)([Bool, Bool])
assert not ite(emb(var(0)), Bool, true, true)([Bool, Bool]) == true([Bool, Bool], Bool)
assert ite(emb(var(0)), Bool, true, true)([Bool, Bool]).ext_eq(true([Bool, Bool], Bool))

true([Unit, Color], Bool) #

ite(emb(var(0)), Bool, true, true)([Bool,Unit])
```

    Term(ctx=[{False, True}, {()}], thin=[True, False], data={(False,): True, (True,): True}, ty={False, True})

# Bits and Bobbles

Cody podcast episode

<iframe data-testid="embed-iframe" style="border-radius:12px" src="https://open.spotify.com/embed/episode/5B8uY9mdMzKNcqy9WkG5cn/video?utm_source=generator&si=1da23707e00043e9" width="624" height="351" frameBorder="0" allowfullscreen="" allow="autoplay; clipboard-write; encrypted-media; fullscreen; picture-in-picture" loading="lazy"></iframe>

<https://arxiv.org/pdf/2510.03170> the minikanren paper for clp(set) has a different feeling definition of intensional vs extensional

<https://en.wikipedia.org/wiki/Extensional_and_intensional_definitions>

<https://philosophy.stackexchange.com/questions/16164/what-is-the-difference-between-intensional-and-extensional-logic>

<https://mathoverflow.net/questions/103815/intensional-equality-in-type-theory> this discussion also seems confused.

<https://people.cs.nott.ac.uk/psztxa/publ/lics99.pdf> Extensional Equality in Intensional Type Theory

I kind of fucking hate the words intensional and extensional and find them very offputting. I have only come to understand what they are kind of talking about by osmosis of many dimly viewed examples. I do not really have a better alternative though. Semantic and structural equality? Not great either.

Intensional vs Extensional type theory is about whether there is a rule that allows definitional equality to use a propositional equality. The type checker is allowed to do a powerful (undecidable) proof search in the middle of type checking.

Another interesting point is that we get used to the idea of equality checking to be _easy_ but it really might not be.

Checking if one boolean circuit is equal to another one is a SAT problem. This can be made arbitrarily hard.

What may be easy is checking if two representations are reasonably similar, as an underapproximation of the extensional equality we are more interested in.

But do we always want to consider two circuits that compute the same thing equal? No way. What about delay, circuit area, fan in, power usage? In fact the entire game of optimization of circuits is exploring the sense these "equal" things _aren't_ equal.

I have not been sure the lifting dict model is ok in regards to eta rules. Sometimes I try stuff and it seems like I only get "lax" equality? There is also a natural partial order on thinning dicts

# Telescoped Version

In a telescope, the sets of the domain depend on the previous sets, so it's an iterated family of sets instead of a product of sets.
This is kind of like a trie structure <https://www.philipzucker.com/telescope_tries/>

I've been reading principles of dependent types and learning about this QIIT (Altenkirch et al) way of defining type theory <https://www.youtube.com/watch?v=imz9UkdQBdI>  <https://www.youtube.com/watch?v=tTZFKkyJEtw> so this is partially inspired by that

```python
from dataclasses import dataclass, field
import itertools

@dataclass
class Ctx: # G |- .
    dom : list["Ty"]   # telescoped domain. `Gamma |- A type`
    #thin : list[bool] # goes here ?
    @staticmethod
    def emp():
        return Ctx(dom=[], thin=[])
    def extend(self, ty : Ty, used=True):
        assert self == ty.ctx
        self.dom.append(ty.cod)
        #self.thin.append(used)
    def tyconst(self, ty0 : set) -> Ty:
        return Ty(ctx=self, thin=[False] * len(self.dom), cod={tuple(): ty0})
    
    def __iter__(self):
        return itertools.product(*[T for T,take in zip(self.dom, self.thin) if take])

@dataclass
class Ty: # G |- T type
    ctx : Ctx
    thin : list[bool]
    cod : dict[tuple, set]
    @staticmethod
    def emp(ty0 : set):
        return Ty(ctx=Ctx.emp(), cod={tuple(): ty0})
    @staticmethod
    def is_type(ctx : Ctx, ty0 : dict[tuple,set]): # attach to Ctx?
        assert set(ty0.keys()) == set(ctx)
        return Ty(ctx=ctx, cod=ty0)

@dataclass
class Term[V]: # G |- t : T
    #ctx : Ctx already in Ty
    ty : Ty
    thin : list[bool]
    data : dict[tuple, V]
    @staticmethod
    def const(val : V, ty : Ty):
        assert all(val in s for s in ty.cod.values())
        return Term(ty=ty, data={tuple(): val})

# class Subst

emp = Ctx.emp()
Void = Ty.emp(set())
Unit = Ty.emp({()})
Bool = Ty.emp({True, False}) 
Color = Ty.emp({"red", "green", "blue"})


tt = Term.const((), Unit)
true = Term.const(True, Bool)
false = Term.const(False, Bool)

def ite[V](cond : Term[bool], tval : Term[V], fval : Term[V], cod : Ty) -> Term[V]:
    assert cond.ty.ctx == tval.ty.ctx == fval.ty.ctx == cod.ctx # or could try to infer.
    data = {k: tval.data[k] if c else fval.data[k] for k,c in cond.data.items()}
    assert all(v in cod.ctx[k] for k,v in data.items())
    return Term(ty=cod, data=data)

def match_unit[V](x : Term[tuple[]], v : Term[V], cod : Ty) -> Term[V]:
    assert x.ty.ctx == v.ty.ctx == cod.ctx
    data = {k: v.data[k] for k in x.data.keys()}
    assert all(val in cod.ctx[k] for k,val in data.items())
    return Term(ty=cod, data=data)

def var(ctx : Ctx, n : int) -> Term:
    assert 0 <= n < len(ctx.dom)
    thin = [False] * len(ctx.dom)
    thin[n] = True
    ty = ctx.dom[n] # question. Does "taint" of ty infect term?
    data = {(k,) : k for k in ty}
    return Term(ty=ty, thin=thin, data=data)

# bidirectional inference?
type Synth = Callable[[Ctx], Term]
#type Check = Callable[[Ctx, Ty], Term]
type Check = Callable[[Ty], Term] # we don't need the context because it is inside Ty

# Mcbride's discipline
def var(n : int) -> Synth:
    return lambda ctx: var(ctx, n)

def Bool(ctx : Ctx) -> Ty:
    return ctx.tyconst({True, False})
def Unit(ctx : Ctx) -> Ty:
    return ctx.tyconst({()})
def Prod(A : Ty, B : Ty) -> Ty:
    assert A.ctx == B.ctx
    ctx = A.ctx
    cod = {tuple(): {(a,b) for a in A.cod[tuple()] for b in B.cod[tuple()]}}
    return Ty(ctx=ctx, thin=[False] * len(ctx.dom), cod=cod)

true = lambda ctx: 

def 

def ite(c : Check, ty : Ty, t : Check, e : Check) -> Synth:
    def res(ctx : Ctx):


#def ann(term : Term, ty : Ty) -> Term: ...
def ann(t : Check, ty : Ty) -> Synth:
    def res(ctx: Ctx) -> Term:
        assert ty.ctx == ctx
        return t(ty)
    return res
def emb(t : Synth) -> Check:
    def res(ty : Ty) -> Term:
        term = t(ty.ctx)
        assert term.ty == ty
        return term
    return res

def Hom(a : Term, b : Term) -> Type: ...






```

```python
def match_(x : Check, tyres : Ty, cases : dict[V, Check]) -> Synth:
    def res(ctx : Ctx) -> Term:
        xval : Term = x(ctx, tyres)
        common = xval.thin.copy()
        for v, case in cases.items():
            common = [c1 or c2 for c1, c2 in zip(common, cval.thin)]
        data = {}
        for key in itertools.product(*ctx):
            k = tuple(k for k,take in zip(key,common) if take)
            v = xval[key]
            if v in cases:
                data[k] = cases[v](ctx, tyres)[key]
            else:
                raise ValueError(f"Unexpected value {v} in match")
        return Term(ctx=ctx, thin=common, data=data, ty=tyres)
    return res


    def match_(self, tyres : Ty, cases : dict[V, Term]):
        assert set(cases.keys()) == self.ty
        common = self.thin.copy()
        for x,case in cases.items():
            common = [c1 or c2 for c1, c2 in zip(common, case.thin)]

def match_(scrut_ty : Ty, x: Check, result_ty: Ty, cases: dict[object, Check]) -> Synth:
    def run(ctx):
        scrutinee = x(ctx)
        assert set(cases) == scrutinee.ty
        branches = {v: body(ctx, result_ty) for v, body in cases.items()}

        thin = scrutinee.thin.copy()
        for branch in branches.values():
            thin = [a or b for a, b in zip(thin, branch.thin)]

        data = {}
        for env in itertools.product(*ctx):
            key = tuple(v for v, keep in zip(env, thin) if keep)
            data[key] = branches[scrutinee[env]][env]
        return Term(ctx=ctx, thin=thin, data=data, ty=result_ty)

    return run

    x.match_()

        def map(self, f : Callable[[V], V]) -> "Term[V]":
        new_data = {k: f(v) for k, v in self.data.items()}
        return Term(ctx=self.ctx, thin=self.thin, data=new_data, ty=self.ty)
    def map2(self, other : "Term[V]", f : Callable[[V, V], V]) -> "Term[V]":
        assert self.ctx == other.ctx
        common = [t1 or t2 for t1, t2 in zip(self.thin, other.thin)]
        new_dom = itertools.product(*[T for take, T in zip(common, self.ctx) if take])
        data = {k: f(self[k], other[k]) for k in new_dom}
        return Term(ctx=self.ctx, thin=common, data=data, ty=self.ty)

def matchtt(x : Check, tyres : Ty, res : Check) -> Synth:
    def res(ctx : Ctx) -> Term:
        xval : Term = x(ctx, Unit)
        r : Term = res(ctx, tyres)
        # tempting to shortcut here
    return res

```

fibration

x,y,z |- x,y  is a prjoection off the last one
mobius strip -> circle
(sphere point,  tan vec) -> sphere point

p for projection
Note that G.x |- G  is a _substitution_ / forest term, not a term
G |- t  somehow projecting to G makes no sense

The fiber is the inverse image function of the projection. But what is up with that? That's a function into the power set space?

It's interesting that the same moves I did in thinning egraphs are showing up in the natural liftA2 definition of liftdict.

Lazy dicts
Ref counted dicts
Union find dicts. Is this demonstrating quotients or subtypes or setoids?

```python
class UFDict[K,V]:
    nf : dict[K, K] # normal form map. union find. Kind of in same mental spot as lifting
    data : dict[K, V]
    def to_dict(self):
        return {k : self.data[k1] for k,k1 in self.nf.items()}
    def ext_eq(self, other):
        return self.to_dict() == other.to_dict()
```

```
type Ty = dict # domain is "set" but target is canonical element of that set. Setoid. Set with equivalence relation
```

Other fun dicts
merge dict

[None, None, t, t, t] timesteps
(A,time)
Timely dictionaries? Timestamps. Dicts with remembered iteration ordering?
Every kind of dict is a new kind of model with different things they intensionally/structurally distinguish
persistent and semi persistent dictionaries

Extensional and intensional aspects of dicts.

<https://types.pl/@sandmouth/116291094930841679>
Two AVL Trees
Two red black trees
history independent datastructures <https://theory.stanford.edu/~vteague/STOC01.pdf>

Thinning Dicts

mcbride and

SAT problems. Their miter is an euquivalence qeustion and the unsat proof of the miter is a equality proof.
Whether two sat problems are the same is NP-complete for sure

The similarity of NP and Recursive is a topic for another day (given a certificate, you can check in polynomial time vs it is decidable to check the cert. So the question is kind of about the exists of the cert, a single E quantifier. Certs can be combined but the intersection requires certs for all subproblems whereas the union requires only 1 cert plus saying which subproblem you picked. This means the certs of the combined problems grow at a different rate. Unions are "easier" than intersections.)

I think my first misconception is that functions in type theory are actually are my naive notion of what a mathematical function is.

I have heard the explanation that we obviously don't consider a O(n) and an O(n^2) algorithms that computes the same input-output to be the same algorithms and I thought it was some kind of analogy or joke.

Having multiple notions of equality, often which refine each other is a completely ubiquitous phenomemon

Well, they _are_ the same algorithm in one sense, the extensional sense.

The principle of function extensionality is also in here somewhere. When I first saw (and still my impulse) if that `forall x y, (f x = g y) -> f = g` is a non statement. That is a property of what functions are, not something that could be be proven or refuted really.

In first order logic, for function _symbols_ there is no other notion of what "equal" function could mean. In fact there is no equality of functions predictae you could have

I use z3 as my standin of more or less what first order logic is

```python
from z3 import *
x,y = Ints("x y")
x == y # a proposition

f = Function("f", IntSort(), IntSort())
g = Function("g", IntSort(), IntSort())

f == g #Not a proposition. They just are not the same symbol

# What you can do is have a meta function in python that macro expands to a genuine proposition
def EqSym(f : FuncDeclRef, g : FuncDeclRef) -> BoolRef:
    return ForAll([x], f(x) == g(x))
EqSym(f,g)
```

```python
# a version following my nose from the thin dict. I hink Adding Nones to do Ctx Term Ty is kind of goofy?
from dataclasses import dataclass, field
import itertools
@dataclass
class TeleThinDict[V]:
    dom : list[TeleThinDict[set]]   # telescoped domain. `Gamme |- A type``
    cod : TeleThinDict[set[V]] | None #   Gamma |- C(x,y) type 
    thin : list[bool] # which actually matter
    data : dict[tuple, V] # keys are only tuples from sets that matter  `x : A, y : B(x) |- z : C(x,y)`

    @staticmethod
    def const(dom : list[TeleThinDict[set]], cod : TeleThinDict[set[V]], value : V) -> "TeleThinDict[V]":
        thin = [False] * len(dom)
        data = {(): value}
        return TeleThinDict(dom=dom, cod=cod, thin=thin, data=data)
    @staticmethod
    def emp_ty(ty0 : set):
        return TeleThinDict(dom=[], cod=None, thin=[], data={() : ty0})
    @staticmethod
    def emp_term(v, ty : TeleThinDict[set]):
        return TeleThinDict(dom=[], cod=ty, thin=[], data={() : v})
    @staticmethod
    def emp_ctx() -> "TeleThinDict[None]":
        return TeleThinDict(dom=[], cod=None, thin=None, data=None)
    @staticmethod
    def emp_term_ctx(v, ty : "TeleThinDict[None]"):
        return TeleThinDict(dom=[], cod=ty, thin=[], data={() : v})

type Ctx = TeleThinDict[None, None] # Gamma |-
type Ty = TeleThinDict[set, None]   # Gamma |- _ : A type
type Term = TeleThinDict[object, set] # Gamma |- t : A 



def ForAllI()

```

```python

import sys
print(sys.getsizeof({}))
d = {n : n for n in range(1000)}
print(sys.getsizeof(d))
for n in range(1000):
    del d[n]
print(sys.getsizeof(d))
assert {} == d
assert not sys.getsizeof({}) == sys.getsizeof(d)
d

assert not {} is {} # not pointer equal
assert {} == {} # extensionally equal
assert sys.getsizeof({}) == sys.getsizeof({}) # have same size

```

    64
    36952
    36952

Taint and Free variables

If we have pure expressions and want to track possible taint, we oculd have some fixed kinds of taint like "user input", but a "free" taint analysis is basically  free variable analysis. Does this term contain an input at all? Which ones? Then compositionally when we apply such a term, we can propagate the taints on the inputs to the outputs.

When we have two terms we have checked for taint like this, we have determined a maximal taint. There is no way for `t` to be tainted by `y` if it does not even appear in the term. But at that point we can start to learn that there is less taint. If two terms are equal which have apparently different taints, actually the semantic taint of the union must be the _intersection_  not the union.

Free variable analysis however has much to do with thinnings. Thinnings can make explicit the basis of support of a term.

Thinnings and free varaiables are more in the normal wheelhouse of type theory

i have said that I think AVL trees deomnstrate some of the phenonmenology of the difference of intensional and extensoinla equatity of sets as a concept.
AVL trees retain an incomplete record of how the order in which they were constructed, although they do not expose this as an interface. The data is somewhat garbled. In a sense they are _tainted_ by their construction method.

Tries are usually partial maps between keys that are sequences and codomain. If we want them to be total maps om some specified set, a different stroage method presents itself

```
type SkipTrie a = 
    | Skip Set SkipTrie
    | Leaf a
    | Case (Map key SkipTrie) actually examined 
    | Var Int -- maybe. If output key is same type as input key
```

This is kind of a BDD like compression, but with telescoping action and storing the domain sets as we go along.
For singleton types, perhaps a path compression could be useful too.

`

A related alternative is a lift dict. If it uniformly does not matter what some parts of the sequence are, we do not have to store hem

```
class LiftDict
    lift : list[Set | None]
    data : dict[tuple[key], a]
```

```
class LiftType0:
    lift : list[bool]   # we don't need to store unseen stuff because it is previously available in telescope. On the other hand, what does it hurt, since these dicts can just be a pointer to the previously defined LiftDict
    data : dict[tuple[key], set[T]]

class LiftTerm
    lift : list[None | LiftDict0[Set[key]]]  # Supports telescoping
    data : 


class LiftDict:
    lift : list[bool]
    telescope : list[LiftDict] # but these are smaller so its ok.
    data : dict[tuple[key], A] # only store relevant keys

 
```

# 2026-06

## Subset interpretation

`Type ~ (A, Asub)` not that we interpret "bare" type as anything.

So valid families are functions/dicts to sets such that when the key is in it's valid subset, the output is well formed Asub <= A

Nat vs Int is too big

Fin(n,N) as subsets?

True = {x : Bool | x = true}
UnitVoid = {x : Unit | false}

What would be ill formed?

Maybe the map is not require to be defined (can be partial) when arguments are out of required subsets

ok, I don't really need the iterated construction.

Rather than materializing `good`, could have `valid : Callable[object, bool]` predicate.

```python
from dataclasses import dataclass, field
type Env = tuple

@dataclass
class SubSet[T]:
    total : set[T]
    good : set[T]
    def __init__(self, total, good=None):
        if good is None:
            good = total
        else:
            assert good <= total
        self.total = total
        self.good = good

type Ctx = SubSet[Env]

@dataclass
class Family:
    good : set[Env]
    data : dict[Env, SubSet[object]]

    def ext_eq(self, other):
        return self.good == other.good and all(self.data[env] == other.data[env] for env in self.good)

# intensional equality is f1.data == f2.data (and f1.good == f2.good). Extensional is forall 




```

```python

@dataclass
class Ctx:
    good: set[Env]
    total: set[Env]
    def __post_init__(self):
        assert self.good <= self.total

```

```python
from dataclasses import dataclass,field

type Family = tuple[list[set[object]], dict[tuple[object], tuple[set, set]]]
# no a factored construction? It _has_ to be a trie. And we have an outer set and

type Family = tuple[set, dict[object, Family | tuple[set, set]]]
# or at every stage have a bool saying if in or out of the subset

type Family = dict[object, tuple[bool, Family | tuple[set, set]]]

@dataclass
class Family:
    argsubs : list[set]
    f : dict[object, tuple[set, set]]

    def subtype(self, P : Section):
        assert self.argsubs == P.argsubs
        return Family(self.argsubs, )

Bool = Family([], {() : ({True, False}, {True, False})})


```

Ok. But actually I wanted to write a post using taint

Taint exposes some of the computational character of _how_ you got the result.

<https://en.wikipedia.org/wiki/Taint_checking>

Taint without values at all to start off? A pure theory of taint. taint is a static analysis so we don't need to expand into all environements

```python
n |- t
```

Taint also feels like some kind of free construction, like dolan was saying? Free semilattices are basically sets of the generators.
free commutative semigroup/monoid is multisets. Adding idempotency basically makes it a set.

When you thin a section, it will retain that thinning

When you thin a type, it needs to enumerate all the thinnings that could work

`if x then 3 else 3` is tainted by x despite not really depending on it in an extensional way.

`x * 0 = 0` extensionally, but not in the taint model.

`x * 0` is a stuck term in typical left match definition. `0 * x` is not. But still tainted? Maybe. These are different definitions of *

`x & false` is a nicer example that is finite and exhibits the same issues. One possible rule of the game is that the definition is not allowed to look at taintedness of subexpressions to make choices.

Taint ~ Thinning ~ free variable analysis.
We might consider some variables tainted and others not, but the "free" version of this tracks which variables go into which stuff.

I guess it was a bit goofy to need groupby. Trie form will really be just

Getting into the value of the trie sucks.
Why can't I just keep it in flat form.

Kind of the internalizing moves to Pi can be just one step of the ctx -> Pi

```python
from dataclasses import dataclass,field
from frozendict import frozendict
from typing import Union
# Trie form
#type Trie = tuple[dict[object, Trie], int] # int is how deep to go

# Or use special class as sigil
@dataclass(frozen=True)
class Trie:
    data : frozendict[object, Union[object,"Trie"]]

    def flatten(self) -> dict[tuple[object, ...], int]:
        return { (k,) + suffix : v for k, v in self.data.items() for suffix, v in (v.flatten().items() if isinstance(v, Trie) else {() : v}.items()) }
    
    @staticmethod
    def from_flat(flat : dict[tuple[object, ...]]) -> "Trie":
        root = {}
        for k, v in flat.items():
            d = root
            for part in k:
                if (part,) not in d:
                    d[(part,)] = {}
                d = d[(part,)]
            d[()] = v
        return Trie(frozendict(root))

Trie.from_flat({(1,2,3) : 42, (1,2,4) : 43})





```

    Trie(data=frozendict.frozendict({(1,): {(2,): {(3,): {(): 42}, (4,): {(): 43}}}}))

```python
#type TaintFun = tuple[int, frozenset[int]]
type TaintFun = list[bool]  # which ones actually show up. This is exactly a thinning... Taint kind of tracks minimal context needed. Huh.

type Family =  tuple[InCtx[object], set[object], Thin] # What contexts does the type make sense in?
type Section = tuple[InCtx[object], Thin] # InCtx[tuple[object, Thin]] ? Thin is kind of static so shouldn't be env dependent.
def idthin(n):
    return [True] * n

Bool = ({(): {True, False}}, idthin(0))

# In the set semantics
ArrUnitUnit0 : Family = {(): {frozendict({() : ()})}}
idUnit : Section = {() : {() : ()}}

idUnitTaint_tainted : Section = ({() : ({() : ()}, True)}, idthin(0))
idUnitTaint_untainted : Section = ({() : ({() : ()}, False)}, idthin(0))
# Arrow values come packaged with whether they are tainted by the argument or not
# But then we have a more recursive looking thing. Where taint can depend on previous values
# Maybe the thin needs to be composed. So False, means we thin from the outerthinnning
# But True means we may still thin or not in the inner stuff.
# So maybe I really do need InCtx to be a trie to better match Arrow?
# So maybe my boolean should be a full Thin

```

```python
type Ctx = int
type InCtx[T] = tuple[int, T]

type Family = InCtx[set[int]] # free taint
type Section = InCtx[set[int]] # ?  which things tainted us?
def weak(t : Thin, x : InCtx)
```
