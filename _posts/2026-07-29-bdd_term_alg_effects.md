---
title: Finite Algebraic Effects as dicts and such
date: 2026-07-29
---

[Algebraic effects](https://arxiv.org/abs/1807.05923) are a style / mathematical framework for modelling mutation, search, and some other things. They are another attempt to bridge the gap between mathy looking stuff and our crass world of mud and time.

I think the main point of such endeavors to me is

1. it's neat
2. it kind of turns processes (an annoyingly abstract concept) into data (bits and shit) we can manipulate and reason about (dicts in this case)
3. It bridges the surprisingly painful gap between math and programs. Math class had some great ways of manipulating expressions (polynomials, fractions, integrals and so on) which could be nice if we have a language of useful programming as succinct and as easily reasoned about. For some reason, it is hard I think to _really_ systematically reason about imperative code although we do it pretty well all the time. And the only method of attack that makes sense to me (and I'd love to have an alternative that more closely matches our intrinsic ability to reason about imperativeness without the crutch) is to convert (compile?) imperative code into math (transition systems, syntax, set theory, type theory etc).
4. For me, I'm intrigued because this is an interesting way to add effects to e-graphs / SMT solvers as a baked in theory / regular rules.

The trick of algebraic effects is actually very simple, but very surprising abuse of the notion of arity (number of arguments). I guess that's why it was hard to discover. And it's still a little mind boggling.

# Terms with Parameters and Generalized Arity

Generalized Arity is kind of the same thing as keyword arguments to terms.

A basic term data type looks like this


```python
from dataclasses import dataclass
@dataclass
class App:
    f : str
    args : list["App"]

    def arity(self) -> int:
        return len(self.args)

App("add", [App("x",[]), App("42",[])])
```




    App(f='add', args=[App(f='x', args=[]), App(f='1', args=[])])



But this type is unnecessarily constrained. This isn't persay a bad thing. Abstraction and generalization is sometimes evil and sometimes goods.

We don't need function symbols to be strings. Basically we need them to have some way to compare them for equality, sometimes hashable, sometimes `<=` etc, parseable and printable. We rarely would care they are made of a sequence of characters. So we can generalize that part.

The ordered list of arguments isn't really that important either. A `list` is basically a mapping from integers to an element. A `dict` let's use map from other stuff. I believe Lua for example doesn't even have lists/arrays as a separate thing from dict/table. This is a little crazy, but also beautiful in a way. We do want to sometimes compare two terms, and we do so by zipping together arguments under common keys. The old case of arguments that are listlike can be encoded by using integers 0,1,2... as keys.

Many programming languages have positional and keyword arguments. Why shouldn't terms also have this?


```python
@dataclass
class App:
    f : object
    args : dict[object, "App"]

    def arity(self) -> int:
        # arity is now the key set.
        return set(self.args.keys())

App("add", {0 : App("x", {}), 1 : App(42, {})})
```




    App(f='add', args={0: App(f='x', args={}), 1: App(f=42, args={})})



A slightly different organization is to factor out "parameters" as special from "f". Fine, whatever.


```python
@dataclass
class App:
    f : str
    param: object
    args : dict[object, "App"]

App("add", {0 : App("x", {}), 1 : App(42, {})})
```

These two modifications make our terms into terms with parameters and generalized arity.

I recently discussed other modifications of the definition of Term here https://www.philipzucker.com/thin_term/

# Meaning

The following is so trivial that it is confusing.

If I wanted to directly explain in a shallowly embedded way the meaning of arithmetic expressions, I could write the following combinators.


```python
type V = int
def add(x : V, y : V) -> V:
    return x + y
def lit(p : int) -> V:
    return p
def neg(x : V) -> V:
    return -x

add(lit(1), lit(2))
```




    3



A more burdensome way of doing a similar thing by making an AST and then writing an interpreter over it. Python does not make AST's very lightweight. This code is so verbose it kind of makes me want to die. You can imagine how well I'm doing in the modern age of LLMs.


```python
type V = int

@dataclass
class Add:
    arg0 : V
    arg1 : V

@dataclass
class Lit:
    p : int

type Expr = Add | Lit

def interp(a : Expr) -> V:
    match a:
        case Add(arg0, arg1):
            return interp(arg0) + interp(arg1)
        case Lit(p):
            return p

interp(Add(arg0=Lit(p=1), arg1=Lit(p=2)))

```




    3



Instead of using positional arguments, I could capture all the arguments in a dictionary. This is in essence the same as the first example


```python
from typing import Never # Never is python's Void type
type Binary = Literal[0] | Literal[1]
type Unary  = Literal[0]
type V = int

def add(args : dict[Binary, V]) -> V:
    return args[0] + args[1]
def lit(p : int, args : dict[Never, V]) -> V: # Never because lit had no subexpression arguments
    return p
def neg(args : dict[Unary, V]) -> V:
    return -args[0]

neg({0 : add({0: lit(1, {}), 1: lit(2, {})})})
```




    -3



## Get-Set

This last style maps well onto the needs of algebraic effects.

This shows the meaning of a get and set on a single bool of state. Basically we are evaluating every pathway a stateful program could take and storing the result in a dictionary. Because our state is finitely enumerable, this is doable (although at greater and greater cost the larger the state gets if we do it in this direct eager non-memoized way). This is counter intuitive because for more useful state types than bool, we will end up with MASSIVE arity, when we are used to thinking about arity 0,1,2,3 and that's about it. There is no law about not going bigger though.


```python
BOOL = [True,False]

type V = dict[bool, tuple[int, bool]]
def get(args : dict[bool, V]) -> V: # get is a "diagonal projection" in a curious kind of way
    return {b : v[b] for b,v in args.items()} # projects out one layer of dict[bool, dict[bool, ..]].
def set(b : bool, args : dict[tuple[()], V]) -> V:
    res = args[()][b] # Grab the case for the new set value
    return {b0 : res for b0 in BOOL} # return it no matter what b0 we started with. We clobbered b0
def ret(i : int) -> V:
    return {b : (i, b) for b in BOOL}

get(set(True, {(): ret(3)}))
get({b : ret(3) if b else ret(4) for b in BOOL}) # This gets pretty close to lambda notation without refl

```




    {True: (3, True), False: (4, False)}



The combinators do not change much if we use some other finite enumeration like a `Color` enum.


```python
from enum import Enum
Color = Enum("Color", "Red Green Blue")

type V = dict[Color, tuple[int, Color]]

def get(args : dict[Color, V]) -> V: 
    return {c : v[c] for c,v in args.items()}
def set(c : Color, args : dict[tuple[()], V]) -> V:
    res = args[()][c] 
    return {c0 : res for c0 in Color}
def ret(i : int) -> V:
    return {c : (i, c) for c in Color}
get({c : ret(3) if c == Color.Red else ret(4) for c in Color})
```




    {<Color.Red: 1>: (3, <Color.Red: 1>),
     <Color.Green: 2>: (4, <Color.Green: 2>),
     <Color.Blue: 3>: (4, <Color.Blue: 3>)}



## Nondeterminism

We can do a similar thing with nondeterminism / search. Basically we want to return a dict of results keyed on what the randomizer / chooser chose.


```python
type V = dict[tuple[bool,...], int] # choice sequence to integer result
BOOL = [True,False]
def choose(args : dict[bool, V]) -> V:
    return {(b,) + seq : res for b,v in args.items() for seq,res in v.items()}
def ret(i : int) -> V:
    return {() : i}

choose({b : ret(3) if b else 
            choose({b1 : ret(5) if b else
                         ret(6) 
                    for b1 in BOOL}) 
        for b in BOOL})

```




    {(True,): 3, (False, True): 6, (False, False): 6}



# Free Effects
But we don't have to immediately evaluate our expressions. Like in the `Add` expression case, we can construct a tree and then interpret it later. Perhaps this is useful to start applying term techniques like memoization, smart constructors, rewriting, and e-graphs, etc.



```python
@dataclass
class App:
    f : str
    param: object
    args : dict[object, "App"]

# helper constructors. Somewhat smart.
def get[T](args : dict[T, App]) -> App:
    assert all(isinstance(arg,App) for arg in args.values())
    return App("get", (), args) # Get has no interesting param  = Unit
def set[T](i : T, args : dict[tuple[()], App]) -> App:
    return App("set", i, args) # Set has no interesting branching = arity is Unit
def ret[T](i : T) -> App:
    return App("ret", i, {}) # ret has no subexpressions. No children

type V = dict[bool, tuple[int, bool]]

def interp(e : App) -> V:
    match e:
        case App("get", (), args):
            return {b : interp(v)[b] for b,v in args.items()} # The body of previous get
        case App("set", b, args):
            return {b0 : interp(args[()])[b] for b0 in BOOL} # body of previous set
        case App("ret", i, {}):
            return {b : (i, b) for b in BOOL} # body of previus ret
        case _:
            raise ValueError(f"Unknown App: {e}")


set(True, {(): ret(3)})
```




    App(f='set', param=True, args={(): App(f='ret', param=3, args={})})




```python
interp(set(True, {(): ret(3)}))
```




    {True: (3, True), False: (3, True)}




```python
get({b : ret(3) if b else ret(4) for b in BOOL})
```




    App(f='get', param=(), args={True: App(f='ret', param=3, args={}), False: App(f='ret', param=4, args={})})




```python
interp(get({b : ret(3) if b else ret(4) for b in BOOL}))
```




    {True: (3, True), False: (4, False)}



# Bits and Bobbles

See
- Andrej Bauer - What's algebraic about algebraic effects  https://arxiv.org/abs/1807.05923 https://www.youtube.com/watch?v=atYp386EGo8
- Sam Lindley SPLV 2024 https://spli.scot/splv/2024-strathclyde/assets/slides/sam-1.pdf https://www.youtube.com/watch?v=giSaeD8R_E8&
- https://math.andrej.com/wp-content/uploads/2012/03/eff.pdf Eff 
- Pretnar https://www.eff-lang.org/handlers-tutorial.pdf an Introduction
- 
Monads are a similar endeavor. Algebraic effects kind of mush around some of the same combinators.

My impressions of by monads and algerbaic effects is that they require some ability to manipulate lambdas / continuations or at least binders. But this appears to be false in a sense if you can brute force expand the cases.

When you have something that can fail, every value you're manipulating is kind of `Option A`. In the monadic style, you have this `bind` operator `>>=` that handles the boilerplate of the `Option` so that your effectful functions have signature `a -> Option b`. It is somewhat compelling to me to just preapply `bind` to turn all your effectful functions to `Option a -> Option b` and now our expressions look normal instead of weird. For example, division by 0 could fail, but `add(div(x,y),z)` if we lift everything is fine. This is not really the algerbaic effects trick.

It is interesting to compare and contrast the get-set algebraic effects style with the SMT theory of arrays. They are pretty different. The theory of arrays thing is second nature to me at this point. Algerbaic effects is almost a complete hackery abuse of the notion of arity and that's neat.

Algerbaic effects is kind of a HOAS. We are using host enumeration to model embedded lambdas kind of

If we want to go bigger, we should think about how to go more symbolic, either via SMT style things or BDD style things. It is intriguing to think about smt returning a path in the tern as a model


I didn't get to the thrust of what I wanted but that's ok.

For bigger spaces, we should compact effects via smart constructors and memoization. BDDs (or generalizations thereof) of arguments for terms of arity 10^100. BDDs are spiritually functions / dicts. They are a form of compressed, memoized trie.


Terms have an ordered list of arguments. We typically think of a small number of arguments like `add(x,y)`. It makes the mind go interesting places to consider terms with 10^100 arguments. It requires no change to the conceptual foundations, but of course requires radically different data structure choices if they are to be feasibly manipulated. In particular, I have in mind a Binary Decision Diagram of children. 

Binary Decision Diagrams (BDD) are a compressed extensional representation of functions of the form `BitVec -> T` in a similar sense that a regular dictionary is also an extensional representation of functions `S -> T`. If there aren't too many different `T` values and the dependence on the bitvec argument isn't too complex, what would be a ridiculously huge dictionary might be a fairly compact BDD. BDDs are kind of a compressed interned Trie as bitvecs are keys that form a sequence.

One place this is actually possibly kind of useful is for algebraic effects. While one typically thinks of them as having lambda terms or continuations as children, it is perhaps feasible sometimes to instead extensionally expand / reify these lambdas into something more data structure like. The operators like `get`, `set`, `throw` etc which had one higher order lambda argument can be seen as actually an operator with a very very large number of first order arguments.

https://www.cs.cmu.edu/~emc/papers/Contributions%20to%20Edited%20Volumes/Multi-Terminal%20Binary%20Decision%20Diagrams%20and%20Hybrid%20Decision%20Diagrams.pdf MTBDD multi terminal binary decision diagrams


It's intriguing the idea that let bound variables at all are an effect. I've seen that in kiselyov's stuff. Sharing is a subtle thing. The subtlest thing maybe.

https://users.ece.cmu.edu/~gnb/Related%20Work_files/bryant92.pdf Restriction substitution cofactoring

Restrict = dump1/dump2. 

Lifting BDDs. BDDs are a little bit named. Named sucks

Wow, my old (last year) bdd sucks https://www.philipzucker.com/toy_bdd/ . This new one is way better.



```python
type V = int

def add(**kw : V) -> V:
    return kw["arg0"] + kw["arg1"]
def lit(p : int) -> V:
    return p

add(arg0=lit(1), arg1=lit(2))

```




    3



Ok, punning on keyword arguments is probably more confusing than clarifying. It forces me to make my keys be strings.


```python
from typing import Literal
type Bool = Literal["true"] | Literal["false"]
type Unit = Literal["tt"]
type V = dict[Bool, tuple[int, Bool]]

def get(**kw : V) -> V:
    return {"true" : kw["true"]["true"], "false" : kw["false"]["false"]} 
def set(b : Bool, **kw : V) -> V:
    res = kw["tt"][b]
    return {"true" : res, "false" : res}
def ret(i : int) -> V:
    return {b : (i, b) for b in ["true", "false"]}

def refl(k) -> V: # reflect a lambda on bool into a dict on Bool
    return {"true" : k(True), "false": k(False)}

get(**refl(lambda b: ret(3)))

def getk(k) -> V:
    return get(**refl(k))

getk(lambda b: ret(3))
set("true", tt=getk(lambda b: ret(3)))
```




    {'true': (3, 'true'), 'false': (3, 'true')}




```python


```




    {True: (3, True), False: (4, False)}



A lambda case construct is kind of a nice in between of the lambda picture and the keyword dict picture.
A full lambda case on a finitely enumerated type doesn't actually introduce any bound variables.




```python
def get(True=None, False=None): # does not work
    pass
```


      Cell In[16], line 1
        def get(True=None, False=None): # does not work
                ^
    SyntaxError: invalid syntax




```python
def get(argTrue=None, argFalse=None):
    pass
```


```python
def get(vTrue=None, vFalse=None):
    pass
```


```python

```

---
title: "Trie Terms: Arity 10^100 for Algebraic Effects"
date: 2026-07-24
---





```python
from dataclasses import dataclass

@dataclass
class App:
    f : str
    args : list["App"]
    def __repr__(self):
        return f"{self.f}({",".join(map(repr,self.args))})"
```

# Algebraic Effects

"Data" is somehow less mysterious to me than "computation". I do kind of have a feel for integers, lists, dicts, sets and don't feel like they are that mysterious. I don't even know what "computation" really is without somehow finding some kind of data to represent it. The environment data structure of an interpreter or emulator also does not seem that mysterious, being a dictionary of variables names or registers to the stuff held in those locations. Likewise a trace isn't that mysterious, being snapshots of this state over time. Traces can be at different levels of fine grained-ness. A fine grained trace might involve every logic gates, every single instruction or every subexpression or every line of code or every function call or every system call.

There are cool tools like `rr` which let you rerun seemingly stateful computation.



In temporal logic, there is a logic CTL which talks about computation trees.

fork based continuations





```python
class Cont:
    child_pid : int
    def __call__(self, arg):

# https://github.com/kmcallister/cccallcc

def callcc(f):
    pid = os.fork()
    if pid == 0:
        signal.signal(signal.SIGUSR1, handle_signal)
        # Sleep/pause until a signal arrives
        signal.pause()
        return
    else:
        f(Cont(child_pid=pid))
```

# Single Bit Get Set

For a single bit, we don't have to get fancy with our term.

Any operation that mutates a state can be modelled purely functionally as a function `State -> State`.

An operation that reads and writes state but also returns a result can be modelled as `State -> (Res, State)`.

If `State = bool` we have `(State -> State) ~ (State, State)` as evidenced by this pair of functions


```python
def to(s) -> tuple:
    return s(True), s(False)
def fro(t: tuple):
    return lambda b: t[0] if b else t[1]
assert to(fro((1,2))) == (1,2) # inverses of each other
assert to(lambda b : 1 if b else 2) == (1,2)
```

For some strange reason, I find this version the most intuitive to start from. The first part of the tuple is the resulting state if the current boolean state is `True` and the second part of the tuple is the result if the current state is `False`


```python
type V = tuple[tuple[int, bool], tuple[int, bool]]

def get(c1 : V, c2 : V) -> V:
    # Takes True world of first argument and False world of second argument
    x, _ = c1
    _, y = c2
    return (x, y)

def set(b : bool, c : V) -> V:
    # depending on b, picks one world to duplicate, one to throw away
    return (c[0], c[0]) if b else (c[1], c[1])

def ret(i : int):
    # Just passes along True/False
    return ((i, True), (i, False))

print("state = true in both worlds", set(True, ret(3)))
print("state = false in both worlds", get(set(False, ret(3)), ret(4)))
```

    state = true in both worlds ((3, True), (3, True))
    state = false in both worlds ((3, False), (4, False))


If I was going to try and describe that abstract idea of a theory of a commutative boolean operation add, I might show a final interpreter / model / denotation like so.

This is kind of more confusing because how circular and pointless it looks. But the above get/set interpretation doesn't feel so trivial and yet it is the saem sort of thing operating on a more complex `V`


```python
type V = int

def add(x : V, y : V) -> V:
    return x + y
def lit(x : int) -> V:
    return x

add(lit(3), lit(2))
```

Via the isomorphism it is the same as these combinators. This type smells more familiar to the monad minded.


```python
type V = Callable[[bool], tuple[int, bool]]

def get(c1 : V, c2 : V) -> V:
    return lambda b: c1(True) if b else c2(False)

def set(b : bool, c : V) -> V:
    return lambda b1: c(b) 

def ret(i : int):
    return lambda b: (i, b)

def refl(k):
    return (k(True,), k(False))

set(True, ret(3))

refl(get(set(False, ret(3)), ret(4)))
```




    ((3, False), (4, False))




```python
def getk(k) -> V:
    return lambda b: k(True)(True) if b else k(False)(False)
def getk(k) -> V:
    return lambda b: k(b)(b)
```


```python
type V = tuple[tuple[int, bool], tuple[int, bool]]

def get(c1 : V, c2 : V) -> V:
    x, _ = c1
    _, y = c2
    return (x, y)

def getk(k : Callable[[bool], V]) -> V:
    return (k(True)[0], k(False)[1])

def set(b : bool, c : V) -> V:
    return (c[0], c[0]) if b else (c[1], c[1])

def ret(i : int):
    # Just passes along True/False
    return ((i, True), (i, False))


getk(lambda b: set(False, ret(3)) if b else ret(4))
```




    ((3, False), (4, False))



This is talking about te same sort of thing as a monadic style, but it is precomposing bind in some ways with the operators.

# BDDs

Binary Decision Diagrams are kind of a hash cons with smart constructors. See the modular hash consing paper and previous blog post.

BDDs can be seen as if-then-else expressions with hash consing smart constructors that do the following
- `if b1 then (if b2 then x else y) else z -> if b2 (if b1 then x else z) (if b1 then y else z)` if b1 < b2 in a variable (term) ordering. This is smells like an ordered rewriting kind of thing (and likewise for the else branch)
- `if b then (if b then x else y) else z -> if b then x else z`
- `if b then x else x -> x`  node removal / compression

What happens during set and get smart constructors is we have an inversion 




```python
from dataclasses import dataclass, field
import functools
class Node: ...
@dataclass(frozen=True)
class Value(Node):
    f : object
@dataclass(frozen=True)
class ITE(Node):
    c : object
    t : int
    e : int
type Id = int
@dataclass
class IdRef:
    bdd : BDD
    idx : Id
    def __eq__(self, other):
        assert self.bdd is other.bdd
        return self.idx == other.idx
    def __repr__(self):
        return self.bdd.show(self.idx)
    def map(self, f):
        return self.bdd.map(self.idx, f)
    def extract(self):
        return self.bdd.extract(self.idx)

def If(vlabel : object, t : IdRef, e : IdRef) -> IdRef:
    bdd = t.bdd
    assert bdd is e.bdd
    return IdRef(bdd, bdd.ite(vlabel, t.idx, e.idx))


@dataclass
class BDD:
    nodes : list[Node] = field(default_factory=list)
    memo : dict[Node, Id] = field(default_factory=dict)

    def add(self, node : Node) -> Id:
        if node in self.memo:
            return self.memo[node]
        else:
            self.nodes.append(node)
            idx = len(self.nodes) - 1
            self.memo[node] = idx
            return idx
    def get(self, idx : Id) -> Node:
        return self.nodes[idx]

    def value(self, res : object) -> Id:
        return self.add(Value(res)) # change to Result? Return?
    def Result(self, res : object) -> IdRef:
        return IdRef(self, self.value(res))
    def proj_bool(self, vlabel : object) -> IdRef:
        return IdRef(self, self.ite(vlabel, self.value(True), self.value(False)))
    # def cases(self, scrutinee, *cs): -> Id
    def ite(self, c, t : Id, e : Id) -> Id:
        assert isinstance(e, int) and isinstance(t, int)
        if t == e: # if b then c else c = c
            return t
        #if c == True: # No this is a confusion of layers. c is a _variable label_, not the value it takes
        #    return t
        #if c == False:
        #    return e
        match self.get(t):
            case ITE(c1, t1, e1) if c1 == c:
                return self.ite(c, t1, e)
            case ITE(c1, t1, e1) if c1 < c:
                return self.ite(c1, self.ite(c, t1, e), self.ite(c, e1, e))
        match self.get(e):
            case ITE(c1, t1, e1) if c1 == c:
                return self.ite(c, t, e1)
            case ITE(c1, t1, e1) if c1 < c:
                return self.ite(c1, self.ite(c, t, t1), self.ite(c, t, e1))
        return self.add(ITE(c, t, e))
    def show(self, idx : Id) -> str: # indent_level=0. # print with fun env -> if env[] then .... lambda **kw: if kw[0] then ... 
        match self.get(idx):
            case Value(v):
                return str(v)
            case ITE(c, t, e):
                return f"if {c} then {self.show(t)} else {self.show(e)}" # TODO: let bind
    def map(self, idx: Id, f, join=False) -> Id:
        memo = {}
        def worker(idx: Id) -> Id:
            if idx in memo:
                return memo[idx]
            else:
                match self.get(idx):
                    case Value(v):
                        if join:
                            # join to collapse two bdd layers akin to monadic join of (BitVec -> T)
                            res = f(v)
                            assert isinstance(res, int)
                        else:
                            res = self.value(f(v))
                        memo[idx] = res
                        return res
                    case ITE(c, t, e):
                        res = self.ite(c, self.map(t, f), self.map(e, f))
                        memo[idx] = res
                        return res
        return worker(idx)
    # def map2(): # applicative of A -> B, A -> C
    def flatmap(self, idx: Id, f : Callable[[object], Id]) -> Id:
        self.map(idx, f, join=True)
    def extract(self, idx : Id) -> list[Node]:
        # extract a canonical compacted list of nodes
        # We don't want to just take self.nodes because we want a canonical traversal ordering
        # and there might be ids that aren't needed
        arena = []
        idmap = {}
        def worker(idx : Id) -> int:
            if idx in idmap:
                return idmap[idx]
            match (node := self.get(idx)):
                case Value(v):
                    newidx = len(arena)
                    arena.append(node)
                    idmap[idx] = newidx
                    return newidx
                case ITE(c, t, e):
                    newt = worker(t)
                    newe = worker(e)
                    newidx = len(arena)
                    arena.append(ITE(c, newt, newe))
                    idmap[idx] = newidx
                    return newidx
        worker(idx)
        return arena
    def insert(self, arena : list[Node]) -> Id:
        # insert an arena of nodes in topological order
        idmap = {}
        for idx, node in enumerate(arena):
            match node:
                case Value(v):
                    newidx = self.add(node)
                    idmap[idx] = newidx
                case ITE(c, t, e):
                    newidx = self.ite(c, idmap[t], idmap[e])
                    idmap[idx] = newidx
        return idmap[len(arena) - 1]
h = BDD()
seven, fred = h.Result(7), h.Result("fred")


print(If("v1", seven, fred))
print(If("v2", If("v1", fred, seven), seven))

"""
h.show(h.ite("v2", h.ite("v1", fred, seven), seven))
h.show(h.ite("v1", h.ite("v2", fred, seven), seven))
t = h.ite("v1", h.ite("v2", fred, seven), seven)
h.extract(h.ite("v1", h.ite("v2", fred, seven), seven))
assert h.insert(h.extract(t)) == t

h.show(h.map(h.ite("v1", h.value("fred"), h.value("gary")), lambda x: x.upper()))
"""
```

    if v1 then 7 else fred
    if v1 then if v2 then fred else 7 else 7





    '\nh.show(h.ite("v2", h.ite("v1", fred, seven), seven))\nh.show(h.ite("v1", h.ite("v2", fred, seven), seven))\nt = h.ite("v1", h.ite("v2", fred, seven), seven)\nh.extract(h.ite("v1", h.ite("v2", fred, seven), seven))\nassert h.insert(h.extract(t)) == t\n\nh.show(h.map(h.ite("v1", h.value("fred"), h.value("gary")), lambda x: x.upper()))\n'



# BDDs of Children


```python
bdd = BDD()
@dataclass
class App:
    f : str
    #bdd : BDD. We'll use a global BDD for convenience.
    args : Id




```

type V = BitVec -> (int, BitVec) use bdd to represent 
factor to `type V = (BitVec -> int, BitVec -> BitVec) And then further break about
type V = {res : BDD, bv : [BDD]}
type V = (Id, list[Id])

# BDD Semantics

`type V = tuple[dict[K,Res], dict[K,K]]` spiritually. But the Id


```python
type V = tuple[Id, list[Id]]

@dataclass
class IdState:
    


bdd = BDD()

N = 100
def get(refid, k) -> V:
    (v1, bv1),(v2,bv2) = k(True), k(False)
    #bv1[refid] = bdd.value(True)
    #bv2[refid] = bdd.value(False)
    #v1.assume(refid)
    #v2.assume(refid)
    v = bdd.ite(refid, v1, v2)
    bv = [bdd.ite(refid,x,y) for x,y in zip(bv1,bv2)]
    return v, bv

def set(refid, b : bool, v : V) -> V:
    (v, bv) = v
    bv[refid] = bdd.value(b)
    return (v, bv)

def proj(refid): # projection function  x,y,z -> y
    return bdd.ite(refid, bdd.value(True), bdd.value(False))
def ret(i) -> V:
    return (bdd.value(i), [proj(refid) for refid in range(N)])

bdd.show(ret(3)[1][0])
bdd.show(get(0, lambda b: set(1, b, ret(0)))[1][1])

```




    'if 0 then True else False'




```python
1 == True # Python you crazy
```




    True




```python
type V = Id

bdd = BDD()
def get(refid, k) -> V:
    return bdd.ite(refid, k(True), k(False))
def set(refid, x, v : V) -> V:
    


```

# Bits and Bobbles

Huh, Adding liftings to BDD ought to achieve more compression sometimes. If there are sort of localized subpatterns.


It is really fun when you end up realizing there is some parameter you assumed without thinking was small but can also be made very big.

An example of this is in Database queries. We're used to databases being big and queires being small or medium. Very small databases and very large queries turns the problem into one that feels like constraint satisfaction.
link to CSP post

Terms are roughly


Interaction trees
Command and Response trees



https://www.youtube.com/watch?v=JbnjusltDHk
`let rec gobs_prog _ = print("butt"); gobs_prog()`

print ~ Writer Monad
Trace semantics
`["butt"], ["butt","butt"], ...`
vs
result semantics
`["butt","butt", ...]`



And in our head we're kind of thinking of `add(x,y)`, `mul(add(x,y),z)`, `ifthenelse(c, t, e)` and stuff like that. `args` is usually of length 0,1,2, or 3. Length 4 starts to get rare.

There is a general phenomenon really that to our guts there is 0,1,2,3,4,5, the kind of 10s-ish, 100-ish, 1000-ish. We can intuitively feel very small integers. I can count 4 things at a glance without a counting process. Then we sort of can get orders of magntidue. And then eventually we kind of can feel orders of orders of magnitude. `10^-23` is so small or `10^80` is so big I kind of only can grasp the `80`.

Another place this shows up in is vectors. We are usually first taught about vectors as little arrows, 2 and 3 dimensional vectors. Sometimes 4 or 5 dimensional vectors show up in projective algebra, geometric algebra and relativity.

Then you jump up to 1000 dimension vectors. These sorts of things are useful for parametrizing 1-dimensional functions for the purpsoes of solving differential equations. It's quite an abstract analogy when you first hear it.

Then there are 10^10 etc vectors which show up if you discretize 3d/4d space.

Even larger vectors conceptually show up in probability/amplitude distributions on many degrees of freedom, such as in multi particle quantum mechanics or reinforcement learning.




```python
# state = Int mod 3

N = 10
type V = tuple[tuple[int, int], tuple[int, int], tuple[int, int]]

def get(k) -> V:
    return tuple(k(i)[i] for i in range(N))
def set(j : int, v : V) -> V:
    return tuple([v[j % N]]*N)
def ret(j : int):
    return tuple((j, i) for i in range(N))

# get then increment. "Reflection" from state over into value.
get(lambda j: set(j + 2, ret(j)))
get(lambda j: ret(j))

```




    ((0, 0),
     (1, 1),
     (2, 2),
     (3, 3),
     (4, 4),
     (5, 5),
     (6, 6),
     (7, 7),
     (8, 8),
     (9, 9))




```python
type V = dict[object, tuple[object,object]]

def get(keys, k) -> V:
    return {key : k(key)[key] for key in keys}
def set(key, v : V) -> V:
    return {key1: (x,key) for key1,(x, key2) in v.items()}
def ret(keys, i):
    return {key : (i, key) for key in keys}
BOOL = {True, False}
get(BOOL, lambda b: ret(BOOL, 3) if b else set(False, ret(BOOL, 4)))

```




    {False: (4, False), True: (3, True)}




```python
# Terms with keyword args. `get` has args like this. set
@dataclass
class App:
    f : str
    args : dict[object,"App"]

x,y = App("x", {}), App("y", {})
App("add", {0 : x, 1: y})

def get(k):
    App("get", {True : k(True)[True], False : k(False)[False] })

```




    App(f='add', args={0: App(f='x', args={}), 1: App(f='y', args={})})



Choose. Nondeterminsim. A different way to use BDDs


```python
type V = dict[tuple[bool,...], int]

def choose(k : Callable[[bool], V]) -> V:
    res = {(True,) + key : v for key, v in k(True).items()}
    res.update({(False,) + key : v for key,v in k(False).items()})
    return res
def ret(i) -> V:
    return {() : i}



choose(lambda b1: choose(lambda b: ret(1) if b and b1 else ret(2)))
choose(lambda b1: ret(3) if b1 else choose(lambda b2: ret(4)))
```




    {(True,): 3, (False, True): 4, (False, False): 4}




```python
# choose(x,x) -> x. If we implement choose differently in a compressive way.
def choose(k : Callable[[bool], V]) -> V:
    res1,res2 = k(True), k(False)
    if res1 == res2:
        return res1
    else:
        return  {**{(True,) + k: v for k,v in res1.items()}, **{(False,) + k: v for k,v in res2.items()}}
```


```python
type V = dict[tuple[bool, ...], tuple[float, int]] # probability
def choose(p : float, k : Callable[[bool], V]) -> V:
    res = {(True,) + key : (p*p1, v) for key, (p1,v) in k(True).items()}
    res.update({(False,) + key : ((1-p)*p2, v) for key,(p2, v) in k(False).items()})
    return res
# Can also do in compressive way. Use 
```

A different BDD. It also needs to maintain a interned Value id -> probability index?
Or factored BitVec -> Prob, BitVec -> Value ? Random variable is Omega -> Val, Dist is measure Omega -> R

Omega is like manifold M. "coordinates" are the generating random variables Omega -> Bool. 

Memoize choose(k) so that we don't actually have to traverse tree for conversion?

If you have

`State -> (Res, State)`
`type State = Bool`

`Bool -> (Res, Bool) ~ ((Res, Bool), (Res,Bool))` because you can tabulate the function.


```python


```




    ((3, False), (4, False))




```python

```




    ((3, False), (4, False))



It is not that pleasant as a user to list out all the cases. Using host language lambdas and if then else is kind of nicer. Smart constructors can swtich between them


```python
def get(k : Callable[[bool], App]) -> App:
    return App("get", [k(True), k(False)])

def set(b : bool, c : App) -> App:
    return App("set", [b, c])

def ret(i : int) -> App:
    return App("ret", [i])
get(lambda b: set(False, ret(3)) if b else ret(4))
get(lambda b: set(False, ret(3) if b else ret(4)))

```




    get(set(False,ret(3)),set(False,ret(4)))



Smart constructors



```python
def get(k : Callable[[bool], App]) -> App:
    # get(get(a,b), x) = get(a, x) 
    match (ctrue := k(True)):
        case App("get", [c1,c2]):
            ctrue = c1
    # get(x, get(a,b)) = get(x, b)
    match (cfalse := k(False)):
        case App("get", [c1,c2]):
            cfalse = c2
    return App("get", [ctrue, cfalse])

def set(b : bool, c : App) -> App:
    match c:
        case App("set", [_, _]): # This current set is redundant. set(b1, set(b2, c)) = set(b2, c)
            return c
        case App("get", [c1, c2]): # get receives current b. We're wasting energy to evaluate all of get btw.
            return set(b, c1 if b else c2) # loop to maybe do more compression. terminates because we are on a subterm

def ret(i : int) -> App:
    return App("ret", [i])

get(lambda b: get(lambda b1: ret(3) if b else ret(4) if b1 else ret(5)))
set(True, get(lambda b: ret(3) if b else ret(4)))

```




    set(True,ret(3))






```python


```




    'if v1 then FRED else GARY'




```python
@dataclass
class App:
    f : str
    bdd : BDD
    args : Id

```


```python
@dataclass(frozen=True)
class App:
    f : str
    arena : tuple[Node,...]
```


```python
from dataclasses import dataclass, field
@dataclass(frozen=True)
class Node:
    f : object
    args : tuple[int,...]


@dataclass
class HashCons[T]:
    nodes : list[T] = field(default_factory=list)
    memo : dict[T, int] = field(default_factory=dict)

    def add(self, node : T) -> int:
        if node in self.memo:
            return self.memo[node]
        else:
            self.nodes.append(node)
            idx = len(self.nodes) - 1
            self.memo[node] = idx
            return idx
    def get(self, idx : int) -> T:
        return self.nodes[idx]

    def const(self, name : str) -> int:
        return self.add(Node(name, ()))

    def ite(self, c, t : int, e : int) -> int:
        if t == e: # if b then c else c = c
            return t
        if c == True:
            return t
        if c == False:
            return e
        match self.get(t):
            case Node("ite", [c1, t1, e1]) if c1 == c:
                return self.ite(c, t1, e)
            case Node("ite", [c1, t1, e1]) if c1 < c:
                return self.ite(c1, self.ite(c, t1, e), self.ite(c, e1, e))
        match self.get(e):
            case Node("ite", [c1, t1, e1]) if c1 == c:
                return self.ite(c, t, e1)
            case Node("ite", [c1, t1, e1]) if c1 < c:
                return self.ite(c1, self.ite(c, t, t1), self.ite(c, t, e1))
        return self.add(Node("ite", (c, t, e)))
    def show(self, idx : int) -> str:
        match self.get(idx):
            case Node("ite", [c, t, e]):
                return f"if {c} then {self.show(t)} else {self.show(e)}"
            case Node(name, []):
                return name
            
h = HashCons()
true, false = h.const("true"), h.const("false")
h.show(h.ite("v1", true, true))

```




    'true'



BitVec -> BitVec -> x  take the diagonal. We're kind of mapping under the ite?

get()


If everything is concrete, just like the python evaluator, if we do all rewrites, we ought to end up with `get(?set(ret), ?set(ret)) normal form.

It isn't really magical. We are basically enumerating every evaluation path in order to construct term.

BDDs are both symbolic and not. Spiritually, they are kind of evaluating every path way / boolean combination. In the worst case, constructing them is does this.

Cyclic terms using these sorts of enumerated algebraic effects are quite a bit like finite automata.



```python
type V = Callable[[bool], tuple[int, bool]]

# refactor to make b take a continuation
def get(k : Callable[[bool], V]) -> V:
    return lambda b: k(b)(b)

# set should take a thunk continuation for consistency?
def set(b : bool, c : V) -> V:
    return lambda b1: c(b) 

def ret(i : int):
    return lambda b: (i, b)

def refl(k):
    return (k(True,), k(False))

set(True, ret(3))

refl(get(lambda b: set(False, ret(3)) if b else ret(4)))
```




    ((3, False), (4, False))




```python
def getk(k : Callable[[bool], tuple[int, bool]]) -> 
```


```python
from typing import Callable
type S = Callable[[bool], tuple[int, bool]]
def refl(v : V) -> S:
    return lambda b: v[0] if b else v[1]
def reify(s : S) -> V:
    return (s(True), s(False))
def getk(k : S) -> tuple[int, bool]:
    return k
def setk(b : bool, k : S) -> S:
    return lambda b1: k(b)
def ret(i : int) -> S:
    return lambda b: (i, b)

reify(getk(lambda b: ret(1) if b else ret(2)))

```




    (<function __main__.ret.<locals>.<lambda>(b)>,
     <function __main__.ret.<locals>.<lambda>(b)>)




```python

# monad
def getm() -> S:
    return lambda b: (b,b)
def setm(b : bool) -> S:
    return lambda b1: (-1, b)
def bind(x, f):
    return lambda b: f((r := x(b))[0])(r[1])


```


```python
import kdrag as kd
import kdrag.smt as smt



```



https://www.youtube.com/watch?v=giSaeD8R_E8

1 bit state. That's a good example.
error()




```python
from dataclass import dataclass

@dataclass
class App:
    f : str
    args : list["App"]
```

IdRef does make things nicer. But it's nice to have the rawer version


```python
from dataclasses import dataclass, field
import functools
class Node: ...
@dataclass(frozen=True)
class Value(Node):
    f : object
@dataclass(frozen=True)
class ITE(Node):
    c : object
    t : int
    e : int
type Id = int
class IdRef:
    bdd : BDD
    idx : Id
    def __eq__(self, other):
        assert self.bdd is other.bdd
        return self.idx == other.idx
    def __repr__(self):
        return self.bdd.show(self.idx)
    def map(self, f):
        return self.bdd.map(self.idx)

@dataclass
class BDD:
    nodes : list[Node] = field(default_factory=list)
    memo : dict[Node, Id] = field(default_factory=dict)

    def add(self, node : Node) -> Id:
        if node in self.memo:
            return self.memo[node]
        else:
            self.nodes.append(node)
            idx = len(self.nodes) - 1
            self.memo[node] = idx
            return idx
    def get(self, idx : Id) -> Node:
        return self.nodes[idx]

    def value(self, v : object) -> Id:
        return self.add(Value(v))
    # def cases(self, scrutinee, *cs): -> Id
    def ite(self, c, t : Id, e : Id) -> Id:
        assert isinstance(e, int) and isinstance(t, int)
        if t == e: # if b then c else c = c
            return t
        #if c == True: # No this is a confusion of layers. c is a _variable label_, not the value it takes
        #    return t
        #if c == False:
        #    return e
        match self.get(t):
            case ITE(c1, t1, e1) if c1 == c:
                return self.ite(c, t1, e)
            case ITE(c1, t1, e1) if c1 < c:
                return self.ite(c1, self.ite(c, t1, e), self.ite(c, e1, e))
        match self.get(e):
            case ITE(c1, t1, e1) if c1 == c:
                return self.ite(c, t, e1)
            case ITE(c1, t1, e1) if c1 < c:
                return self.ite(c1, self.ite(c, t, t1), self.ite(c, t, e1))
        return self.add(ITE(c, t, e))
    def proj_bool(self, c) -> Id:
        return self.ite(c, self.value(True), self.value(False))
    def show(self, idx : Id) -> str:
        match self.get(idx):
            case Value(v):
                return str(v)
            case ITE(c, t, e):
                return f"if {c} then {self.show(t)} else {self.show(e)}" # TODO: let bind
    def map(self, idx: Id, f, join=False) -> Id:
        memo = {}
        def worker(idx: Id) -> Id:
            if idx in memo:
                return memo[idx]
            else:
                match self.get(idx):
                    case Value(v):
                        if join:
                            # join to collapse two bdd layers akin to monadic join of (BitVec -> T)
                            res = f(v)
                            assert isinstance(res, int)
                        else:
                            res = self.value(f(v))
                        memo[idx] = res
                        return res
                    case ITE(c, t, e):
                        res = self.ite(c, self.map(t, f), self.map(e, f))
                        memo[idx] = res
                        return res
        return worker(idx)
    # def map2(): # applicative of A -> B, A -> C
    def flatmap(self, idx: Id, f : Callable[[object], Id]) -> Id:
        self.map(idx, f, join=True)
    def extract(self, idx : Id) -> list[Node]:
        # extract a canonical compacted list of nodes
        # We don't want to just take self.nodes because we want a canonical traversal ordering
        # and there might be ids that aren't needed
        arena = []
        idmap = {}
        def worker(idx : Id) -> int:
            if idx in idmap:
                return idmap[idx]
            match (node := self.get(idx)):
                case Value(v):
                    newidx = len(arena)
                    arena.append(node)
                    idmap[idx] = newidx
                    return newidx
                case ITE(c, t, e):
                    newt = worker(t)
                    newe = worker(e)
                    newidx = len(arena)
                    arena.append(ITE(c, newt, newe))
                    idmap[idx] = newidx
                    return newidx
        worker(idx)
        return arena
    def insert(self, arena : list[Node]) -> Id:
        # insert an arena of nodes in topological order
        idmap = {}
        for idx, node in enumerate(arena):
            match node:
                case Value(v):
                    newidx = self.add(node)
                    idmap[idx] = newidx
                case ITE(c, t, e):
                    newidx = self.ite(c, idmap[t], idmap[e])
                    idmap[idx] = newidx
        return idmap[len(arena) - 1]
h = BDD()
seven, fred = h.value(7), h.value("fred")
h.show(h.ite("v1", fred, seven))
h.show(h.ite("v2", h.ite("v1", fred, seven), seven))
h.show(h.ite("v1", h.ite("v2", fred, seven), seven))
t = h.ite("v1", h.ite("v2", fred, seven), seven)
h.extract(h.ite("v1", h.ite("v2", fred, seven), seven))
assert h.insert(h.extract(t)) == t

h.show(h.map(h.ite("v1", h.value("fred"), h.value("gary")), lambda x: x.upper()))
```
