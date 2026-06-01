---
title: Arenas, Cyclic Terms, and Flat Equational Systems
date: 2026-06-01
---

I was invited a few months ago into discussions with Cheng Zhang, Sam Coward and Alexandra Silva on some work integrating loopy infinite streamy things into e-graphs. A few years back, I was barking up a similar but distinct tree <https://www.philipzucker.com/coegraph/>

Cheng will presenting at EGRAPHS 2026 <https://pldi26.sigplan.org/details/egraphs-2026-papers/12/From-Rewriting-to-Fixpoints-Solving-Recursive-Equations-with-E-Graphs> Come check it out!

One interesting aspect of the discussion has been my confusion of where they are even coming from. There is some formalistic perspective on what a co-term / cyclic term / rational term is that I'm still trying to unpack.

To me, it is somewhat natural that you can talk about loopy terms like `zeros := Cons(0, zeros)` as a little picture

<https://softwarepreservation.computerhistory.org/prolog/marseille/doc/Colmerauer-InfTree-1982.pdf> PROLOG AND INFINITE TREES - Alain Colmerauer

![](/assets/rational_tree.png)

But a picture does not quite code nor rigorous math make (Welllllll... Diagrammatic reasoning can be as legit as any other form of reasoning or syntax. But I still feel like I need to know how to translate the diagrams to something more formula and code-like). You kind of need a story about how to represent this in a system you can actually work with, say ZFC or python or lean or what have you.

I think there is a somewhat natural journey starting from a basic term datatypes, turning that into an arena datatype, and then removing the condition of acyclicity of nodes in the arena. <https://docs.rs/egg/latest/egg/struct.RecExpr.html> "RecExprs must satisfy the invariant that enodes’ children must refer to elements that come before it in the list. "

That is a implementation flavored explanation of what a co-term / cyclic / rational term / equation system even is.

Then we can talk about some of the things we like to do with terms and how to generalize that to rational terms:  

- interpret them
- rewrite them
- store sets of them
- insert them into e-graphs
- extract them from e-graphs

I don't get all the way there on this post by any means, but it's a start!

# Basic Terms

A basic term data type (a finite well founded tree with ordered children) might look like this

```python
from dataclasses import dataclass, field

@dataclass
class Term:
    f : str
    args : list["Term"]

Term("f", [Term("a", [])]) # f(a)
("f", ("a", )) # Basically the same thing using tuples. It can be lighter weight to do it this way.
```

# Arena Terms

There is a different style which is sometimes pleasant to use. Here we used python references to refer to our children. Instead we could keep all the data of the term in a list and have our own index system. These are kind of our own special pointers

```python
from dataclasses import dataclass, field
from pprint import pprint
type Id = int

@dataclass
class Node:
    f : str
    args : list[Id] # Arguments are indirectly referred to by id

@dataclass
class Arena():
    data : list[Node] = field(default_factory=list)
    def app(self, f : str, *args : Id) -> "TermRef":
        self.data.append(Node(f, list(args)))
        return TermRef(len(self.data) - 1, self)
    #def reserve(self):
    #    self.

@dataclass
class TermRef:
    # Bundling an id with it's arena store makes it easier to use.
    # You can do operator overloading for example.
    id : Id
    arena : Arena

    def __add__(self, other : TermRef) -> TermRef:
        assert self.arena is other.arena
        return self.arena.app("+", self.id, b.id)

A = Arena()
one = A.app("lit", 1)
two = A.app("lit", 2)
pprint(one + two)

```

Many systems do this. Using the regular allocator (malloc) has a cost. Fine grained memory management has a cost. An arena (bump allocation) is one of the fastest and simplest forms of memory allocation. Having it all there in a single block is also good for caches.

See also

- This corresponds to egg's RecExpr <https://docs.rs/egg/latest/egg/struct.RecExpr.html>
- <https://www.cs.cornell.edu/~asampson/blog/flattening.html> Flattening ASTs (and Other Compiler Data Structures)
- Twee's description of it's flat terms <https://smallbone.se/papers/twee.pdf> section 4.1
- Handbook of automated reasoning  <https://dl.acm.org/doi/10.5555/778522.778535>
- <https://link.springer.com/article/10.1007/BF00881866> Flatterms, Discrimination Nets, and
Fast Term Rewriting

# Cyclic Arena Terms

It is not necessary to use Arena style to build cyclic terms, but it does make it feel less weird somehow to me.

To make cyclic terms, you often need a way to "tie the knot" (Landin's knot specifically refers to achieving recursion, not this?).

```python
t = [None]
t[0] = t
t
```

    [[...]]

This requires something kind of like mutation. Logic variables, like in prolog, also enable you to do this, because logic variables are kind of "assign once" variables <https://web.archive.org/web/20221003021352/https://www3.cs.stonybrook.edu/~warren/xsbbook/node5.html> , which is a bit more principled than write as many times as you like variables.

By giving the arena an interface to `makevar` and `define`, we can make this less spooky.

```python
from dataclasses import dataclass, field
from pprint import pprint
type Id = int

@dataclass
class Node:
    f : str
    args : list[Id] # Arguments are indirectly referred to by id

@dataclass
class Arena():
    data : list[Node | None] = field(default_factory=list)

    def makevar(self):
        self.data.append(None)
        return len(self.data) - 1
    def define(self, x : Id, body : Node):
        assert self.data[x] is None
        self.data[x] = body
    def app(self, f : str, *args : Id) -> "TermRef":
        x = self.makevar()
        self.define(x, Node(f, list(args)))
        return TermRef(x, self)

@dataclass
class TermRef:
    id : Id
    arena : Arena

    def __add__(self, other : TermRef) -> TermRef:
        assert self.arena is other.arena
        return self.arena.app("+", self.id, b.id)

A = Arena()
one = A.app("lit", 1)
two = A.app("lit", 2)
pprint(one + two)

```

    TermRef(id=2,
            arena=Arena(data=[Node(f='lit', args=[1]),
                              Node(f='lit', args=[2]),
                              Node(f='+', args=[0, 1])]))

We can make a cyclic term

```python
A = Arena()
z = A.app("0")
zeros = A.makevar()
A.define(zeros, Node("cons", [z.id, zeros]))
pprint(A)

```

    Arena(data=[Node(f='0', args=[]), Node(f='cons', args=[0, 1])])

But we can also make non cyclic terms in such a way that they are no longer topologically sorted in the arena.

```python
A = Arena()
fa = A.makevar()
a = A.makevar()
A.define(fa, Node("f", [a])) # f(A)
A.define(a, Node("a", [])) # a
pprint(A)
```

# Flat Equation Systems

The arena can be viewed in a more logical looking light by considering it to represent a formal equation system. The index 47 in the arena represents a variables $x_{47}$ and the entry represents something like the equation $x_{47} := foo(x_{32}, x_{45})$. In other words, the arena represents a `Var -> Node<Var>` mapping.

```
The arena 

[Term("a", []), Term("f", [0])]

is kind of the same as the flat equation system

x0 := a
x1 := f(x0) 
```

- <https://www8.cs.fau.de/ext/milius/phd/AMV1.pdf> Free iterative theories: a coalgebraic view. Section: What is a rational tree?
- <https://jeannin.github.io/papers/capsules-journal.pdf>
- <https://jeannin.github.io/papers/nwf.pdf> Language Constructs for Non-well-Founded Computation
- <https://mcrl2.org/web/user_manual/language_reference/bes.html> Boolean equation systems. Related?

In a funny way, the arena form has exposed a very light and limited form of variable. We have not discussed any notion of alpha invariance for this notion of variable, but any arena with the indices shuffled ought to be basically the same thing. In a sense, this notion of variable which is sufficient to described cyclic terms is the thing the e-graph with fixed points is trying to support. These variables are also pretty much that same thing as an eid, but some distinctions have to be made and careful understanding of the semantics to stay sound.

# Interpreting

The is nothing so far inductive or coinductive about what we've discussed. It is just some data. A formal structure. I think that comes in when we start discussing what we want the thing to mean and how different arenas may relate to each other.

For ordinary terms, we can define an interpretion by writing a recursive function

```python
def interp(e) -> int:
    match e:
        case ("+", a, b):
            return interp(a) + interp(b)
        case ("lit", a):
            return a
interp(("+", ("lit", 1), ("lit", 2)))
```

    3

We could do the same top down recursive thing for well founded arena terms, but now the opportunity to instead perform interpretation bottom up presents itself.

If the arena is in a topologically sorted order, we could interpret using a single bottom up sweep.

But the new api doesn't persay guarantee that. Instead we have to iterate to a fixed point. The reason we're thinking about it this way is because the same methodology works for cyclic arena terms as well.

For equation systems, it is pretty natural to interpret the system as representing a single step of some iteration. The equational system is kind of in the form $x_{t+1} := A x_{t}$

This means that the natural thing to interpret it into is a `Env -> Env` function where `Env` is a mapping of semantics values to variable names `type Env = Var -> T`

```python
type Env = list[int] # Var -> T
def interp(A : Arena, cur : Env) -> Env:
    next = []
    for node in A.data:
        match node:
            case Node("+", [a,b]):
                next.append(cur[a] + cur[b])
            case Node("lit", [n]):
                next.append(n)
            case _:
                raise ValueError("unexpected Node")
    return next
```

Note the similarities and differences to the following standard recursive semantics of simple terms with variables. If our expressions contain variables a typical semantics would be one that is environment dependent `Env -> int`. However, it would not also return an environment

```python
def interp(e, env : dict[str, int]) -> int:
    match e:
        case ("+", a, b):
            return interp(a, env) + interp(b, env)
        case ("lit", a):
            return a
        case ("var", x):
            return env[x]
```

# Fixed Point Interpretations

While the basic interpretation of arena terms is `Env -> Env`, whenever there is ever a function whose domain is the same as it's codomain, it is also possible to talk about it's set of fixed points, and possibly it's minimal, maximal, or unique fixed point. <https://en.wikipedia.org/wiki/Fixed_point_(mathematics)>

```python
def interp(A : Arena) -> list[int]:
    res = [None] * len(A.data)
    while True:
        done = True
        for i, node in enumerate(A.data):
            if res[i] is not None:
                continue
            match node:
                case Node("+", [a,b]):
                    if res[a] is not None and res[b] is not None:
                        res[i] = res[a] + res[b]
                        done = False
                case Node("lit", [a]):
                    res[i] = a
                    done = False
        if done:
            return res
    
A = Arena()
plusonetwo = A.makevar()
one = A.app("lit", 1)
two = A.app("lit", 2)
A.define(plusonetwo, Node("+", [one.id, two.id]))
interp(A)
```

    [3, 1, 2]

A particularly interesting interpretation is one that builds tuple trees out of the arena trees.

```python
def extract(a : Arena) -> tuple: # Interpreting into ordinary tuple terms is a non lossy interpretation
    terms = [None]*len(a.data)
    while True:
        done = True
        for i, n in enumerate(a.data):
            if n is None:
                continue
            if terms[i] is None and all(terms[j] is not None for j in n.args):
                terms[i] = (n.f, *[terms[j] for j in n.args])
                done = False
        if done:
            return terms

A = Arena()
fa = A.makevar()
a = A.makevar()
A.define(fa, Node("f", [a])) # f(A)
A.define(a, Node("a", [])) # a
extract(A)
```

    [('f', ('a',)), ('a',)]

# Equality of Arena Terms

Determining which entries are equal to the other entries in a syntactic sense is also not necessarily straightforward. For ordinary terms we'd do something like this:

```python
def eq(e,e2) -> int:
    match e,e2:
        case ("+", a, b), ("+", a2, b2):
            return eq(a,a2) and eq(b,b2)
        case ("lit", a), ("lit", a2):
            return a == a2
```

Note that if we have a cyclic term, this program would not terminate. We could fix that by remember a trail of what ids we've seen before or looking up into our stack. The arena has to confront this problem head on, but because of that does it more naturally IMO.

We can define pessimistic and optimistic equality. Disequal until proven equal vs equal until proven disequal. Both are legit definitions. In some sense pessimistic requires a well founded congruence proof that the two ids are equal. It is inductive-y least fixed pointy somehow. I can't say that I see it very crisply. A Union find would give some speedup perhaps.

If you have a loop in your arena, pessimistic equality won't even find that it is equal to itself. That's kind of odd.

```python
def pess_eq(a : Arena, b : Arena):
    eq = [[False]*len(b.data) for i in range(len(a.data))]
    while True:
        done = True
        for i in range(len(a.data)):
            for j in range(len(b.data)):
                if eq[i][j]: continue
                match a.data[i], b.data[j]:
                    case Node(fa, argsa), Node(fb, argsb) if fa == fb and len(argsa) == len(argsb):
                        if all(eq[ai][bi] for ai, bi in zip(argsa, argsb)):
                            eq[i][j] = True
                            done = False
        if done:
            return eq

A = Arena()
fa = A.makevar()
a = A.makevar()
A.define(fa, Node("f", [a])) # f(A)
A.define(a, Node("a", [])) # a

pess_eq(A,A)
```

    [[True, False], [False, True]]

Optimistic equality is saying the two trees are bisimilar. They are equal until proven unequal. Partition refinement would perhaps given a faster algorithm.

```python
def opt_eq(a : Arena, b : Arena):
    eq = [[True]*len(b.data) for i in range(len(a.data))]
    while True:
        done = True
        for i in range(len(a.data)):
            for j in range(len(b.data)):
                if not eq[i][j]: continue
                match a.data[i], b.data[j]:
                    case Node(fa, argsa), Node(fb, argsb) if fa != fb or len(argsa) != len(argsb) or any(not eq[ai][bi] for ai, bi in zip(argsa, argsb)):
                            eq[i][j] = False
                            done = False
        if done:
            return eq

A = Arena()
fa = A.makevar()
a = A.makevar()
A.define(fa, Node("f", [a])) # f(A)
A.define(a, Node("a", [])) # a

opt_eq(A,A)
        
```

    [[True, False], [False, True]]

# Bits and Bobbles

Well, I wrote something.

I am having a hard time making a nice cohesive story with well backed code snippets. I think I'm feeling generally a little burnt out these days, so that probably ain't helping.

Maybe a good starting point to juicier topics? I don't know how to attack all this. That is why bit sized posts are good.

Rereading through my notes, they make not that much sense. And I'm not sure what I wrote above makes that much sense either.

- Rewriting of arena terms
- Hash consing
- Bisimulation
- Sets of arena terms. Factoring into VSA / Multiterms. <https://www.philipzucker.com/smart_constructor_aegraph/>  Aegraphs
- Productivity. What is the different between constructors and non constructors? Causality. <https://www.cl.cam.ac.uk/~nk480/frp-lics11.pdf>
- What are loops in an e-graph
- Egraphs as equational systems `eclasses : Var -> Set<Node<Var>>>` Multi-equations? Quite similar notion to Grechanik's polyprograms <https://www.mathnet.ru/links/bf0adfca50e9ba6e89a63640700a21d1/mais647.pdf>
- Sergei A Grechanik. 2015. Proving properties of functional programs by equality saturation. <https://persons.iis.nsk.su/files/persons/pages/step05_12may23sergeygrechanik.pdf>
- Top Down Extraction
- `:=` and `=` judgements as distinct
- Congruence closure with loopy proof trees
- named eclasses as a seperate namespace from enode constants. Like a lisp-2 kind of. egglog's let should be `define`. `define-rec`?
- <https://arxiv.org/abs/2306.10009> extracting systems of equations
- To some degree, the e-graph with fixed point is trying to remove the restriction on RecExpr that they need to be well founded. Insertion and extraction neither should require it. But also `1*x = x` is not the same kind of loop as `zeros := cons(0, zeros)`.
- Homomorphisms of arenas into the egraph is non mutating lookup of the arena in the egraph. Again, insertion of a term is an asy recursive function, but we can't guarantee that so easily

There is some goofiness with these "equalities". It is not obvious that you will even have reflexivity for pessimistic equality.  Maybe that's ok. Maybe it's a kleene equality. <https://en.wikipedia.org/wiki/Kleene_equality>

```python
@dataclass(frozen=True)
class MultiNode():
    f : str
    args : tuple[frozenset[Id], ...]

type MultiEnv = dict[Id, frozenset[Node]]
```

Kind of looks like a non well founded set.

```
fix(T) -> fixsubst(T,fix(T))
fixsubst(Hole, t) -> t
fixsubst(Cons(a, tail), t) -> Cons(a, fixsubst(tai,t))
```

```
struct Obs<T> { constructor : Option<Node<T>>, enodes : HashSet<Node<T>>}
struct CoEgraph {comemo : HashMap<Id, Obs<Id>> } // eclasses basically.

// vs
struct Enode {
    f : str,
    args : Vec<Id>
    is_constr : bool
}
struct Egraph {eclasses : HashMap<Id, Vec<ENodes>>}
```

title: Term and Co-Terms, Egraphs and Co-Egraphs

I was invited a few months ago into discussions with Cheng Zhang, Sam Coward and Alexandra Silva on some work they had started on integrating loopy infinite streamy things into e-graphs. A few years back, I was barking up a similar but distinct tree to the one they were working on <https://www.philipzucker.com/coegraph/>

Cheng will be giving a talk next month <https://pldi26.sigplan.org/details/egraphs-2026-papers/12/From-Rewriting-to-Fixpoints-Solving-Recursive-Equations-with-E-Graphs> on the topic, so it's no big secret. He has a much more mathematical perspective on things, so I'd like to lay down my doofus perspective both for myself and others.

# Terms, Flat Terms, and Co-Terms

# Cyclic Terms

We can also represent terms that have loops in them like

The `define` and `makevar` api is more general than the `app` api.
Even if you are describing well founded trees, it is no longer guaranteed that the children need to appear earlier than parents

# Interpreting Equational Systems

For ordinary expressions with variables, a basic semantics is  an environment receiving one `(var -> T) -> T`

```python
def interp(e, env):
    match e:
        case ("+", a, b):
            return interp(a,env) + interp(b,env)
        case ("var", a):
            return env[a]
```

The arena can be seen as a mapping `Var -> Node<Var>` where the arena index is a way of referring to a "variable"

The entries of the arena is basically something like an expression with variables in it.

The basic interpretation of the entire arena is as an operator that you can iterate.

The arena can be seen as representing an operator `(var -> T) -> (var -> T)`.

`x_{t+1} = Ax_{t}`

Each entry of the arena is defining an expressions per variable `x_i`. These expressions may themselves refer ot variables.

it may often be the case that we'd like to talk about a fixed point of this intepretation, perhaps the greatest, least, or set of fixed points. One can talk about fixed points for any operator `A -> A`

```python

```

# Equality and Subterms

<https://www.philipzucker.com/subterm_mod_miller/>

It is kind of nice to take two entire arenas and see what makes sense to consider as equal.

Which of these two notions of equality to use (or some other notion), may depend on what domain of interpretation we intend.

```python
def pess_eq(a : Arena, b : Arena):
    eq = [[False]*len(b.data) for i in range(len(a.data))]
    while True:
        done = True
        for i in range(len(a.data)):
            for j in range(len(b.data)):
                if eq[i][j]: continue
                match a.data[i], b.data[j]:
                    case Node(fa, argsa), Node(fb, argsb) if fa == fb and len(argsa) == len(argsb):
                        if all(eq[ai][bi] for ai, bi in zip(argsa, argsb)):
                            eq[i][j] = True
                            done = False
        if done:
            return eq

A = Arena()
fa = A.makevar()
a = A.makevar()
A.define(fa, Node("f", [a])) # f(A)
A.define(a, Node("a", [])) # a

pess_eq(A,A)
```

    [[True, False], [False, True]]

```python
def opt_eq(a : Arena, b : Arena):
    eq = [[True]*len(b.data) for i in range(len(a.data))]
    while True:
        done = True
        for i in range(len(a.data)):
            for j in range(len(b.data)):
                if not eq[i][j]: continue
                match a.data[i], b.data[j]:
                    case Node(fa, argsa), Node(fb, argsb) if fa != fb or len(argsa) != len(argsb) or any(not eq[ai][bi] for ai, bi in zip(argsa, argsb)):
                            eq[i][j] = False
                            done = False
        if done:
            return eq

A = Arena()
fa = A.makevar()
a = A.makevar()
A.define(fa, Node("f", [a])) # f(A)
A.define(a, Node("a", [])) # a

opt_eq(A,A)
        
```

    [[True, False], [False, True]]

```python
A = Arena()
z = A.app("0")
zeros = A.makevar()
A.define(zeros, Node("cons", [z.id, zeros]))
opt_eq(A,A)

```

    [[True, False], [False, True]]

```python
pess_eq(A,A)
```

    [[True, False], [False, False]]

Is there an example we might want to mix pessimism and optimism?
Well we might want to reject loops in arithmetic expressions as nonsensical, but have loops in stream expressions.

We are defining a single step operator. This single step may not be exactly _time_.
We know that if we define the next time step in terms of the previous, we're good.

Rational Trees are a thing. They are loopy data structures. You can build them by knot tying like this.
Note that egg has the restriction "RecExprs must satisfy the invariant that enodes’ children must refer to
elements that come before it in the list." Basically, there are ways to remove that restriction.

```python
t = [None]
t[0] = t
t
```

    [[...]]

```python
f = Term("f", [None])
f.args[0] = f
f # fffffffffffffff...
```

    Term(f='f', args=[...])

```python
arena = [Node("f", [0])]
```

This is a notch too cute. You have to reach for annoying shallow stuff like python's `id` function to deal with this.

It is better to use the RecExpr style.

# Flattening Exposes Nice Structure For Some Reason

Compound terms are kind of goofy. We can expand them into flat form and this often exposes new ways of thinking or clarifies confusion.

One way to talk about this is as let expansion

```
f(g(a),b)

vs

let e1 = b in
let e2 = a in
let e3 = g(e2) in
let e4 = f(e3,e4)
```

Flattening may or may not require you to pick a linearization/sequencing of your subexpressions.

In an impreative language, expressions can actually be subservient to statements/commands. An expression should be thought of as a command with implicit destination storage `type Expr = Dst -> Stmt`. I think this is a shocking inversion of priority of concepts to those raised in functional programming / Imp, but IMO it's legit. This concept also appears also in the destination passing style compiler. This is why the walrus operator in python is an expression, or that assignement `=` can be used as an expression in C. It's acually kind of natural.  The fact that you _don't_ order the subexpressions when considered as statements is bizarre and a source of nondeterminism, unspecified beahvior or undefined behavior.

In order to flatten, you may need to invent new names. This is kind of like ids in a hash cons, arena, or egraph.

From a flattened form, it is not that far off to consider mututal recursion in those bindings.

```
let rec e1 = cons(0, e2)
and e2 = cons(1, e1) in
```

- egglog
- slog
- FOLDS
- A-normal form
- SSA
- Expressions are implicit destination statements
- Relational vs Functional style. Prolog vs Haskell/Curry. Resolution vs Superposition.

# Interpreting Terms and Co-Terms

If I want to interpret / give a semantics to a term, I can make an interpreter.

```python
def interp(e) -> int:
    match e:
        case ("+", a, b):
            return interp(a) + interp(b)
        case ("lit", a):
            return a
        case _:
            raise ValueError("Unknown expression", e)
interp(("+", ("lit", 1), ("lit", 2))) # 3
```

    3

It is less clear how one is going to construct an interpretation over a non-well founded term.

What we can do is make an operator turning a current valuation of the entire arena into a next valuation

This also works for a well founded term. It will finitely stabilize. The above simple intepreter can be seen as a nice topologically sorted ordering of the same kind of thing.

```python
def interp(a : Arena, cur : list[float]) -> list[float]:
    new = []
    for node in a:
        match node:
            case Node("+", [a, b]):
                new.append(cur[a] + cur[b])
            case Node("lit", [a]):
                new.append(a)
            case _:
                raise ValueError("Unknown expression", node)
    return new


def interp_set(a : Arena, cur : list[float]) -> list[float]:
    new = []
    for node in a:
        match node:
            case Node("union", [a, b]):
                new.append(cur[a] | cur[b])
            case Node("inter", [a, b]):
                new.append(cur[a] & cur[b])
            case Node("lit", [a]):
                new.append(a)
            case _:
                raise ValueError("Unknown expression", node)
    return new


```

There is a free interpretation of a kind that just builds increasing large finite approximations of the coterm. This also stabilizes. You can start this thing of wit `[None, None, None, ...]`

```python
def free_interp(a : Arena, cur : list[float]) -> list[float]:
    new = []
    for node in a:
        match node:
            case Node("+", [a, b]):
               cur.append(("+", cur[a], cur[b]))
            case Node("lit", [a]):
                new.append(a)
            case _:
                raise ValueError("Unknown expression", node)
    return new
```

For some kinds of interpretations, we may have a method to build the solution in one go.
Linear equations
Probablistic transition diagrams. Corresponds to multiplying the transition matrix over and over, which should fixed point into the stationary distribution <https://en.wikipedia.org/wiki/Markov_chain#Stationary_distribution_relation_to_eigenvectors_and_simplices>
For other interpretations, they will finitely stabilize.

Sometimes there will be a unique fixed point solution, other times there might be multiple. A least or a greatest.

Optimistic questions / Predicates. Greatest fixed point on a false <= true.
Pessimistic questions / predicates. Least fixed point

Binary Questions / Relations [[]]

# Sets of Terms and Co-Terms

For a finite set of terms, we can just put them into a set data structure.

```python
{ ("+", ("lit", 1), ("lit", 2)), 
  ("lit", 7) }
```

    {('+', ('lit', 1), ('lit', 2)), ('lit', 7)}

There is some oppotunity for compaction here. Sometimes we created a set of terms because we are applying `f` to two sets of children `{a,b}` `{c,d}` . Sometimes a set lifted version of `f` is denoted by using brackets `[f](A,B) = {f(a,b) | a in A, b in B}`. By allowing the set data structure and

Upon the union of two term sets, it could notice that there is a possibility to push the union down to the children. This is kind of a factoring move. The factored form of a polynomial might be much smaller than the fully FOILed out form. It also reminds me a bit of a BDD in some ways.
`{f(a,c), f(b,d)} | {f(a,d), f(b,c)} = f({a,b}, {c,d})`

I call this sort of thing "multiterms". It is also related or the same thing as VSA "version space algebras" and I think also a good model of what the aegraph is kind of getting at.

Infinite sets of well founded terms are not finitely representable in this framework.

This is in distinction to an e-graph, which can represent the infinite set of `{x, 1*x, 1*1*x, ...}` via a loop.

```python
@dataclass
class MultiNode:
    f : str
    args : list[set[Id]]

@dataclass
class TermSetRef:
    ids : set[Id]
    arena : Arena


```

# Productivity

# Rewriting on Arenas

We can rewrite on terms.

We can also do rewriting on terms held in arenas.

We can also do rewriting on cyclic terms held in arenas. It doesn't change anything _too_ much.

# Optimistic and Pessimistic Memoization

In the basic presentation of memoization in the context of [dynamic programming](https://en.wikipedia.org/wiki/Dynamic_programming) (rod cutting or what have you), it is assumed that you are doing a well founded recursion, that one subcall won't end up calling itself.

This is not the case in the implementation of depth first search in a graph. There, you keep a record of nodes you've already visited, and you do not go down already expanded nodes.

This can be thought of as memoization where you separately make an entry into the memo table on entry and on exit. A node can be "in process" as marked by a None entry in the memo table.

Checking equality in RecExpr can be made faster by memoizing. RecExpr is capable of expressing DAGs

This some how or other corresponds to least and greatest fixed points. I'm not sure how

Sergei A Grechanik. 2015. Proving properties of functional programs by equality saturation.

```python
def memo(f):
    cache = {}
    def memoized(x):
        if x in cache:
            return cache[x]
        else:
            y = f(x)
            cache[x] = y
            return y
    return memoized

def pess_memo(f):
    cache = {}
    def memoized(x):
        if x in cache:
            if cache[x] is None:
                return False
            return cache[x]
        else:
            cache[x] = None
            y = f(x)
            cache[x] = y
            return y
    return memoized


def opt_memo(f):
    cache = {}
    def memoized(*args):
        if args in cache:
            if cache[args] is None:
                return True
            return cache[args]
        else:
            cache[args] = None
            y = f(*args)
            cache[args] = y
            return y
    return memoized

    
def wf_eq(t : TermRef, s : TermRef):
    assert t.arena is s.arena
    arena = t.arena
    def eq(x,y):
        if x == y:
            return True
        else:
            node1, node2 = arena[x], arena[y]
            if node1.f != node2.f or len(node1.args) != len(node2.args):
                return False
            else:
                return all( zip(node1.args, node2.args) )
            

            
    
    return pess_memo(eq)(t.id, s.id)


```

# What is a loop in an e-graph?

We've talked about loops in terms. Is a loop in an egraph the same thing? It's subtle.

If I put the equation `zero = cons(0, zero)` into an egraph, I'm inclined to say that the contents of the eclass are an infinite set of finite terms `{zero, cons(0,zero), cons(0,cons(0,zero)), ...}` and not a singleton set of a single infinite term `{cons(0, cons(0, cons(0,...)))}`. These things _are_ kind of similar though.

# Egraphs as Eclasses

I would have thought the union find or `memo` is the most important field, but perhaps the most important field of an egraph is `eclasses : Id -> Set<Enode>`. This seems to fit best into the equational system persepctive

`eclasses` on it's own _is_ kind of a like arena. It is kind of like a multiterm arena

Indeed eclasses represents all the choices you may make during ematching or during extraction.

```python
@dataclass
class EGraph:
    eclasses : list[list[Node]] 

```

We may want ot distinguish between constructors and non constructors. Constructor are canonical. We might have more than one constructor in the list, but they should have the same symbol and resolve their children

# Inserting Co-Terms into an EGraph

As we insert a RecExpr, we record what eid we got for each index. If there is a backedge in the RecExpr (which is a child that points forward), we need to make a raw eid placeholder for that.

```python
from dataclasses import dataclass, field

type Id = int

@dataclass(frozen=True)
class Node:
    f : str
    args : tuple[Id, ...] = field(default_factory=tuple)
    constr : bool = False # new

@dataclass
class EGraph:
    memo : dict[Id, Node] = field(default_factory=dict)
    uf : list[int] = field(default_factory=list)
    defns : list[Id | None] = field(default_factory=list) # new

    def makeset(self):
        id = len(self.uf)
        self.uf.append(id)
        self.defns.append(None) # new
        return id

    def find(self, id: Id) -> Id:
        if self.defns[id] is not None: # lookup in definition table?
            id = self.defns[id]
        while self.uf[id] != id:
            id = self.uf[id]
        return id
    
    def define(self, x: Id, t : Id): # new
        assert self.defns[x] is None
        self.defns[x] = t

    def union(self, id1: Id, id2: Id):
        a, b = self.find(id1), self.find(id2)
        if a != b:
            self.uf[a] = b

    def canonicalize(self, node : Node) -> Node:
        return Node(node.f, tuple([self.find(arg) for arg in node.args]), constr=node.constr)

    def add_node(self, node) -> Id:
        node = self.canonicalize(node)
        id = self.memo.get(node)
        if id is None:
            id = self.makeset()
            self.memo[node] = id
        return id

    def app(self, f, args, constr=False):
        return self.add_node(Node(f, args, constr=constr))
 

    def nodes_in_class(self, id: Id) -> list[object]:
        # naive and slow
        if self.defns[id] is not None:
            id = self.defns[id]
        id = self.find(id)
        return [obj for obj, obj_id in self.memo.items() if self.find(obj_id) == id]
    
    def is_eq_fast(self, x : Id, y : Id) -> bool:
        return self.find(x) == self.find(y)

    def is_eq_slow(self, x : Id, y : Id, guard=False, history = []):
        x, y = self.find(x), self.find(y)
        if x == y:
            return True
        if (x,y) in history:
            return guard
        history = history + [(x,y)]
        for enode1 in self.nodes_in_class(x):
            for enode2 in self.nodes_in_class(y):
                if enode1.f == enode2.f and len(enode1.args) == len(enode2.args):
                    for argx,argy in zip(enode1.args, enode2.args):
                        if not self.is_eq_slow(argx, argy, guard=guard or enode1.constr, history=history):
                            break
                    else:
                        return True
        return False

    def is_eq_slow(self, x : Id, y : Id, guard_history=[], unguard_history = []):
        x, y = self.find(x), self.find(y)
        if x == y:
            return True
        if (x,y) in guard_history:
            return True
        elif (x,y) in unguard_history:
            return False
        for enode1 in self.nodes_in_class(x):
            for enode2 in self.nodes_in_class(y):
                if enode1.f == enode2.f and len(enode1.args) == len(enode2.args):
                    if enode1.constr:
                        unguard_history1 = [] 
                        guard_history1 = guard_history + unguard_history + [(x,y)]
                    else:
                        unguard_history1 = unguard_history + [(x,y)]
                        guard_history1 = guard_history
                    for argx,argy in zip(enode1.args, enode2.args):
                        if not self.is_eq_slow(argx, argy, guard_history, unguard_history):
                            break
                    else:
                        return True
        return False

    def is_eq_slow(self, x : Id, y : Id):
        guard_seen = {}
        unguard_seen = {}
        def worker(x,y):
            x, y = self.find(x), self.find(y)
            if x == y:
                return True
            if (x,y) in guard_seen:
                return True
            elif (x,y) in unguard_seen:
                return False
            for enode1 in self.nodes_in_class(x):
                for enode2 in self.nodes_in_class(y):
                    if enode1.f == enode2.f and len(enode1.args) == len(enode2.args):
                        if enode1.constr:
                            unguard_seen

                        for argx,argy in zip(enode1.args, enode2.args):
                            if not self.is_eq_slow(argx, argy, guard=guard or enode1.constr, history=history):
                                break
                        else:
                            return True
            return False

    
    def rebuild_slow(self):
        while True:
            done = True
            nodes = list(self.memo.items())
            for node, id in nodes:
                id1 = self.add_node(node)
                if not self.is_eq_fast(id, id1):
                    self.union(id, id1)
                    done = False
            for x in range(len(self.uf)):
                for y in range(len(self.uf)):
                    if not self.is_eq_fast(x,y):
                        if self.is_eq_slow(x,y):
                            self.union(x,y)
                            done = False    
            if done:
                return


E = EGraph()
a = E.app("a", [])
fa = E.app("f", [a])
E

E = EGraph()
z = E.app("z", [])
zeroS = E.makeset()
consz = E.app("cons", [z, zeroS], constr=True)
E.define(zeroS, consz)
E
zero1 = E.makeset()
consz = E.app("cons", [z, zero1], constr=True)
E.define(zero1, consz)
print(E.is_eq_slow(zero1, zeroS))
from pprint import pprint
pprint(E)

E.rebuild_slow()
E.is_eq_fast(zero1, zeroS)
E

```

    True
    EGraph(memo={Node(f='cons', args=(0, 3), constr=True): 4,
                 Node(f='z', args=(), constr=False): 0,
                 Node(f='cons', args=(0, 1), constr=True): 2},
           uf=[0, 1, 2, 3, 4],
           defns=[None, 2, None, 4, None])



    ---------------------------------------------------------------------------

    KeyboardInterrupt                         Traceback (most recent call last)

    Cell In[28], line 136
        133 from pprint import pprint
        134 pprint(E)
    --> 136 E.rebuild_slow()
        137 E.is_eq_fast(zero1, zeroS)
        138 E


    Cell In[28], line 108, in EGraph.rebuild_slow(self)
        106 for y in range(len(self.uf)):
        107     if not self.is_eq_fast(x,y):
    --> 108         if self.is_eq_slow(x,y):
        109             self.union(x,y)
        110             done = False    


    Cell In[28], line 86, in EGraph.is_eq_slow(self, x, y, guard, history)
         84 history = history + [(x,y)]
         85 for enode1 in self.nodes_in_class(x):
    ---> 86     for enode2 in self.nodes_in_class(y):
         87         if enode1.f == enode2.f and len(enode1.args) == len(enode2.args):
         88             for argx,argy in zip(enode1.args, enode2.args):


    Cell In[28], line 76, in EGraph.nodes_in_class(self, id)
         74     id = self.defns[id]
         75 id = self.find(id)
    ---> 76 return [obj for obj, obj_id in self.memo.items() if self.find(obj_id) == id]


    Cell In[28], line 27, in EGraph.find(self, id)
         25 if self.defns[id] is not None:
         26     id = self.defns[id]
    ---> 27 while self.uf[id] != id:
         28     id = self.uf[id]
         29 return id


    KeyboardInterrupt: 

```python
    """
    def add_term(self, t : TermRef) -> Id:
        eids = []
        for i, node in enumerate(t.arena):
            newargs = []
            for arg in node.args:
                if arg >= i:
                    #backedge
                    newargs.append(self.makeset())
                else:
                    newargs.append(eids[arg])
            eids.append(self.app(node.f, newargs))

    """
```

```python
    def is_eq_slow(self, x : Id, y : Id):
        cache = {}
        def worker(x,y):
            x, y = self.find(x), self.find(y)
            if x == y:
                return True
            if (x,y) in cache:
                return cache[(x,y)]
            for enode1 in self.nodes_in_class(x):
                for enode2 in self.nodes_in_class(y):
                    if enode1.f == enode2.f and len(enode1.args) == len(enode2.args):
                        for argx,argy in zip(enode1.args, enode2.args):
                            cache[]
                            if not worker(argx, argy):
                                break
                        else:
                            return True
            return False
        return worker(x,y)
```

# Top Down Rebuilding

# Enumerative Extraction as a Process

Guardedness as an offset eid?

```python
# Based on https://github.com/mwillsey/microegg
# https://github.com/philzook58/egraph-zoo/blob/main/microegg.py
from dataclasses import dataclass, field

type Id = int


class Pattern:
    pass


@dataclass(frozen=True)
class Var(Pattern):
    name: str


@dataclass(frozen=True)
class PApp(Pattern):
    f: str
    args: tuple[Pattern, ...]


type Node = tuple[str, tuple[Id, ...]]
type Subst = dict[str, Id]


@dataclass
class EGraph:
    memo: dict[object, Id] = field(default_factory=dict)
    uf: list[Id] = field(default_factory=list)

    def _add(self, obj: object) -> Id:
        id = self.memo.get(obj)
        if id is not None:
            return self.find(id)
        else:
            id = len(self.uf)
            self.uf.append(id)
            self.memo[obj] = id
            return id

    def add_app(self, f: str, *args: Id) -> Id:
        assert all(isinstance(arg, int) for arg in args)
        return self._add((f, args))

    def find(self, id: Id) -> Id:
        while self.uf[id] != id:
            id = self.uf[id]
        return id

    def union(self, id1: Id, id2: Id):
        a, b = self.find(id1), self.find(id2)
        if a != b:
            self.uf[a] = b

    def nodes_in_class(self, id: Id) -> list[object]:
        id = self.find(id)
        return [obj for obj, obj_id in self.memo.items() if self.find(obj_id) == id]

    def is_eq(self, a: Id, b: Id) -> bool:
        return self.find(a) == self.find(b)

    def canonize_node(self, node: Node) -> Node:
        f, args = node
        canon_args = tuple(self.find(arg) for arg in args)
        return (f, canon_args)

    def rebuild(self):
        copy_memo = self.memo.copy()
        while True:
            done = True
            for obj, id in copy_memo.items():
                id = self.find(id)
                new_node = self.canonize_node(obj)
                new_id = self._add(new_node)
                if new_id != id:
                    self.union(id, new_id)
                    done = False
            if done:
                return

    def ematch(self, pattern: Pattern, id: Id) -> list[Subst]:
        return self.ematch_rec(pattern, id, {})

    def ematch_rec(self, pattern: Pattern, id: Id, subst: Subst) -> list[Subst]:
        id = self.find(id)
        match pattern:
            case Var(name):
                if name in subst:
                    if self.is_eq(subst[name], id):
                        return [subst]
                    else:
                        return []
                else:
                    return [{**subst, name: id}]
            case PApp(f, args):
                results = []
                for obj in self.nodes_in_class(id):
                    match obj:
                        case (f0, arg_ids) if f0 == f and len(arg_ids) == len(args):
                            todo = [subst]
                            for arg_pattern, arg_id in zip(args, arg_ids):
                                todo = [
                                    subst1
                                    for subst0 in todo
                                    for subst1 in self.ematch_rec(
                                        arg_pattern, arg_id, subst0
                                    )
                                ]
                            results.extend(todo)
                        case _:
                            raise ValueError(f"Unexpected object in e-graph: {obj}")
                return results
```

# Bits and Bobbles

<https://jeannin.github.io/papers/cocaml.pdf>
<https://jeannin.github.io/papers/nwf.pdf>

Productivity tracking using the offset or positive offset union find. If there is a self loop with positive offset attached to it, where offset is interpreted as number of guards or timesteps in the future, then this is a definitional edge. A loop with 0 offset is not a definition.

EGraphs with Fixed Points. Consider having an explicit `fix` enode. This requires some notion of variable, which perhaps a slotted or lifting egraph can provide. But then you also need rewrites to push the fixes around. Something needs to discover

```
fix(a, cons(0, a)) = fix(a, cons(0, cons(0, a)))
```

Term Homeomorphism and kruskal's theorem
Coterm homemorphism? Does this get closer to <https://en.wikipedia.org/wiki/Robertson%E2%80%93Seymour_theorem> ?

I'm not really sure inductive vs coninductive whatever that means is the right axis.
Cyclic vs acyclic trees seems less mysterious.

`var := expr` vs `expr = expr`congreunce rule system

```
x := e 



```

Rational terms via recexpr
add_term
Well, I don't have to use recexpr in python, but I might need to watch for seen stuff.

Same for automata hash cons. If I give the entire rational term, I could do automata minimization as it is coming in.

CFG GKat seemed interesting. jumps

sol : E -> set of solution
canon : set of sol -> sol

Extensible emt. We can add new fresh constants that represent solutions

Egraph G is a transition system / process
Extraction is a transition system
Insertion is also a transition system (tree automata perspective?

Is sol() nterpretation kind of extraction? If we interpret into a semantic domain of tree

What is naive coterm rewriting?

Flattening and egglog.

embedding vs homomorphism

bisimulation odes not coniciden with behavioral equivalence
span
projection of a bisimulation?
<https://en.wikipedia.org/wiki/Bisimulation#Coalgebraic_definition>

```python
class RecExpr
```

```python
from dataclasses import dataclass, field

type Id = int

@dataclass(frozen=True)
class Node:
    name : str
    args : tuple[Node, ...] = field(default_factory=tuple)

@dataclass
class EGraph:
    memo : dict[Id, Node] = field(default_factory=dict)
    uf : list[int] = field(default_factory=list)

    def add_term(self, t : Term) -> Id: ...



```

Chang says a special symbol could wrap the body. elem.
Eveything is set lifted? But singleton sets only. And fixedpoints are kind of
With an implicit coercion between elements and sets.

How important are implicit coercions

Definitional equal and equal as different things does smack of type theory.

Extensionally equal ought to be union find + definiition table
So union find is equal - definitions? Kind of odd.
If egraphs are a model, then this is some kind of model that can see the difference between two notions of equality.

unfolding moves I did say a delta reduction
corecursive definitions we are in the ballpark of agda guardedness about which ones are well formed.

But getting bisimilar stuff to be definitionally equal is tough right? bisimilar is more of a extensional idea

<https://ncatlab.org/nlab/show/definition> :=  is a separate judgement. I do have some ploy about GATs as a syntax for multipatterns.
 We could have gats with a separate := judgement

Cycle cutting? Some kind of induction thing? Cyclic proofs something something.

I was trying to make finite models with timestamps

The eclass "is" equations? I guess each eclass could be not just the set of terms, but the set of pairs of equal terms. Doesn't seem to be much point there.
But if it was the set of proofs of equalities of terms, that's interesting.

Yes, it's interesting that the memo and defn occur at opposiute times. a Defn / Fix / FixVar node

```python
from dataclasses import dataclass, field
type Id = int

@dataclass(frozen=True)
class Node:
    f : str
    args : tuple[Id, ...]

class BiSimHashCons:
    memo : dict[Node, Id] = field(default_factory=dict)
    nodes : list[Node] = field(default_factory=list)
    uf : list[Id] = field(default_factory=list)
    defns : dict[Id, Id] = field(default_factory=dict)

    def app(self, f:str, *args):
        n = Node(f, args)
        if n in self.memo:
            return self.memo[n]
        else:
            i = len(self.nodes)
            self.nodes.append(n)
            self.uf.append(i)
            self.memo[n] = i
            return i
    def find(self, i:Id) -> Id:
        while self.uf[i] != i:
            i = self.uf[i]
        return i
    def makeset(self) -> Id:
        i = len(self.nodes)
        self.nodes.append(None)
        self.uf.append(i)
        return i
    def is_eq1(self, i:Id, j:Id) -> bool:
        return self.find(i) == self.find(j)
    def is_bisim(self, i:Id, j:Id) -> bool:
        seen = set()
        def worker(a,b,seen):
            a,b = self.find(a), self.find(b)
            if (a,b) or (b,a) in seen:
                return True
            seen = seen | {(a,b)}
    def define(self, i : Id, j : Id):
        self.defns[i] = j
        # del self.memo[placeholder]. self.memo[Defn(j)] = i
    def rebuild(self):
        ...
    
            



```

named eclasses as distinct from eids

observations  = set of partial extractions until you reach a constructor.
But that might be an infinite set because of egraph loops.

Rudi pointed out the graph coloring heursitic thing for hashing kind of leads to automata minimization if you take it seriously?

extraction gym. priority queue, and dag extraction

te detour cost thing makes a lot of sense. Kind of a*, kind of feels like monte carlo tree search to me or something. I dunno if I know how to think of a* as

Given root, what is cost of best tree that contains eclass x.  cost(root | x).  

A* as trying to find a minimum vs trying to find a known goal. Hmm.

# Definitions an EMT

Are definitions more like:

- rules
- associativity
- egraph equations (ground equations)

Definitions keep some things out of the egraph like baked in assocaitivty. But the concept of definition is more extensible than assocaitity.
egraph equations are also extensible. definitions are very similar, but sublte problems occur when we collapse the concepts.

Are multiple definitions allowed? `(S n) + m := S (n + m)` vs `n + (S m) := S (n + m)` Can such a thing happen the absence of variables?

Rules are conceptually run to a fixed point. We can't actually
Loops in egraphs are infinite sets of terms. We learn infinite congruence via finite means

Ematching modulo delta conversion, ematching modulo definitions

Extraction is nonlocal. Can we do bottom up extraction dyanmic programming style? We _have_ to be sharing cost

What is the normal form of definitions? Unfolding or refolding?

Rewriting the definitional equations and only rewrites that maintain the well formedness of definitions.
But what is the _definition_ as a object semantically. It is the
Definitions as stated feel syntactic. If I wanted a semantic object like to associated with the definitions, I think it would have to be the function that is being fixed that is defined by the definition.

we may write `def fact(n) := n * fact(n-1)` but this can be seen as `def fact := fix(fun f x => n * f (n - 1))
So the _semantic_ object associated with definitions is really that functional mapping. And then fix kind of floats

Egraphs modulo Fixpoint

If you can extract two definitions out the egraph,

You can extract two rational terms out of two eclasses. If these two rational terms are definitional (????) yo ucan combine them. Yeah it doesn't even sense check. Is a term "definitional"?
A pair of terms is definitional

fix(Cons(0, Hole)) = Cons(0, fix(Cons(0, Hole)))

zero = fix(Cons(0, Hole))
zero1 = fix(Cons(0, Hole))

fix(T) -> fixsubst(T,fix(T))
fixsubst(Hole, v) = v
fixsubst(Cons(a, tail), t) -> Cons(a, fixsubst(tai,t))

#

positive offset union fiund for causaality

Nat -> Option T is the more obvious model.

tail s = fun t -> s (t + 1)
head s = s 0
cons x xs = fun t -> if t == 0 then x else s (t - 1)

unknown = fun t -> None

x0 = uknonwn
x1 = cons(0, unknown)
x2 = cons(0,cons(0, unknown))

"look into" unions are unsound if entry is unknown?
x is being "vague" about which xn it is. similar to the way x+1 is "bvague" about which integer x is.

unknown <= cons(0, unknown)
hmmm.

fix x := Cons(0, x)
let x := fix (\y -> Cons(0, y))
cofix?

fix equations can't go in the egraph.

let rec x = Cons(0, x) in
    union(foo, bar)
    union(biz, baz)

In quasi egglog
let rec x = Cons(0, x)
let y = foo(3)

Atkey and Mcbride
utlrametric modls.
interpret delay modality as a contractiion. Then fix (T -> T) -> T is guanreted; Interpreted as sets.

later modality <https://iris-project.org/tutorial-pdfs/lecture7-later.pdf>
guarded recursion in type theory <https://www.pls-lab.org/Guarded_recursion_(type_theory)>

causality is too strong. just want productivity. But what is a semantic model
What is definition of guarded vs productive?

a time of availability model.
causality is a non interference property. The future is secret
<https://en.wikipedia.org/wiki/Causal_system>
(availabletime, value)
(t, stream) but pieces of the stream are only avialble at t + 1. Or maybe they are only avialable at some time > t in an ordere way
availability signals in a circuit. Buffering, processring. Bluespec. Multicycle

Index -> (Time, Value) where time has to increase strictly monotonically
(Time, Index -> Value) model where Time is a start time

tail(b) = (b[0] + 1, b) not (fun t => b[t-1])
cons(x,b) = (bt, fun t => if t == bt then x else bt[t-1])
precons(x,b) = (bt-1, fun t => if t == bt-1 then x else bt[t])

cons and precons are extensioanlly equal but different.

Or maybe always let what happens before go underspecified. But there might be some conivenet equations you could pick up

cons2
delay(b) = (bt + 1, (fun t => b[t-1]))
delay(b) =ext b

tail(cons(x,b)) != b intensionally, but it is extesnionally
tail(precons(x,b)) != b either. But closer. time isn't shifted. Irrelevant time data is overwritten
offset + scale. t0 +

is_causal(f) = forall t < k, a[at + t] =  b[at + t] => f[a] = f[b]
f
causal as generalized congruence?

Any "cuasal equation" x = f(x) defines x
or system of equations.

<https://www.cl.cam.ac.uk/~nk480/frp-lics11.pdf> krishnawswami and benton

Causal = A^k -> B forall k
mealy machines as causal functions

I was sort of bolting in t > 0 to my functional streams Nat -> T
But if I bolt in a starting time also (t, Nat -> T)
and then equality needs  to be defined. forall t, a[at0 + t] = b[bt0 + t]
To be intensionally equals the times need  to be the saem too.

extensional vs intensional as non caonincal set data strcturues.
hott = isomorphic types are equal. sure.

<https://research.vu.nl/ws/portalfiles/portal/2409636/219599.pdf> coniductive clculus of streams

Maybe tail should count as a `-1` to the guard condition is the problem? Most enodes are intuitively 0 or positive "guardedness"
<https://www.philipzucker.com/thin_monus_uf/> I've been thinking about generalized union finds lately. One of the let's you talk about offsets
You could kind of maintain a union find that says b =(-1)= tail(b)
They are indeed mostly equal, but you lose a guard if you use it
Or gain a guard if you go the other way
Or from the temporal stream perspective where everything`Int -> T`, you could perhaps use +-n to track shifted versions of signals.

Likewise for "guardedness" of inductives? Recursion? kind of a measure tracking analysis. But we don't want to say that
t = size 42. We want to say that s is a subterm of t because  t =n s or something

A replacement or generalization of the "constructor union find". Use monus uf, associated +1 height to Cons, and no change in height to functional stuff.
You would never equate things of different height... Hmm.

Cyclic proofs. xs =-1= ys -> Cons(x,xs) = Cons(y, ys). Isn't really a property of between . This is more of a mutlivalued tag / contextual annotation on equality.

Congruence for weight tags
xs =-1= ys -> Cons() =0= Cons or Cons() =-1= Cons?

A way to unify bisimulation collection and inductive collection?

A monus of observation chains? Monoid?
b = tail(b)  feels like the +1 should be associated with tail. So it's a property of _enodes_ perhaps in addition to part of the relation between edis.

```
                      -------------------------  
------          ----------                     | 
0 = 0             a = b                        |
----------------------------                   |
    Cons(0, a) = Cons(0, b)                    |
--------------------------- unfold?            |
 D,E |-  a = b   <-----------------------------------

```

Yes, that kind of described

```
  x = t in D
-------------- unfold
D, E |- x = y



----------------
D,E |- x :=: y 

```

_Definitionally equal_ vs just eqaul. But its kind of the opposite flavor of DTT.

What are the models of `x + 0 = x`

1. Term model
2. `{x:3} |= x + 0 = x` and `{x:4} |= x + 0 = x`
3. x is interpreted as `fun i => i` and all operators and constants are interpreted as pointwise lifted

It isn't this part that goes wrong, it's E infecting D

```
    D,E |- x = y
------------------bisim NO. Not a rule
   D, E U {x = y} 


   D,E |- x = y      {x := t, y := s} U D, E
------------------------------------------  bisimilar reduce
           {x := t} U D, E


        {x := t} U D, E
--------------------------! Not a rule
        D, E U {x = t}


       {x := t} U D, {t = s} U E
----------------------------------
               ?

```

What about the mu calculus for definitions?

<https://persons.iis.nsk.su/files/persons/pages/step05_12may23sergeygrechanik.pdf>
<https://github.com/sergei-grechanik/supercompilation-hypergraph/tree/master/samples>
<https://link.springer.com/article/10.1134/S0361768815030056>

Unique fixed point. Terminationg helps guarnatee that.
And that is a good persepctive. Given our intended semantics, are two things equal in all models. Unique in the given model?

Polyprograms
Actually a collection of rules transforming
Normal form.
Nice table in the talk of correspondances. So yes, supercompilation

<https://github.com/sergei-grechanik/peqsen?tab=readme-ov-file>
<https://github.com/sergei-grechanik/agda-graphsc> agda egraph

Hmm. So maybe the other inductive provers would be good for inspiration.

If there is a way to extract two equal things from an egraph, those eclasses should be equal.

One model is the term model
Another model is the coterm model

Some of the models are probably minimal / initial in some sense
Could there be no notion of minimal? Yeah, negation can screw you.
clauses.
Optimistic fixed points?

<https://scispace.com/pdf/bisimilarity-in-term-graph-rewriting-21f4rcsr85.pdf> rewriting modulo bismiilairty. Term graphs. ariola
Hmm. acyclic term graphs though

A codata union find.
a -> Cons(a,b) as the _union find_
It _is_ equations in solved form
X -> Y considered as aliens?

I noted this is omelets onions.
This is just a rearrangement of my coegraph which I felt was insufficient once they started pointed stuff out

a = Cons(xs, foo)
b = Cons(xs, foo)
Constructors should also be collecting congruence. So they _are_ enodes

What are the current examples that flummox us

Solvers
What abut doing my coegraphs in the
But being _guarded_ instead of sealed?

Backedges are special. "definition events" make a temporary thing avaiable for know tying. It is not an enode.

Infinite number of rules
If there exists a loop in there?

```
y = cons(cons(cons(y))), z = cons(cons(cons(z)))
-------------------
               y = z

```

rational trees CF

Do more automata algorithms from book
Tabling, Rational Terms, and Coinduction Finally Together! <https://arxiv.org/abs/1405.2794>

<https://arxiv.org/abs/cs/0403028> An Application of Rational Trees in a Logic Programming Interpreter for a Procedural Language

<https://cfbolz.de/posts/dfa-minimization-using-rational-trees-in-prolog/>

<https://www.philipzucker.com/coegraph/>

<https://joerg.endrullis.de/publications/infinitary%20rewriting/>

<https://softwarepreservation.computerhistory.org/prolog/marseille/doc/Colmerauer-InfTree-1982.pdf> prolog and infinte trees

<https://dl.acm.org/doi/10.1145/2480359.2429075> Copatterns: programming infinite structures by observations

Adriano Corbelino <https://nepls.org/Events/35/abstracts.html#08c03fd7> CoPy

<https://github.com/pdownen/CoScheme>

I'd assume that you have a rational term, there is some notion of finding a rational term inside another, cutting that out, and then replacing by a right hand side
To perform a rewrite step
And then it feels like a coherent question to ask if a rules set is confluent and to attempt to repair confluence via some procedure (some version of knuth bendix)
Such a confluent system of rules would "solve" ground equations between rational terms (?)
My current spiel is "generalized ground knuth bendix". That one can do knuth bendix over other special structures with notions of matching and overlap and rewriting (polynomials, multisets, ground terms, alpha invariant terms, and now rational terms (terms with loops)). And all these completed rewrite systems correspond to generalized egraphs with some good stuff baked in

f

Go ground first. Isn't that always the advice?

Rational Rewriting
<https://link.springer.com/chapter/10.1007/3-540-58338-6_90>
<https://dl.acm.org/doi/10.1007/978-3-030-68195-1_15> commutative rational rewriting
<https://link.springer.com/chapter/10.1007/978-3-642-33654-6_12>  Rational Term Rewriting Revisited: Decidability and Confluence

finite number of subterms. So a DAG aware term ordering (?). Count of number of subterms

Term graph rewriting
<https://www.cs.uoregon.edu/Reports/TR-1995-016.pdf> ariola and klop. equational term graph rewriting

drags?

mu-terms. mu-expressions

What about having an x after an infinite number of f? Ordinal completion style. Ord -> f | x.

<https://arxiv.org/abs/2601.09986> Outrunning Big KATs: Efficient Decision Procedures for Variants of GKAT

cut egraph loops before minimization

<https://homepage.divms.uiowa.edu/~ajreynol/cade15.pdf> Codatatypes in smt
<https://www.cs.cornell.edu/~kozen/Papers/CoCaml.pdf> cocaml

<https://www.kestrel.edu/people/pavlovic/papers/lapl-LICS98.pdf> calculus in coinductive form
<https://www.cs.cornell.edu/~kozen/Papers/MetricCoind.pdf> metric condinduction <https://mathoverflow.net/questions/26177/uses-of-bisimulation-outside-of-computer-science>

<https://www.cs.cornell.edu/~kozen/Papers/Capsules.pdf> computing with capsules
<https://cacm.acm.org/research/hacking-nondeterminism-with-induction-and-coinduction/>  Hacking Nondeterminism with Induction and Coinduction

<https://decomposition.al/blog/2025/11/20/where-simulation-came-from/>

<https://homes.cs.washington.edu/~djg/msr_russia2012/sangiorgi.pdf> introduction to simulation and

"The Russel example" <https://arxiv.org/abs/2511.20782>
Optimism as a middle fixed point and stable set semantics?

tuples of ints as state vs the ADT/ makes a difference if you want heterogenous state.
Even if heterogenous, the fields ap priori have nothing to do with eac htoerh

<https://isabelle.in.tum.de/website-Isabelle2011-1/dist/Isabelle2011-1/doc/ind-defs.pdf>
A Fixedpoint Approach to (Co)Inductive and (Co)Datatype Definitions∗

<https://arxiv.org/abs/cs/9711105> Mechanizing Coinduction and Corecursion in Higher-order Logic

defintions specify a unify object and bring reasoning principles

<https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-458.pdf> Final Coalgebras as Greatest Fixed Points
in ZF Set Theory

<https://www.andreipopescu.uk/POPL_2023_tutorial/Part1_Introduction.pdf>
<https://www.andreipopescu.uk/VeTSS/Part2_Inductive_Predicates.pdf>
<https://www.andreipopescu.uk/VeTSS/Part3_Coinductive_Predicates.pdf>

<https://www.cl.cam.ac.uk/archive/mjcg/Blog/WhatToDo/Coinduction.pdf> Corecursion and coinduction: what they are and
how they relate to recursion and induction
Mike Gordon <https://www.cl.cam.ac.uk/archive/mjcg/plans/Coinduction.html>

homotoyp type theory gets equality of streams. hmm.

<https://ncatlab.org/nlab/files/GimenezCasteran-InductiveTypes.pdf>
<http://adam.chlipala.net/cpdt/html/Coinductive.html>

<https://www.youtube.com/watch?v=wU2G-ODoabE> ulrich berger Coinduction in Computable Analysis
<https://arxiv.org/abs/1101.2162> From coinductive proofs to exact real arithmetic: theory and applications

<https://golem.ph.utexas.edu/category/2009/05/metric_coinduction.html> ? <https://www.cs.cornell.edu/kozen/Papers/MetricCoind.pdf>

```
I = [-1,1]
signed digit = {-1,0,1}
Phi(X) = {y in I | exists sd, x in X, y = (x + sd) / 2 }
C0 = gfp Phi # covers entire interval
```

```
#Biinifnite stream
smt.ArraySort(smt.IntSort(), A)

def head(s):
    return s[0]
def tail(s):
    return shift(s)
    return smt.Lambda([x], s[x+1]])

# fixedpoint "in what" is an discomfort with impredicativity?



```

rutten and turi
<https://ir.cwi.nl/pub/28550/rutten.pdf>
aczel 1977 inductive

finite algebra = finite set with operations (dicts)
finite homomorphism
finite congruence relation

finite coalgebra. finite set with unfold operations. Finite automata basically

Category theory is besides the point and anti-helpful.

initial algebra - probably infinite. Terms. EPR style restrictions? constants, sort stratification, predicates only
Unless you allow for partial functions. Then the egraph is an initial algebra

final coalgebra - probably infintie

closed vs open

- open datatypes in haskell papers
- open dataypes in ocaml
- open recursion and object oreitned programming
- Closed world assumption. Prolog vs minikanren. Negation by failure
- Whole program compilation MLTON vs Ocaml
- Defunctionalization.
- Agda mutual coppattern definitions
- let rec knot tying
- My new thing is open_definition in knuckledragger, which I kind ofwanted for a coinductive enocding

Things to do:

- Reimplement coegraphs. Definitional version
- Reimplement automata minimzation
- microegg
- cocaml
-

guardedness
productivity

aegraphs and cycle-cutting. Maybe if you aegraph it, automata minimization doesn't need to cycle cut

coterm rewriting

Hmm cocaml, user defined solvers. Shostak like?

Sets are a particularly important and well formed complete lattice.

Might be interesting to implement Paulson's construction using Quine tuples

Inductive sets over finite universes. "Silly" but perhaps useful. Induction over bitvectors.

The infinite set blog post never got written really.

<https://personal.cis.strath.ac.uk/conor.mcbride/pub/JUnfold/junfold.pdf> onor McBride’s "Let’s see how things unfold":
<https://mathoverflow.net/questions/407964/coinduction-for-all>

<https://cs.stackexchange.com/questions/114776/proving-with-co-induction-principles>  Hmm. inductive are easy to produce, annoying to destruct out of, coniductive are easy to destruct annoying to construct. So corecursor makes a stream, while recursor makes thing of our choosing.
Hmm.
So given init_S, and observation function (S -> (R, S)), I can make a Stream. Sure

```
def corec(init, trans):
    smt.Lambda([n], If(n < 0, 0, iterate(trans)[init]))

BiStream
#smt.ArraySort(smt.IntSort(), smt.IntSort(), smt.BoolSort())
smt.ArraySort(Stream, Stream, smt.Array(smt.IntSort(), smt.BoolSort()))
stream_eq = kd.define("stream_eq", [xs,ys], smt.Lambda([n], xs[n] == ys[n]))

BSeq = smt.ArraySort(smt.IntSort(), smt.BoolSort())
BStream = smt.Lambda([ps], smt.ForAll([n], n < 0, p[n] == False)) # True?

BStream is a truth value
Maybe we should just be working with Nat.

```

stream equality and bisimulation and extensionality

<https://www.cs.ru.nl/B.Jacobs/PAPERS/JR.pdf> A tutorail on coinduction and coalgerba jacobs and rutten

<https://isabelle.in.tum.de/dist/Isabelle/doc/functions.pdf>

```python

```

```python
from kdrag.all import *

@kd.reflect.struct
class Stream:
    data : smt.ArraySort(smt.IntSort(), smt.IntSort())
    valid : smt.IntSort()
```

```python
x,t = smt.Ints("x t")
xs,ys = smt.Consts("xs ys", Stream)

tail = kd.define("tail", [xs], xs._replace(valid=xs.valid+1))
cons = kd.define("cons", [x, xs], Stream(data=smt.Store(xs.data, xs.valid - 1, x), valid=xs.valid - 1))
stream_eq = kd.define("stream_eq", [xs, ys], smt.ForAll([t], t >= 0, xs.data[t + xs.valid] == ys.data[t + ys.valid]))
head = kd.define("head", [xs], xs.data[xs.valid])
kd.notation.eq.register(Stream, stream_eq)

delay = kd.define("delay", [xs], Stream(data=smt.Lambda([t], xs.data[t-1]), valid=xs.valid + 1))


```

```python
kd.prove(tail(cons(x, xs)) == xs, by=[stream_eq.defn, tail.defn, cons.defn])
kd.prove(cons(head(xs), tail(xs)) == xs, by=[stream_eq.defn, tail.defn, cons.defn, head.defn])

zeros = smt.Const("zeros", Stream)
head(zeros) == 0
tail(zeros) == delay(zeros)

kd.prove(smt.ForAll([xs], delay(xs) == xs), by=[delay.defn, stream_eq.defn])
kd.prove(smt.ForAll([xs, ys], xs == ys, head(xs) == head(ys)), by=[stream_eq.defn, head.defn])
kd.prove(smt.ForAll([xs, ys], xs == ys, tail(xs) == tail(ys)), by=[stream_eq.defn, tail.defn])




```

    ---------------------------------------------------------------------------

    LemmaError                                Traceback (most recent call last)

    File ~/vibe_coding/knuck_anal/knuckledragger/src/kdrag/tactics.py:315, in prove(thm, fixes, assumes, by, admit, timeout, dump, solver, contracts, unfold)
        314 try:
    --> 315     pf = kd.kernel.prove(
        316         thm, by=by_list, timeout=timeout, dump=dump, solver=solver, admit=admit
        317     )
        318     if fixes:


    File ~/vibe_coding/knuck_anal/knuckledragger/src/kdrag/kernel.py:170, in prove(thm, by, admit, timeout, dump, solver)
        169         smtfile.write(s.sexpr())
    --> 170     raise LemmaError("prove", thm, res, smtfile.name)
        171 else:


    LemmaError: ('prove', ForAll([xs, ys],
           Implies(stream_eq(xs, ys),
                   stream_eq(tail(xs), tail(ys)))), unknown, '/tmp/tmpv5352p6k.smt2')

    
    During handling of the above exception, another exception occurred:


    LemmaError                                Traceback (most recent call last)

    Cell In[30], line 10
          8 kd.prove(smt.ForAll([xs], delay(xs) == xs), by=[delay.defn, stream_eq.defn])
          9 kd.prove(smt.ForAll([xs, ys], xs == ys, head(xs) == head(ys)), by=[stream_eq.defn, head.defn])
    ---> 10 kd.prove(smt.ForAll([xs, ys], xs == ys, tail(xs) == tail(ys)), by=[stream_eq.defn, tail.defn])


    File ~/vibe_coding/knuck_anal/knuckledragger/src/kdrag/tactics.py:331, in prove(thm, fixes, assumes, by, admit, timeout, dump, solver, contracts, unfold)
        329     _, thm = kd.utils.open_binder_unhygienic(thm)  # type: ignore
        330 # We anticipate this failing with a better countermodel since we can now see the quantified variables
    --> 331 pf = kd.kernel.prove(
        332     thm, by=by_list, timeout=timeout, dump=dump, solver=solver, admit=admit
        333 )
        334 # TODO: Maybe we should herbrandize and just let the quantifier free version work for us.
        335 raise Exception(
        336     "Worked with quantifier stripped. Something is going awry", pf
        337 )


    File ~/vibe_coding/knuck_anal/knuckledragger/src/kdrag/kernel.py:170, in prove(thm, by, admit, timeout, dump, solver)
        166         smtfile = tempfile.NamedTemporaryFile(
        167             delete=False, mode="w", suffix=".smt2"
        168         )
        169         smtfile.write(s.sexpr())
    --> 170     raise LemmaError("prove", thm, res, smtfile.name)
        171 else:
        172     reason: list[object] = ["prove"]


    LemmaError: ('prove', Implies(stream_eq(xs, ys), stream_eq(tail(xs), tail(ys))), unknown, '/tmp/tmp974g0_rf.smt2')

```python
/tmp/tmp974g0_rf.smt2
```

```python
def Bool(t0, N):
    return {(t, v) for t in range(t0, t0+N) for v in [False, True]}
Bool(1, 3)
```

    {(1, False), (1, True), (2, False), (2, True), (3, False), (3, True)}

Clocked types. Guarded? A time of availability + a deadline bound just to keep tings finite?

Positive vs negative/lazy tuples?
Really laziness is from demand, not computing the innards after the wrapper

1. Bool(N)
2. Bool(t0,N)
3. Bool(ti, tf)

```python


def Bool(N):
    return {(t, v) for t in range(N) for v in [False, True]}
def Nat(N):
    return {(t, v) for t in range(N) for v in range(N) if t <= v}

Nat(3)

def Arr(N, A,B): ...
    # If we depend on the value of a, b has to come out later than a

def Tup(N, A, B):
    return {(t, ((ta, a), (tb, b))) for ta in range(N) for tb in range(N) for (ta1, a) in A(ta) for (tb1, b) in B(tb) if ta1 == ta and tb1 == tb}
    # arriving first. eager eval?
    return {(t, ((ta, a), (tb, b))) for t in range(N) for (ta,a) in A(t) for (tb, b) in B(t)}
    # arriving later. lazy eval?
    return {(t, ((ta, a), (tb, b))) for t in range(N) for (ta,a) in A(N-t) for (tb, b) in B(N-t)}




```

deoth limit the
my version only finds loops through n =0

cycle cutting via history. If you need to cross at least one constructor for sucess even if revisting

egraphs were always loopy, this loopiness was the extraciton process

extraction via the bisimulation search
cycle cutting as a pruning on history
depth limitting the node search

N-parition refinement

<https://github.com/sergei-grechanik/supercompilation-hypergraph/blob/master/samples/shifted-cycle>
prove: cycle (C A (C B N)) = C A (cycle (C B (C A N)));

<https://github.com/sergei-grechanik/supercompilation-hypergraph/blob/master/samples/shuffled-let>
left x y =  C x y (left x (S y));
right y x = C x y (right (S y) x);
prove: left x y = right y x;
-- f ~ g means "f is equal to g up to some renaming"
--prove: left ~ right;

My bismiulation could did partition refinement to discover all one hops.
One could pump this to two hop, N hop?
a = Cons(0, f(a))
b = Cons(0, f(b))
These should be merged is the claim.

Co MultiTerm extracts?
Deeper and deeper eid leaved muliterm extracts?
Cons(0, {f(a)})

eid -> constr : Option<App>, enodes : set<App>

If Block(v,v2,v3, nextblock)
or Cons(Block(v,v2,v3), nextblock)
Then "extracting" the block is extraction nextblock
The block are the body aren't equal. That's nice. Kind of
We need to extract like a cover still.

```python
# PROVING PROPERTIES OF FUNCTIONAL PROGRAMS Fig 5
def bisim(E, x, y, guard, history):
    if x == y:
        return True
    if (x, y) in history:
        if guard:
            return True
        else:
            return False
    for enode1 in E.enodes[x]:
        for enode2 in E.enodes[y]:
            if enode.f != enode2.f or len(enode.args) != len(enode2.args):
                continue
            if is_guard(enode.f):
                guard1 = True
            else:
                guard1 = guard
            if all(bisim(E, arg1,arg2 , guard, history + [(x, y)]) for arg1, arg2 in zip(enode.args, enode2.args)):
                return True
    return False
```

```python
from kdrag.all import *

Stream = smt.DeclareSort("Stream")
hd = smt.Function("hd", Stream, smt.IntSort())
tl = smt.Function("tl", Stream, Stream)

#Hmm. But where would the tags go?
#hd = OpenFunction("hd", Stream, smt.IntSort())
#tl = OpenFunction("tl", Stream, Stream)

zeros = smt.Const("zeros", Stream)
inc = smt.Const("inc", smt.IntSort(), Stream)
kd.axiom(hd(inc(n)) == n)
kd.axiom(tl(inc(n)) == inc(n+1))




```

# ultrametric

Nat -> T
Nat -> Option T
(Int, Nat -> T)

ultrametric convergence. 1/2^n where n is least n where differs

George had something special to say about this?
d(x,z) <= min(d(x,y), d(y,z)) . Makes sense. Can use an analysis / shortest path
Fixed point of an ultrametric
One way to describe when a fixed point of an operator defines something is in the Nat -> T model where the distance between two streams is defined as 2^-n where n is the first place they differ (edited)
[9:33 AM]Productive definitions make contractive stream maps according to this metric which have fixed points by Banach fixed point
[9:35 AM]George was discussing ultremetrics at the egraphs dahgstuhl,  but i wasn't part of those sessions. <https://en.wikipedia.org/wiki/Ultrametric_space> I think some aspect of his point was that the ultrametric property gives you the ability to do something more like shortest path than what a more general notion of approximate distance requires. So ultrametrics are somewhat amenable to egraph analysis/lattice type stuff requiring less computation and memory

I think he wanted it to use it for bitvectors or floats somehow?
This is interesting as a place where two things I've heard of seem to get close to each other. But I don't have a concrete suggestion beyond that
<https://www.cl.cam.ac.uk/~nk480/frp-lics11.pdf> Ultrametric Semantics of Reactive Programs - Krishnaswami and Benton

"Definitions" are kind of defining stream transformers moreso (?) than they are defining streams. There is a fixed point operator than converts them into

Transformers would be a bit more like a rule.
f(x0) --> body_f(x0)
fix(f)(x0) = fixf(f)(f(x0))

Definitions don't go in the egraph but why not.

transformers : Term -> Term
memo

# knuckle termination

Foetus
Abel and Alternkirch

Just do a pile a of equations

```python
# axioms scheme to just accept equations without compiling them.
def equations(E):
    assert all(smt.is_eq(e) for e in E)
    pats = [e.arg(0) for e in E]
    patvars = [smt.consts(pat) for pat in pats]
    assert all()
    matrix 

    return [kd.axiom(smt.ForAll(vs, e)) for vs, e in zip(patvars, E)]

    

```

```python
@dataclass(frozen=True)
class WellFoundedLT(Judgement):
    n : smt.ExprRef
    m : smt.ExprRef
    by : list[object]





def well_founded_lex(xs,ys): ...

def well_founded_int(n,m, by=[]):
    pf = kd.prove(smt.Abs(n) < smt.Abs(m), by=by)
    return WellFoundedLT(n, m, pf)

size = smt.Function("size", )


def wellfounded_dt_lt(n, m):
    if n.eq(m):
        return False
    while not n.eq(m):
        if smt.is_accessor(m):

        else:
            return False


def prim_wellfounded_lt(n, m):
    sort =


def define_rec(name, args, return_sort, rec, measure=None, termination_by=[]):
    subargs = 


```

```python
def definegas_primrec(name, args, body):
    f_gas = smt.Function(name + "_gas")
    f = smt.Function()

    smt.If(n <= 0, kd.Undef(body.sort()), body)
    body1 = smt.substitute_funs(body, f, f_gas(n-1, Var(0), Var(1), ...))
    return kd.define(name + "_gas"), [n] + args, smt.If(n <= 0, kd.Undef(body.sort()), body1))
# we can't ever prove it's Not equal to Undef, because it's not opersvable.
# could use Option


def define_gas(name: str, args: list[smt.ExprRef], body: smt.ExprRef):
    assert args[-1].sort() == smt.IntSort(), "Last argument must be gas"
    f = smt.Function(name, *[arg.sort() for arg in args], body.sort())
    # get all subcalls of f in body.
    seen = set() # seen should be (ctx, term) pairs
    todo = [(smt.BoolVal(True), body)] # ctx, term
    subcalls = set()
    while todo:
        ctx, t = todo.pop()
        if (ctx.get_id(), t.get_id()) in seen:
            continue
        seen.add((ctx.get_id(), t.get_id()))
        if isinstance(t, smt.QuantifierRef):
            # open_binder?   define(f, args, Lambda(...))
        if smt.is_if(t):
            c,then,else_ = t.children()
            ctx1 = smt.And(ctx, c)
            todo.append((ctx1, then))
            todo.append((ctx1, else_))
        if t.decl() == f:
            seen.add(t)
        else:
            todo.extend(t.children())
    for (ctx, e) in subcalls:
        args1 = e.children()
        kd.prove(smt.ForAll(args, smt.Implies(ctx, smt.Abs(args1[-1] < smt.Abs(args[-1])) )))
    return define(name, args, body)

# a simple form of primrec as a schema
def define_primrec(name: str, sort: smt.DatatypeSortRef, ret_type, *cases):
    assert isinstance(sort, smt.DatatypeSortRef)
    nconstrs = sort.num_constructors()
    assert len(cases) == nconstrs, f"Expected {nconstrs} cases, got {len(cases)}"
    x = smt.FreshConst(sort, prefix="x")
    f = smt.Function(name, ) #declare(name, sort, ret_type)
    acc = smt.FreshConst(ret_type, prefix="undef")
    for i, case in enumerate(cases):
        constr = sort.constructor(i)
        args = [sort.accessor(i, j)(x) for j in range(constr.arity())]
        args = [f(arg) if arg.sort() == sort else arg for arg in args]
        recognizer = sort.recognizer(i)
        acc = smt.If(recognizer(x), case(*args), acc)
    # I should check for recursive calls other than those expected maybe
    return kd.define(name, x, acc)
    # axiom = smt.ForAll([x], smt.Eq(f(x), acc), patterns=[f(x)])
    # defn = make_unfolding(axiom(f(x)))
    # return f
def is_primrec(pf : kd.Proof): ...
def is_term(pf : kd.Proof): ...
    #given equational theorme defining a function,
    # Is the right hand side decreasing?

def define_gas(name, body)

```

```python
from kdrag.all import *
```

```python
# banach
V = smt.DeclareSort("V")
dist = smt.Function("dist", V, V, smt.RealSort())
u,v,w = smt.Consts("u v w", V)
dist_zero = kd.axiom()

VSeq = smt.ArraySort(smt.IntSort(), V)



```

```python
from kdrag.all import *
import kdrag.theories.real.seq as seq
import kdrag.theories.int as int_


int_.even
n,m = smt.Ints("n m")
P = smt.Const("P", smt.SetSort(smt.IntSort()))
@kd.PTheorem(smt.ForAll([P,n], int_.even(n), n >= 0, P[0], smt.ForAll([m], m >= 0, P[m], P[m+2]), P[n]))
def even_induct(l):
    P, n = l.fixes()
    l.intros()
    l.split(-1)
    l.induct(n, int_.induct_nat_strong)
    n1 = l.fix()
    l.intros()
    l.split(-1)
    l.cases(n1 == 0)
    l.auto()

    

```

    Next Goal:
     [P!5388, n!5389, n!5392];
    [even(n!5389),
     n!5389 >= 0,
     P!5388[0],
     ForAll(m, Implies(And(m >= 0, P!5388[m]), P!5388[m + 2])),
     n!5392 >= 0,
     ForAll(m!5391,
           Implies(And(m!5391 >= 0, m!5391 < n!5392),
                   P!5388[m!5391])),
     (n!5392 == 0) == False]
    ?|= P!5388[n!5392]

```python
from kdrag.all import *
import kdrag.theories.real.seq as seq


seq.RSeq
x,y = smt.Reals("x y")

xs, ys = smt.Consts("xs ys", seq.RSeq)
n= smt.Int("n")
Stream = smt.Lambda([xs], smt.ForAll([n], n < 0, xs[n] == 0))
cons = kd.define("RSeq.cons", [x,xs], smt.Lambda([n], smt.If(n < 0, 0, smt.If(n==0, x, xs[n-1]))))
hd = kd.define("RSeq.hd", [xs], xs[0])
tl = kd.define("RSeq.tl", [xs], smt.Lambda([n], smt.If(n < 0, 0, xs[n+1])))
hd_cons = kd.prove(smt.ForAll([x,xs], hd(cons(x,xs)) == x), by=[cons.defn, hd.defn])
cons_stream = kd.prove(smt.ForAll([x,xs], Stream(cons(x,xs))), by=[cons.defn])

@kd.Theorem(smt.ForAll([x,xs, n], Stream(xs), tl(cons(x,xs))[n] == xs[n]))
def tl_cons(l):
    x,xs,n = l.fixes()
    l.intros()
    l.unfold(tl)
    l.unfold(cons)
    l.beta()
    l.simp()
    l.specialize(-1,n)
    l.auto()
    #l.simp()
tl_cons = kd.prove(smt.ForAll([x,xs], Stream(xs), tl(cons(x,xs)) == xs), by=[tl.defn, cons.defn])

def StreamF(S):
    return smt.Lambda([xs], smt.Exists([y,ys], smt.And(S[ys], xs == cons(y, ys))))
#kd.GFP(StreamF, seq.RSeq)

P = smt.Const("P", smt.SetSort(seq.RSeq))
smt.ForAll([P, xs], Stream(xs), smt.ForAll([y,ys], Stream(ys), P[cons(y,ys)], P[ys]), P[xs])

# Hmm the relational 

```

    ---------------------------------------------------------------------------

    AttributeError                            Traceback (most recent call last)

    /tmp/ipykernel_526422/4179467695.py in ?()
         28 tl_cons = kd.prove(smt.ForAll([x,xs], Stream(xs), tl(cons(x,xs)) == xs), by=[tl.defn, cons.defn])
         29 
         30 def StreamF(S):
         31     return smt.Lambda([xs], smt.Exists([y,ys], smt.And(S[ys], xs == cons(y, ys))))
    ---> 32 kd.GFP(StreamF, seq.RSeq)


    ~/vibe_coding/knuck_anal/knuckledragger/src/kdrag/__init__.py in ?(F, sort)
        432     """
        433     SetSort = _infer_sort(F, sort)
        434     x = smt.FreshConst(SetSort.domain(), prefix="x")
        435     A = smt.FreshConst(SetSort, prefix="A")
    --> 436     return smt.Lambda([x], smt.Exists([A], PostFix(F, A), A[x]))


    ~/vibe_coding/knuck_anal/knuckledragger/src/kdrag/__init__.py in ?(F, A)
        405 def PostFix(F, A):
    --> 406     return A <= F(A)


    /tmp/ipykernel_526422/4179467695.py in ?(S)
         30 def StreamF(S):
    ---> 31     return smt.Lambda([xs], smt.Exists([y,ys], smt.And(S[ys], xs == cons(y, ys))))


    ~/philzook58.github.io/.venv/lib/python3.12/site-packages/z3/z3.py in ?(self, arg)
       4722         a[i]
       4723         >>> a[i].sexpr()
       4724         '(select a i)'
       4725         """
    -> 4726         return _array_select(self, arg)


    ~/philzook58.github.io/.venv/lib/python3.12/site-packages/z3/z3.py in ?(ar, arg)
       4733     if isinstance(arg, tuple):
       4734         args = [ar.sort().domain_n(i).cast(arg[i]) for i in range(len(arg))]
       4735         _args, sz = _to_ast_array(args)
       4736         return _to_expr_ref(Z3_mk_select_n(ar.ctx_ref(), ar.as_ast(), sz, _args), ar.ctx)
    -> 4737     arg = ar.sort().domain().cast(arg)
       4738     return _to_expr_ref(Z3_mk_select(ar.ctx_ref(), ar.as_ast(), arg.as_ast()), ar.ctx)


    ~/philzook58.github.io/.venv/lib/python3.12/site-packages/z3/z3.py in ?(self, val)
       2444                 _z3_assert(self.ctx == val.ctx, "Context mismatch")
       2445             val_s = val.sort()
       2446             if self.eq(val_s):
       2447                 return val
    -> 2448             if val_s.is_int() and self.is_real():
       2449                 return ToReal(val)
       2450             if val_s.is_bool() and self.is_int():
       2451                 return If(val, 1, 0)


    AttributeError: 'ArraySortRef' object has no attribute 'is_int'

```python
def powerset(iterable):
    "Subsequences of the iterable from shortest to longest."
    # powerset([1,2,3]) → () (1,) (2,) (3,) (1,2) (1,3) (2,3) (1,2,3)
    s = list(iterable)
    return chain.from_iterable(combinations(s, r) for r in range(len(s)+1))

def is_monotone(U, F):
    return all(F(s1) <= F(s2) for s1 in powerset(U) for s2 in powerset(U) if  s1 <= s2)
def is_antimonotone(U, F):
    return all(F(s1) >= F(s2) for s1 in powerset(U) for s2 in powerset(U) if  s1 <= s2)

def least_prefix(U, F):
    # computationally speaking, this is insane.
    return set.union(s for s in powerset(U) if F(s) <= s)

def greatest_postfix(U, F):
    return set.intersection(s for s in powerset(U) if s <= F(s))

def least_fixedpoint2(F):
    res = set()
    while True:
        new_res = F(res) # assuming monotone
        if new_res == res:
            return res
        res = new_res

def monotonize(U, F):
    return lambda S: F(S).union(S)
def antimonotonize(U, F):
    return lambda S: F(S).intersection(S)


```

```python
def PreFix(A, F):
    BigUnion(smt.Lambda([S], F(S) <= S))
def PostFix(A, F):
    ...
def Monotone(A, F):





```

```python
def is_sim(T1, T2, R):
    for p1,q1 in R:
        for p2 in T1[p1]:
            T2[2]
            


```

# microegg

```python
# Based on https://github.com/mwillsey/microegg
from dataclasses import dataclass, field
type Id = int
class Pattern: ...
@dataclass(frozen=True)
class Var(Pattern):
    name: str
@dataclass(frozen=True)
class PApp(Pattern):
    f: str
    args: tuple[Pattern, ...]
type Node = tuple[str, tuple[Id, ...]]
type Subst = dict[str, Id]

@dataclass(frozen=True)
class Obs:
    name: str
    args: tuple[Id, ...]

@dataclass
class EGraph:
    memo: dict[object, Id] = field(default_factory=dict)
    obs: dict[Id, Obs] = field(default_factory=dict)
    uf: list[Id] = field(default_factory=list)

    def _add(self, obj: object) -> Id:
        id = self.memo.get(obj)
        if id is not None:
            return self.find(id)
        else:
            id = len(self.uf)
            self.uf.append(id)
            self.memo[obj] = id
            return id

    def add_app(self, f: str, *args: Id) -> Id:
        assert all(isinstance(arg, int) for arg in args)
        return self._add((f, args))

    def find(self, id: Id) -> Id:
        while self.uf[id] != id:
            id = self.uf[id]
        return id

    def union(self, id1: Id, id2: Id):
        a, b = self.find(id1), self.find(id2)
        if a != b:
            self.uf[a] = b

    def nodes_in_class(self, id: Id) -> list[object]:
        id = self.find(id)
        return [obj for obj, obj_id in self.memo.items() if self.find(obj_id) == id]

    def is_eq(self, a: Id, b: Id) -> bool:
        return self.find(a) == self.find(b)

    def canonize_node(self, node: Node) -> Node:
        f, args = node
        canon_args = tuple(self.find(arg) for arg in args)
        return (f, canon_args)

    def rebuild(self):
        copy_memo = self.memo.copy()
        while True:
            done = True
            for obj, id in copy_memo.items():
                id = self.find(id)
                new_node = self.canonize_node(obj)
                new_id = self._add(new_node)
                if new_id != id:
                    self.union(id, new_id)
                    done = False
            if done:
                return




E = EGraph()
a = E.add_app("a")
b = E.add_app("b")
fa = E.add_app("f", a)
fb = E.add_app("f", b)
E.union(a, b)
assert E.is_eq(a, b)
assert not E.is_eq(fa, fb)
E.rebuild()
assert E.is_eq(a, b)
assert E.is_eq(fa, fb)

assert len(E.ematch(PApp("f", (Var("x"),)), E.find(fa))) == 2


```

sam style

```python
@dataclass
class EGraph:
    memo: dict[object, Id] = field(default_factory=dict)
    definitions : dict[Id, Id] = field(default_factory=dict)
    uf: list[Id] = field(default_factory=list)

    def _add(self, obj: object) -> Id:
        id = self.memo.get(obj)
        if id is not None:
            return self.find(id)
        else:
            id = len(self.uf)
            self.uf.append(id)
            self.memo[obj] = id
            return id

    def add_app(self, f: str, *args: Id) -> Id:
        assert all(isinstance(arg, int) for arg in args)
        return self._add((f, args))

    def find(self, id: Id) -> Id:
        while self.uf[id] != id:
            id = self.uf[id]
        return id

    def union(self, id1: Id, id2: Id):
        a, b = self.find(id1), self.find(id2)
        if a != b:
            self.uf[a] = b

    def nodes_in_class(self, id: Id) -> list[object]:
        id = self.find(id)
        return [obj for obj, obj_id in self.memo.items() if self.find(obj_id) == id]

    def is_eq(self, a: Id, b: Id) -> bool:
        return self.find(a) == self.find(b)

    def canonize_node(self, node: Node) -> Node:
        f, args = node
        canon_args = tuple(self.find(arg) for arg in args)
        return (f, canon_args)

    def rebuild(self):
        copy_memo = self.memo.copy()
        while True:
            done = True
            for obj, id in copy_memo.items():
                id = self.find(id)
                new_node = self.canonize_node(obj)
                new_id = self._add(new_node)
                if new_id != id:
                    self.union(id, new_id)
                    done = False
            if done:
                return




E = EGraph()
a = E.add_app("a")
b = E.add_app("b")
fa = E.add_app("f", a)
fb = E.add_app("f", b)
E.union(a, b)
assert E.is_eq(a, b)
assert not E.is_eq(fa, fb)
E.rebuild()
assert E.is_eq(a, b)
assert E.is_eq(fa, fb)

assert len(E.ematch(PApp("f", (Var("x"),)), E.find(fa))) == 2

```

Cheng example:
x = Cons(0, f1(x))
y = Cons(0, f2(y))
z = Cons(0, f2(z))

Hmm. Yeah, observation table won't work to solve this.
f2(x) = f2(y)

enum StreamLanguage {
    Num(i32),
    "Cons" = Cons([Id; 2]),
    "S" = Successor([Id; 1]),
    "Node" = Node([Id; 3]),
    "+" = Add([Id; 2]),
    "*" = Mul([Id; 2]),
    "f" = F([Id; 1]),
    "g" = G([Id; 1]),
    "h" = H([Id; 1]),
    "Map" = Map([Id; 2]),
    "App" = App([Id; 2]),
    Symbol(Symbol),
}

states are eclasses
transitions labelled by function symbol
point to vectors of eclasses

exists a coterm in eclass that are equal

observation tyable vs not

simpel egraph = finite number of terms is meaning of each eclass
loopy egraph - some eclasses can represent infintie number of finite terms

coe-graph - some eclasses represent coterms

clouds with coterms
notice two coterms asre equal
EXISTS coterms

witness _is_ coterm

coterm is bisimulation?

What abouty multiterm

eclass = set of terms
eclass = set of coterms

top down rebuilding - take two eclasses, extract a common term / coterm. union if you can
bottom up rebuilding -

```python
from dataclasses import dataclass
@dataclass(frozen=True)
class App:
    f : str
    args : tuple["App", ...]

a = App("a", ())
b = App("b", ())
fa = App("f", (a,))
fb = App("f", (b,))
{fa, fb}
```

    {App(f='f', args=(App(f='a', args=()),)),
     App(f='f', args=(App(f='b', args=()),))}

```python
import itertools
@dataclass(frozen=True)
class MultiTerm():
    f : str
    argsets : tuple[frozenset["MultiTerm"], ...]

    def expand(self):
        argsets = [{arg.expand() for arg in argset} for argset in self.argsets]
        return frozenset([App(self.f, arg) for arg in itertools.product(*argsets)])

a = MultiTerm("a", ())
b = MultiTerm("b", ())
ab = frozenset([a, b])
fa = MultiTerm("f", (ab, ab, ab)) # a set of 2^3 = 8 terms
fa.expand()

```

    frozenset({App(f='f', args=(frozenset({App(f='a', args=())}), frozenset({App(f='a', args=())}), frozenset({App(f='a', args=())}))),
               App(f='f', args=(frozenset({App(f='a', args=())}), frozenset({App(f='a', args=())}), frozenset({App(f='b', args=())}))),
               App(f='f', args=(frozenset({App(f='a', args=())}), frozenset({App(f='b', args=())}), frozenset({App(f='a', args=())}))),
               App(f='f', args=(frozenset({App(f='a', args=())}), frozenset({App(f='b', args=())}), frozenset({App(f='b', args=())}))),
               App(f='f', args=(frozenset({App(f='b', args=())}), frozenset({App(f='a', args=())}), frozenset({App(f='a', args=())}))),
               App(f='f', args=(frozenset({App(f='b', args=())}), frozenset({App(f='a', args=())}), frozenset({App(f='b', args=())}))),
               App(f='f', args=(frozenset({App(f='b', args=())}), frozenset({App(f='b', args=())}), frozenset({App(f='a', args=())}))),
               App(f='f', args=(frozenset({App(f='b', args=())}), frozenset({App(f='b', args=())}), frozenset({App(f='b', args=())})))})

multiterm with id
multiterm of coterms

extraction of coterms?
coinductive logic programming for extraction or for searching for bisimulation?

But that is rational unification? No but we have a choice?

bisim(t,s) :-

<https://maude.lcc.uma.es/maude-manual/maude-manualch5.html#x40-640005> Yeah, I guess we could define two vending machines and show they get merged. That'd be traditional
[11:43 AM]Or like a euro and dollar vending machine with currency exchange functions or something?

<https://mcrl2.org/web/user_manual/language_reference/data.html#structured-sorts>

how to extract coterm from coegraph?

```python
from dataclasses import dataclass
type Id = int
@dataclass(frozen=True)
class Node():
    f : str
    args : tuple[Id, ...]

type Term = tuple[Node, dict[Id, Node]] # RecExpr basically
# type Term = tuple[Id, dict[Id, Node]] # RecExpr basically

def term_to_app(t : Term) -> App:
    node, defs = t
    def helper(node : Node) -> App:
        return App(node.f, tuple(helper(defs[arg]) for arg in node.args))
    return helper(node)

a = Node("a", ())
b = Node("b", ())
env = {0 : a, 1 : b}
f = Node("f", (0, 1))
term_to_app((f, env))

```

    App(f='f', args=(App(f='a', args=()), App(f='b', args=())))

```python

f = Node("f", (0,))
env = {0 : f}
# inifnite term
#term_to_app((f, env))
```

    ---------------------------------------------------------------------------

    RecursionError                            Traceback (most recent call last)

    Cell In[42], line 3
          1 f = Node("f", (0,))
          2 env = {0 : f}
    ----> 3 term_to_app((f, env))


    Cell In[40], line 14, in term_to_app(t)
         12 def helper(node : Node) -> App:
         13     return App(node.f, tuple(helper(defs[arg]) for arg in node.args))
    ---> 14 return helper(node)


    Cell In[40], line 13, in term_to_app.<locals>.helper(node)
         12 def helper(node : Node) -> App:
    ---> 13     return App(node.f, tuple(helper(defs[arg]) for arg in node.args))


    Cell In[40], line 13, in <genexpr>(.0)
         12 def helper(node : Node) -> App:
    ---> 13     return App(node.f, tuple(helper(defs[arg]) for arg in node.args))


    Cell In[40], line 13, in term_to_app.<locals>.helper(node)
         12 def helper(node : Node) -> App:
    ---> 13     return App(node.f, tuple(helper(defs[arg]) for arg in node.args))


    Cell In[40], line 13, in <genexpr>(.0)
         12 def helper(node : Node) -> App:
    ---> 13     return App(node.f, tuple(helper(defs[arg]) for arg in node.args))


        [... skipping similar frames: <genexpr> at line 13 (1485 times), term_to_app.<locals>.helper at line 13 (1485 times)]


    Cell In[40], line 13, in term_to_app.<locals>.helper(node)
         12 def helper(node : Node) -> App:
    ---> 13     return App(node.f, tuple(helper(defs[arg]) for arg in node.args))


    Cell In[40], line 13, in <genexpr>(.0)
         12 def helper(node : Node) -> App:
    ---> 13     return App(node.f, tuple(helper(defs[arg]) for arg in node.args))


    RecursionError: maximum recursion depth exceeded

```python
@dataclass(frozen=True)
class MultiNode():
    f : str
    args : tuple[frozenset[Id], ...]

type MultiEnv = dict[Id, frozenset[Node]]
# Can now also represent a set of coterms

```

```python



a = MultiTerm("a", )

ab = {a, b}

f = MultiTerm("f", (ab, ab)) #


```

      Cell In[23], line 12
        return App( itertools.product(*self.args)
                  ^
    SyntaxError: '(' was never closed

```python
    def ematch(self, pattern: Pattern, id: Id) -> list[Subst]:
        return self.ematch_rec(pattern, id, {})

    def ematch_rec(self, pattern: Pattern, id: Id, subst: Subst) -> list[Subst]:
        id = self.find(id)
        match pattern:
            case Var(name):
                if name in subst:
                    if self.is_eq(subst[name], id):
                        return [subst]
                    else:
                        return []
                else:
                    return [{**subst, name: id}]
            case PApp(f, args):
                results = []
                for obj in self.nodes_in_class(id):
                    match obj:
                        case (f0, arg_ids) if f0 == f and len(arg_ids) == len(args):
                            todo = [subst]
                            for arg_pattern, arg_id in zip(args, arg_ids):
                                todo = [
                                    subst1
                                    for subst0 in todo
                                    for subst1 in self.ematch_rec(
                                        arg_pattern, arg_id, subst0
                                    )
                                ]
                            results.extend(todo)
                        case _:
                            raise ValueError(f"Unexpected object in e-graph: {obj}")
                return results
```

A cool thing about the egraph is that the memo table is literally the algebra function f a -> a  with the underlying set being the set of Ids
That really helps the algebra thing feel more real to me
So would a maximally inefficient coegraph be

```rust
Node { f : str, args : Vec<Id> }
CoEgraph { comemo : HashMap<Id, HashSet<Node>>}(edited)
```

I guess even uf in the ordinary egraph is redundant kind of. It let's you do lazy rebuilding but you don't necessarily need it
Maybe if you containerize it one could literally use jules' library?

Node<T> { f : str, args : Vec<T> }
CoEgraph { comemo : HashMap<Id, HashSet<Node<Id>>>}(edited)
No maybe

```rust
struct Node<T> { constructor : bool, f : str, args : Vec<T> }
struct CoEgraph { comemo : HashMap<Id, HashSet<Node<Id>>>}(edited)
struct Egraph {memo : HashMap<Node<Id>, Id>}
```

This is very similar to Max's IndexMap single table egraph. But IndexMap is kind of sort of two tables pakced in one. If I wanted to do this I'd need to eagerly replace id1 with id2 everywhere

Really hammers home the duality
The appearance of the hashset is odd and interesting though

<https://www.swi-prolog.org/pldoc/man?section=cyclic>
<https://softwarepreservation.computerhistory.org/prolog/marseille/doc/Colmerauer-InfTree-1982.pdf>

The observation persepctive of rational trees is that they have two observations

Hmm. Prolog acutally does this

functor(t) =
children(t) = [a,b,c]

functor(t)
child(t, n)

```python
# brtually inefficient/eager egraph
# it's hard to even keep a handle on entities.
# I guess eids ought to correspond to terms
# It is always fully rebuilt
# it's actually confusing to be this eager

from dataclasses import dataclass
@dataclass(frozen=True)
class Node:
    f : str
    args : tuple[Id, ...]

class EGraph:
    memo : dict[Node, Id]

    # all external Ids become immediately stale too.
    def add_app(self, f: str, *args: Id) -> Id:
        node = Node(f, args)
        id = self.memo.get(node)
        if id is None:
            id = len(self.memo)
            self.memo[node] = id
        else:
            return id

    def find(self, id: Id) -> Id: 
        raise ValueError("There is no find")

    def union(self, a : Id, b : Id) -> Id:
        if a != b:
            newmemo = {}
            for node, id in self.memo.items():
                node = Node(node.f, tuple(b if arg == a else arg for arg in node.args))
                # oh actually we might get a collision because we're performing rebuilding here
                # do the parent and then start over?
                if id == a:
                    newmemo[node] = b
                else:
                    newmemo[node] = id
        return EGraph(newmemo)
        
```

```python
class CoEgraph:
    comemo : dict[Id, set[Node]]

    def add_app(self, )
        
    def define(self, f):
        id = len(self.comemo)
        node = f(id) # ???

    def union(self, a : Id, b : Id) -> Id:

    def coequation(self, ) # assert a and b are bisimilar?
```

# cocaml / capsules

(value, env) pairs
Is everything uniformly that?
(x, [x -> y, y -> 3]) ?

type tuple[str, locals]

def step

In an evaluator, the value returned by a variable is not env[x] but instead (x, env)? Lazy lookup

It is a lot like a partial evaluator. Hmm.

So do even arith expr change?

```python
def interp(e,env):
    match e:
        case ("lit", v):
            return v
        case ("var", name):
            return (e, env)
        case ("add", e1, e2):
            v1 = interp(e1, env)
            v2 = interp(e2, env)
            if isinstance(v1, int) and isinstance(v2, int):
                return v1 + v2
            else:
                return (("add", v1, v2), env)


```

    ---------------------------------------------------------------------------

    TypeError                                 Traceback (most recent call last)

    Cell In[22], line 15
         12             else:
         13                 return (("add", v1, v2), env)
    ---> 15 interp(("add", ("lit", 1), ("lit", 2)))


    TypeError: interp() missing 1 required positional argument: 'env'

<> = None?

```python
from kdrag.all import *

x,y = smt.Ints("x y")

ex1 = (x, {x : y, y : smt.IntVal(3)})
#def step(c):
#    return (smt.substitute(c[0], *[(x, t) for x,t in c[1].items() if t is not None], c[1])
def step(c):
    return (smt.substitute(c[0], *c[1].items(), c[1])

step(step(ex1))

# mutation is important to them. Different than rebinding? Not capture avoiding
def set_(c, x, v):
    return (c[0], {**c[1], x: v})

# def solver





```

```python
type Capsule = tuple[str, dict]

def step(c):
    if isinstance(c[0], str):
        return (eval(c[0], c[1]),c[1])
    else:
        return c

step(step(step(("x", {"x" : "step((y, locals()))", "y" : 3, "step" : step}))))








```

    ((3,
      {'x': 'step((y, locals()))',
       'y': 3,
       'step': <function __main__.step(c)>,
       '__builtins__': {'__name__': 'builtins',
        '__doc__': "Built-in functions, types, exceptions, and other objects.\n\nThis module provides direct access to all 'built-in'\nidentifiers of Python; for example, builtins.len is\nthe full name for the built-in function len().\n\nThis module is not normally accessed explicitly by most\napplications, but can be useful in modules that provide\nobjects with the same name as a built-in value, but in\nwhich the built-in of that name is also needed.",
        '__package__': '',
        '__loader__': _frozen_importlib.BuiltinImporter,
        '__spec__': ModuleSpec(name='builtins', loader=<class '_frozen_importlib.BuiltinImporter'>, origin='built-in'),
        '__build_class__': <function __build_class__>,
        '__import__': <function __import__(name, globals=None, locals=None, fromlist=(), level=0)>,
        'abs': <function abs(x, /)>,
        'all': <function all(iterable, /)>,
        'any': <function any(iterable, /)>,
        'ascii': <function ascii(obj, /)>,
        'bin': <function bin(number, /)>,
        'breakpoint': <function breakpoint>,
        'callable': <function callable(obj, /)>,
        'chr': <function chr(i, /)>,
        'compile': <function compile(source, filename, mode, flags=0, dont_inherit=False, optimize=-1, *, _feature_version=-1)>,
        'delattr': <function delattr(obj, name, /)>,
        'dir': <function dir>,
        'divmod': <function divmod(x, y, /)>,
        'eval': <function eval(source, globals=None, locals=None, /)>,
        'exec': <function exec(source, globals=None, locals=None, /, *, closure=None)>,
        'format': <function format(value, format_spec='', /)>,
        'getattr': <function getattr>,
        'globals': <function globals()>,
        'hasattr': <function hasattr(obj, name, /)>,
        'hash': <function hash(obj, /)>,
        'hex': <function hex(number, /)>,
        'id': <function id(obj, /)>,
        'input': <bound method Kernel.raw_input of <ipykernel.ipkernel.IPythonKernel object at 0x73b4cbc29640>>,
        'isinstance': <function isinstance(obj, class_or_tuple, /)>,
        'issubclass': <function issubclass(cls, class_or_tuple, /)>,
        'iter': <function iter>,
        'aiter': <function aiter(async_iterable, /)>,
        'len': <function len(obj, /)>,
        'locals': <function locals()>,
        'max': <function max>,
        'min': <function min>,
        'next': <function next>,
        'anext': <function anext>,
        'oct': <function oct(number, /)>,
        'ord': <function ord(c, /)>,
        'pow': <function pow(base, exp, mod=None)>,
        'print': <function print(*args, sep=' ', end='\n', file=None, flush=False)>,
        'repr': <function repr(obj, /)>,
        'round': <function round(number, ndigits=None)>,
        'setattr': <function setattr(obj, name, value, /)>,
        'sorted': <function sorted(iterable, /, *, key=None, reverse=False)>,
        'sum': <function sum(iterable, /, start=0)>,
        'vars': <function vars>,
        'None': None,
        'Ellipsis': Ellipsis,
        'NotImplemented': NotImplemented,
        'False': False,
        'True': True,
        'bool': bool,
        'memoryview': memoryview,
        'bytearray': bytearray,
        'bytes': bytes,
        'classmethod': classmethod,
        'complex': complex,
        'dict': dict,
        'enumerate': enumerate,
        'filter': filter,
        'float': float,
        'frozenset': frozenset,
        'property': property,
        'int': int,
        'list': list,
        'map': map,
        'object': object,
        'range': range,
        'reversed': reversed,
        'set': set,
        'slice': slice,
        'staticmethod': staticmethod,
        'str': str,
        'super': super,
        'tuple': tuple,
        'type': type,
        'zip': zip,
        '__debug__': True,
        'BaseException': BaseException,
        'BaseExceptionGroup': BaseExceptionGroup,
        'Exception': Exception,
        'GeneratorExit': GeneratorExit,
        'KeyboardInterrupt': KeyboardInterrupt,
        'SystemExit': SystemExit,
        'ArithmeticError': ArithmeticError,
        'AssertionError': AssertionError,
        'AttributeError': AttributeError,
        'BufferError': BufferError,
        'EOFError': EOFError,
        'ImportError': ImportError,
        'LookupError': LookupError,
        'MemoryError': MemoryError,
        'NameError': NameError,
        'OSError': OSError,
        'ReferenceError': ReferenceError,
        'RuntimeError': RuntimeError,
        'StopAsyncIteration': StopAsyncIteration,
        'StopIteration': StopIteration,
        'SyntaxError': SyntaxError,
        'SystemError': SystemError,
        'TypeError': TypeError,
        'ValueError': ValueError,
        'Warning': Warning,
        'FloatingPointError': FloatingPointError,
        'OverflowError': OverflowError,
        'ZeroDivisionError': ZeroDivisionError,
        'BytesWarning': BytesWarning,
        'DeprecationWarning': DeprecationWarning,
        'EncodingWarning': EncodingWarning,
        'FutureWarning': FutureWarning,
        'ImportWarning': ImportWarning,
        'PendingDeprecationWarning': PendingDeprecationWarning,
        'ResourceWarning': ResourceWarning,
        'RuntimeWarning': RuntimeWarning,
        'SyntaxWarning': SyntaxWarning,
        'UnicodeWarning': UnicodeWarning,
        'UserWarning': UserWarning,
        'BlockingIOError': BlockingIOError,
        'ChildProcessError': ChildProcessError,
        'ConnectionError': ConnectionError,
        'FileExistsError': FileExistsError,
        'FileNotFoundError': FileNotFoundError,
        'InterruptedError': InterruptedError,
        'IsADirectoryError': IsADirectoryError,
        'NotADirectoryError': NotADirectoryError,
        'PermissionError': PermissionError,
        'ProcessLookupError': ProcessLookupError,
        'TimeoutError': TimeoutError,
        'IndentationError': IndentationError,
        'IndexError': IndexError,
        'KeyError': KeyError,
        'ModuleNotFoundError': ModuleNotFoundError,
        'NotImplementedError': NotImplementedError,
        'RecursionError': RecursionError,
        'UnboundLocalError': UnboundLocalError,
        'UnicodeError': UnicodeError,
        'BrokenPipeError': BrokenPipeError,
        'ConnectionAbortedError': ConnectionAbortedError,
        'ConnectionRefusedError': ConnectionRefusedError,
        'ConnectionResetError': ConnectionResetError,
        'TabError': TabError,
        'UnicodeDecodeError': UnicodeDecodeError,
        'UnicodeEncodeError': UnicodeEncodeError,
        'UnicodeTranslateError': UnicodeTranslateError,
        'ExceptionGroup': ExceptionGroup,
        'EnvironmentError': OSError,
        'IOError': OSError,
        'open': <function _io.open(file, mode='r', buffering=-1, encoding=None, errors=None, newline=None, closefd=True, opener=None)>,
        'copyright': Copyright (c) 2001-2023 Python Software Foundation.
        All Rights Reserved.
        
        Copyright (c) 2000 BeOpen.com.
        All Rights Reserved.
        
        Copyright (c) 1995-2001 Corporation for National Research Initiatives.
        All Rights Reserved.
        
        Copyright (c) 1991-1995 Stichting Mathematisch Centrum, Amsterdam.
        All Rights Reserved.,
        'credits':     Thanks to CWI, CNRI, BeOpen.com, Zope Corporation and a cast of thousands
            for supporting Python development.  See www.python.org for more information.,
        'license': Type license() to see the full license text,
        'help': Type help() for interactive help, or help(object) for help about object.,
        'execfile': <function _pydev_bundle._pydev_execfile.execfile(file, glob=None, loc=None)>,
        'runfile': <function _pydev_bundle.pydev_umd.runfile(filename, args=None, wdir=None, namespace=None)>,
        '__IPYTHON__': True,
        'display': <function IPython.core.display_functions.display(*objs, include=None, exclude=None, metadata=None, transient=None, display_id=None, raw=False, clear=False, **kwargs)>,
        'get_ipython': <bound method InteractiveShell.get_ipython of <ipykernel.zmqshell.ZMQInteractiveShell object at 0x73b4c8173710>>}}),
     {'x': 'step((y, locals()))',
      'y': 3,
      'step': <function __main__.step(c)>,
      '__builtins__': {'__name__': 'builtins',
       '__doc__': "Built-in functions, types, exceptions, and other objects.\n\nThis module provides direct access to all 'built-in'\nidentifiers of Python; for example, builtins.len is\nthe full name for the built-in function len().\n\nThis module is not normally accessed explicitly by most\napplications, but can be useful in modules that provide\nobjects with the same name as a built-in value, but in\nwhich the built-in of that name is also needed.",
       '__package__': '',
       '__loader__': _frozen_importlib.BuiltinImporter,
       '__spec__': ModuleSpec(name='builtins', loader=<class '_frozen_importlib.BuiltinImporter'>, origin='built-in'),
       '__build_class__': <function __build_class__>,
       '__import__': <function __import__(name, globals=None, locals=None, fromlist=(), level=0)>,
       'abs': <function abs(x, /)>,
       'all': <function all(iterable, /)>,
       'any': <function any(iterable, /)>,
       'ascii': <function ascii(obj, /)>,
       'bin': <function bin(number, /)>,
       'breakpoint': <function breakpoint>,
       'callable': <function callable(obj, /)>,
       'chr': <function chr(i, /)>,
       'compile': <function compile(source, filename, mode, flags=0, dont_inherit=False, optimize=-1, *, _feature_version=-1)>,
       'delattr': <function delattr(obj, name, /)>,
       'dir': <function dir>,
       'divmod': <function divmod(x, y, /)>,
       'eval': <function eval(source, globals=None, locals=None, /)>,
       'exec': <function exec(source, globals=None, locals=None, /, *, closure=None)>,
       'format': <function format(value, format_spec='', /)>,
       'getattr': <function getattr>,
       'globals': <function globals()>,
       'hasattr': <function hasattr(obj, name, /)>,
       'hash': <function hash(obj, /)>,
       'hex': <function hex(number, /)>,
       'id': <function id(obj, /)>,
       'input': <bound method Kernel.raw_input of <ipykernel.ipkernel.IPythonKernel object at 0x73b4cbc29640>>,
       'isinstance': <function isinstance(obj, class_or_tuple, /)>,
       'issubclass': <function issubclass(cls, class_or_tuple, /)>,
       'iter': <function iter>,
       'aiter': <function aiter(async_iterable, /)>,
       'len': <function len(obj, /)>,
       'locals': <function locals()>,
       'max': <function max>,
       'min': <function min>,
       'next': <function next>,
       'anext': <function anext>,
       'oct': <function oct(number, /)>,
       'ord': <function ord(c, /)>,
       'pow': <function pow(base, exp, mod=None)>,
       'print': <function print(*args, sep=' ', end='\n', file=None, flush=False)>,
       'repr': <function repr(obj, /)>,
       'round': <function round(number, ndigits=None)>,
       'setattr': <function setattr(obj, name, value, /)>,
       'sorted': <function sorted(iterable, /, *, key=None, reverse=False)>,
       'sum': <function sum(iterable, /, start=0)>,
       'vars': <function vars>,
       'None': None,
       'Ellipsis': Ellipsis,
       'NotImplemented': NotImplemented,
       'False': False,
       'True': True,
       'bool': bool,
       'memoryview': memoryview,
       'bytearray': bytearray,
       'bytes': bytes,
       'classmethod': classmethod,
       'complex': complex,
       'dict': dict,
       'enumerate': enumerate,
       'filter': filter,
       'float': float,
       'frozenset': frozenset,
       'property': property,
       'int': int,
       'list': list,
       'map': map,
       'object': object,
       'range': range,
       'reversed': reversed,
       'set': set,
       'slice': slice,
       'staticmethod': staticmethod,
       'str': str,
       'super': super,
       'tuple': tuple,
       'type': type,
       'zip': zip,
       '__debug__': True,
       'BaseException': BaseException,
       'BaseExceptionGroup': BaseExceptionGroup,
       'Exception': Exception,
       'GeneratorExit': GeneratorExit,
       'KeyboardInterrupt': KeyboardInterrupt,
       'SystemExit': SystemExit,
       'ArithmeticError': ArithmeticError,
       'AssertionError': AssertionError,
       'AttributeError': AttributeError,
       'BufferError': BufferError,
       'EOFError': EOFError,
       'ImportError': ImportError,
       'LookupError': LookupError,
       'MemoryError': MemoryError,
       'NameError': NameError,
       'OSError': OSError,
       'ReferenceError': ReferenceError,
       'RuntimeError': RuntimeError,
       'StopAsyncIteration': StopAsyncIteration,
       'StopIteration': StopIteration,
       'SyntaxError': SyntaxError,
       'SystemError': SystemError,
       'TypeError': TypeError,
       'ValueError': ValueError,
       'Warning': Warning,
       'FloatingPointError': FloatingPointError,
       'OverflowError': OverflowError,
       'ZeroDivisionError': ZeroDivisionError,
       'BytesWarning': BytesWarning,
       'DeprecationWarning': DeprecationWarning,
       'EncodingWarning': EncodingWarning,
       'FutureWarning': FutureWarning,
       'ImportWarning': ImportWarning,
       'PendingDeprecationWarning': PendingDeprecationWarning,
       'ResourceWarning': ResourceWarning,
       'RuntimeWarning': RuntimeWarning,
       'SyntaxWarning': SyntaxWarning,
       'UnicodeWarning': UnicodeWarning,
       'UserWarning': UserWarning,
       'BlockingIOError': BlockingIOError,
       'ChildProcessError': ChildProcessError,
       'ConnectionError': ConnectionError,
       'FileExistsError': FileExistsError,
       'FileNotFoundError': FileNotFoundError,
       'InterruptedError': InterruptedError,
       'IsADirectoryError': IsADirectoryError,
       'NotADirectoryError': NotADirectoryError,
       'PermissionError': PermissionError,
       'ProcessLookupError': ProcessLookupError,
       'TimeoutError': TimeoutError,
       'IndentationError': IndentationError,
       'IndexError': IndexError,
       'KeyError': KeyError,
       'ModuleNotFoundError': ModuleNotFoundError,
       'NotImplementedError': NotImplementedError,
       'RecursionError': RecursionError,
       'UnboundLocalError': UnboundLocalError,
       'UnicodeError': UnicodeError,
       'BrokenPipeError': BrokenPipeError,
       'ConnectionAbortedError': ConnectionAbortedError,
       'ConnectionRefusedError': ConnectionRefusedError,
       'ConnectionResetError': ConnectionResetError,
       'TabError': TabError,
       'UnicodeDecodeError': UnicodeDecodeError,
       'UnicodeEncodeError': UnicodeEncodeError,
       'UnicodeTranslateError': UnicodeTranslateError,
       'ExceptionGroup': ExceptionGroup,
       'EnvironmentError': OSError,
       'IOError': OSError,
       'open': <function _io.open(file, mode='r', buffering=-1, encoding=None, errors=None, newline=None, closefd=True, opener=None)>,
       'copyright': Copyright (c) 2001-2023 Python Software Foundation.
       All Rights Reserved.
       
       Copyright (c) 2000 BeOpen.com.
       All Rights Reserved.
       
       Copyright (c) 1995-2001 Corporation for National Research Initiatives.
       All Rights Reserved.
       
       Copyright (c) 1991-1995 Stichting Mathematisch Centrum, Amsterdam.
       All Rights Reserved.,
       'credits':     Thanks to CWI, CNRI, BeOpen.com, Zope Corporation and a cast of thousands
           for supporting Python development.  See www.python.org for more information.,
       'license': Type license() to see the full license text,
       'help': Type help() for interactive help, or help(object) for help about object.,
       'execfile': <function _pydev_bundle._pydev_execfile.execfile(file, glob=None, loc=None)>,
       'runfile': <function _pydev_bundle.pydev_umd.runfile(filename, args=None, wdir=None, namespace=None)>,
       '__IPYTHON__': True,
       'display': <function IPython.core.display_functions.display(*objs, include=None, exclude=None, metadata=None, transient=None, display_id=None, raw=False, clear=False, **kwargs)>,
       'get_ipython': <bound method InteractiveShell.get_ipython of <ipykernel.zmqshell.ZMQInteractiveShell object at 0x73b4c8173710>>}})

# minimization

I want to try the
<https://www.philipzucker.com/naive_automata/>

Rational lists / trees.
Solvers like cocaml?

```python
from dataclasses import dataclass
from typing import Optional
type Id = int
@dataclass(frozen=True)
class Obs:
    accept: bool
    a_trans : Id
    b_trans : Id

    def map(self, f):
        return Obs(self.accept, f(self.a_trans), f(self.b_trans))
    

ex1 = {
    1 : Obs(False, 2, 3),
    2 : Obs(False, 4, 3),
    3 : Obs(False, 5, 3),
    4 : Obs(True, 5, 4),
    5 : Obs(True, 4, 4)
}

def unfold(a : dict[Id, Obs]):
    return {id: obs.map(lambda id2: a[id2]) for id, obs in a.items()}
def gen_of(a, st : Id): # unfold? corec?
    while True:
        obs = a[st]
        ab = yield obs.accept
        if ab == "a":
            st = obs.a_trans
        elif ab == "b":
            st = obs.b_trans


def is_bisim(a1, a2): ...
def is_bisim(a, st1, st2): ...
def is_bisim(R, a, a1): ...





```

```python
from collections import namedtuple
Obs = namedtuple('Obs', ['accept', 'a_trans', 'b_trans'])
State = int
Automaton = dict[State, Obs]

ex1 : Automaton = {
  1 : Obs(False, 2, 3),
  2 : Obs(False, 4, 3),
  3 : Obs(False, 5, 3),
  4 : Obs(True, 5, 4),
  5 : Obs(True, 4, 4)
}

```

```python
import itertools
Partition = list[State]
PartMap = dict[State, Partition]

def dfa_map(f : PartMap, x : Automaton):
  # map function for observations. 
  return {n : Obs(accept, f[a], f[b])  for n, (accept, a, b) in x.items()}

states : list[State] = list(ex1.keys())
partmap = {i : states for i in range(1,6)}


for i in range(6): # iterate to stabilization
    print("partition map: ", partmap)
    # obs is the Automaton map with state ids replaced by  
    obs = dfa_map(partmap, ex1)
    partmap = {}
    for group_obs, equivs in itertools.groupby(sorted(states, lambda state: obs[state]), lambda state: obs[state]):
        equivs = list(equivs)
        for id_ in equivs:
            partmap[id_] = equivs
```

# Sam's example

Sam says:

```
i := cons(1, i)
j := cons(1, if (j<20) then i else k)
k := cons(0, if (j<20) then (k+1) else (k+2))
```

```
start_term      
j < const(20)                                       by start_term definition
cons(1, ite(j < const(20), i, k)) < const(20)       by j expand
cons(1 < 20, ite(j < const(20), i, k) < const(20))  by  < step
cons(true, ite(j < const(20), i, k) < const(20))    by  constant folding
cons(true, ite(start_term, i, k) < const(20))       by refold start_term


ite(cons(true, cs), cons(e,es), cons(t,ts)) = cons(e, ite(true, es, ts)) 
```

```
# copattern style?
ret(loop(I,J,K)) := None
ret(if_head(I,J,K)) := None
ret(done(I,J,K)) := Some J
next(loop(I,J,K)) := if K < 100 then if_head(I,J,K) else done(I,J,K)
next(...) := ...
next(...) := ...


# cons style
myfun := cons(?, loop(1,1,0))
loop(I,J,K) := cons(None, if K < 100 then if_head(I,J,K) else done(I,J,K))
if_head(I,J,K) := cons(None, if J < 20 then then_block(I,J,K) else else_blk(I,J,K))
then_block(I,J,K) := cons(None, loop(i,i,k+1))
else_block(I,J,K) := cons(None, loop(I, K, K+2))
... and so on
done(I,J,K) := cons(Some J, done(I,J,K))
```

The state is the loop(i,j,k)  stuff. I guess I was kind of thinking that I was going to consider state to be observable at each jump so instead that would be `loop(I,J,K) := cons(loop_obs(i,j,k), if K < 100 then if_head(i,j,k) else done(I,J,K)` .
I'm missing  to match the example
That's the initialization
It's maybe some kind of structure of arrays style refactoring
You have 3 streams, whereas I have 1 stream of records

I think it's neat that the stream of records can be heterogenous, like block arguments can be

```ocaml
type BlockObs = loop_obs of int * int * int | if_head_obs of int*int*int | .. and so on
type BlockStream = Cons of BlockObs * BlockStream

let rec loop (i j k : int) : BlockStream = Cons (loop_obs (i,j,k), if k < 100 then if_head i j k else done i j k)
and let if_head : int -> int -> int -> BlockStream
... and so on
```

Wait, so does HOL have induction baked in?

```python
sdg = kd.define("sdg", [d], smt.Or(d == -1, d == 0, d == 1))
phi = kd.define("phi", [S], smt.Lambda([S], smt.Exists([x, d], sdg(d), S[x], smt.Lambda([y], smt.And(x + d / 2 == y )))))

Prefix(phi)
GFP(phi)
LFP(phi)




```

Ok, so how can I define add inductively over the ints?

```python
def factF(S):
    return smt.Lambda([x,y], smt.Or(smt.And(x == 0, y == 1), smt.And(x > 0, S[x-1, ] * x == y)))
```

```python
from kdrag.all import *

x,y,z = smt.Ints("x y z")
def addF(S):
    return smt.Lambda([x,y,z], 
        smt.Or(
            smt.And(x == 0, y == z),
            smt.And(x > 0, S[x-1,y,z-1])
        )
    )
add = kd.define(kd.LFP(addF, sort=))

exists_add = smt.ForAll([x,y], smt.Exists([z], add(x,y,z)))
unique_add = smt.ForAll([x,y,z,z1], add(x,y,z), add(x,y,z1), z == z1)

```

    ---------------------------------------------------------------------------

    ValueError                                Traceback (most recent call last)

    Cell In[2], line 11
          4 def addF(S):
          5     return smt.Lambda([x,y,z], 
          6         smt.Or(
          7             smt.And(x == 0, y == z),
          8             S[x-1,y,z-1]
          9         )
         10     )
    ---> 11 kd.LFP(addF)


    File ~/vibe_coding/knuck_anal/knuckledragger/src/kdrag/__init__.py:418, in LFP(F, sort)
        409 def LFP(F, sort=None):
        410     """
        411     >>> ZSet = smt.SetSort(smt.IntSort())
        412     >>> F = smt.Array("F", ZSet, ZSet)
       (...)    416                 Implies(subset(F[A!...], A!...), A!...[x!...])))
        417     """
    --> 418     SetSort = _infer_sort(F, sort)
        419     x = smt.FreshConst(SetSort.domain(), prefix="x")
        420     A = smt.FreshConst(SetSort, prefix="A")


    File ~/vibe_coding/knuck_anal/knuckledragger/src/kdrag/__init__.py:384, in _infer_sort(F, sort)
        382     return S
        383 else:
    --> 384     raise ValueError("sort must be provided for non-function F")


    ValueError: sort must be provided for non-function F

Also natR

cut out stream
cut out lists from Int -> Option

Finite Sets of Ints

```python
#even
from kdrag.all import *
ZSet = smt.SetSort(smt.IntSort())
ZSetMap = smt.ArraySort(ZSet, ZSet)
n = smt.Int("n")
def evenF(S):
    return smt.Lambda([n], smt.Or(n == 0, S[n-2]))
S,S1,S2 = smt.Consts("S S1 S2", ZSet)
def Monotone(F):
    return smt.ForAll([S1,S2], S1 <= S2, F(S1) <= F(S2))
def LFP(F):
    return smt.Lambda([n], smt.ForAll([S], F(S) <= S, S[n]))
    #return smt.Lambda([S], smt.ForAll([S1], F(S1) <= S1, S <= S1))

even = kd.define("even", [], LFP(evenF))
even_0 = kd.prove(even[0], by=[even.defn])
even_succ2 = kd.prove(smt.ForAll([n], even[n], even[n+2]), by=[even.defn])
P = smt.Const("P", ZSet)
even_induct = smt.ForAll([P], P[0], smt.ForAll([n], P[n], P[n+2]), 
                         smt.ForAll([n], even[n], P[n]))


def natF(S):
    return smt.Lambda([n], smt.Or(n == 0, S[n-1]))
nat = kd.define("nat", [], LFP(natF))
nat_zero = kd.prove(nat[0], by=[nat.defn])
nat_succ = kd.prove(smt.ForAll([n], nat[n], nat[n+1]), by=[nat.defn])

nat_induct = kd.prove(smt.ForAll([P], smt.Implies(natF(P) <= P, 
                                   nat <= P)), by=nat.defn)
nat_induct     


#nat_induct2 = kd.prove(smt.ForAll([P], P[0], smt.ForAll([n], P[n], P[n+1]),
#                        smt.ForAll([n], nat[n], P[n])), by=nat_induct)
@kd.Theorem(smt.ForAll([P], P[0], smt.ForAll([n], P[n], P[n+1]),
                        smt.ForAll([n], nat[n], P[n])))
def nat_induct2(l):
    P = l.fix()
    l.intros()
    l.split(-1)
    n = l.fix()
    l.have(natF(P) <= P)
    l.auto()
    l.have(nat <= P, by=[nat_induct])
    l.auto()
    l.qed()

    





```

```python
import kdrag.theories.set as set_
from kdrag.all import *
#def intF(S):
#    return smt.Lambda([n], smt.Or(n == 0, S[n-1], S[n+1]))
S = smt.Const("S", smt.SetSort(smt.IntSort()))
n = smt.Int("n")
P = smt.Const("P", smt.SetSort(smt.IntSort()))
intF = smt.Lambda([S], smt.Lambda([n], smt.Or(n == 0, S[n-1], S[n+1])))
int_ = kd.define("int", [], kd.LFP(intF))

int_0 = kd.prove(int_[0], by=[int_.defn])
int_succ = kd.prove(smt.ForAll([n], int_[n], int_[n+1]), by=[int_.defn])
int_pred = kd.prove(smt.ForAll([n], int_[n], int_[n-1]), by=[int_.defn])
int_induct = kd.prove(smt.ForAll([P], smt.Implies(intF(P) <= P, int_ <= P)), by=int_.defn)
```

```python
int_prefix = kd.prove(kd.PreFix(intF, int_), by=[int_.defn]) # introduction rules
int_postfix = kd.prove(kd.PostFix(intF, int_), by=[int_.defn]) # case rules
int_fix = kd.prove(intF(int_) == int_, by=[int_.defn])
```

```python
def define_indrel(name, F):
    rel = kd.define(name, [], kd.LFP(F))
    constructors = kd.prove(kd.PreFix(F, rel), by=[rel.defn])
    cases = kd.prove(kd.PostFix(F, rel), by=[rel.defn]) 
    induct = kd.prove(smt.ForAll([P], smt.Implies(kd.PreFix(F, P), rel <= P)), by=[rel.defn])
    return rel, constructors, cases, induct

```

IntVec(n) - cut it out of Seq

Parameters?

FiniteSets
well founded

Defining function by first defining their graph, showing uniqueness

```python
def FinF(S):
    return smt.Lambda([A], smt.Or(A == smt.EmptySet(smt.IntSort()),
                                  smt.Exists[[B, n], S[B], A == smt.SetAdd(B, n)]))

```

```python
# a sufficient universe to cut some wild stuff out of?
def Univ(*A):
    dt = kd.Inductive("Univ_" + "_".join([A.name() for A in A]))
    for S in A:
        dt.add_constructor(A.name(), A)
    dt.declare("Seq", smt.SeqSort(dt))
    #dt.declare("Arr", smt.ArraySort(A, dt))
    # dt.declare("ISeq", smt.ArraySort(smt.IntSort(), dt))
    #dt.declare("Int", smt.IntSort())   
    #dt.declare("Bool", smt.BoolSort()) # redundant.
    return dt.create()

```

```python
def VecF(S):
    # hmm. I need to recruse into Vec(n-1)?
    return smt.Lambda([l], )
```

```python
@kd.PTheorem(int_[n])
def int_all(l):
    l.have(intF(int_) <= int_, by=[int_.defn])
    l.have(int_ <= int_, by=[int_induct])
```

    Next Goal:
     [subset(Lambda(n, Or(n == 0, int[n - 1], int[n + 1])), int), subset(int, int)]
    ?|= int[n]

```python
@kd.Theorem(smt.ForAll([P], smt.ForAll([n], P[n], P[n-1]), P[0], smt.ForAll([n], P[n], P[n+1]),
                        smt.ForAll([n], int_[n], P[n])))
def int_induct2(l):
    P = l.fix()
    l.intros()
    l.have(intF(P) <= P, by=[])
    l.have(int_ <= P, by=[int_induct])
    l.auto(by=[int_.defn])
    l.qed()

```

    ---------------------------------------------------------------------------

    LemmaError                                Traceback (most recent call last)

    File ~/vibe_coding/knuck_anal/knuckledragger/src/kdrag/tactics.py:315, in prove(thm, fixes, assumes, by, admit, timeout, dump, solver, contracts, unfold)
        314 try:
    --> 315     pf = kd.kernel.prove(
        316         thm, by=by_list, timeout=timeout, dump=dump, solver=solver, admit=admit
        317     )
        318     if fixes:


    File ~/vibe_coding/knuck_anal/knuckledragger/src/kdrag/kernel.py:161, in prove(thm, by, admit, timeout, dump, solver)
        160         raise LemmaError(thm, "Countermodel", s.model())
    --> 161     raise LemmaError("prove", thm, res)
        162 else:


    LemmaError: ('prove', Implies(And(And(ForAll(n, Implies(P!336[n], P!336[n - 1])),
                    P!336[0],
                    ForAll(n, Implies(P!336[n], P!336[n + 1]))),
                subset(Lambda(n,
                              Or(n == 0,
                                 P!336[n - 1],
                                 P!336[n + 1])),
                       P!336),
                subset(int, P!336)),
            ForAll(n, P!336[n])), unknown)

    
    During handling of the above exception, another exception occurred:


    TimeoutError                              Traceback (most recent call last)

    File ~/vibe_coding/knuck_anal/knuckledragger/src/kdrag/tactics.py:960, in ProofState.auto(self, **kwargs)
        959 try:
    --> 960     pf = kd.prove(smt.Implies(smt.And(ctx), goal), **kwargs)
        961 except Exception as _e:


    File ~/vibe_coding/knuck_anal/knuckledragger/src/kdrag/tactics.py:324, in prove(thm, fixes, assumes, by, admit, timeout, dump, solver, contracts, unfold)
        323 if time.perf_counter() - start_time > timeout / 1000:
    --> 324     raise TimeoutError(
        325         "Timeout. Maybe you have given `prove` too many or not enough lemmas?"
        326     )
        327 elif isinstance(thm, smt.QuantifierRef):


    TimeoutError: Timeout. Maybe you have given `prove` too many or not enough lemmas?

    
    During handling of the above exception, another exception occurred:


    ValueError                                Traceback (most recent call last)

    Cell In[10], line 1
    ----> 1 @kd.Theorem(smt.ForAll([P], smt.ForAll([n], P[n], P[n-1]), P[0], smt.ForAll([n], P[n], P[n+1]),
          2                         smt.ForAll([n], P[n])))
          3 def int_induct2(l):
          4     P = l.fix()
          5     l.intros()


    File ~/vibe_coding/knuck_anal/knuckledragger/src/kdrag/tactics.py:2091, in Theorem.<locals>.res(f)
       2089 else:
       2090     l = kd.Lemma(goal1)
    -> 2091 f(l)
       2092 pf = l.qed()
       2093 if timing:


    Cell In[10], line 8, in int_induct2(l)
          6 l.have(intF(P) <= P, by=[])
          7 l.have(int_ <= P, by=[int_induct])
    ----> 8 l.auto(by=[int_.defn])
          9 l.qed()


    File ~/vibe_coding/knuck_anal/knuckledragger/src/kdrag/tactics.py:962, in ProofState.auto(self, **kwargs)
        960     pf = kd.prove(smt.Implies(smt.And(ctx), goal), **kwargs)
        961 except Exception as _e:
    --> 962     raise ValueError("auto failed on goal", goalctx)
        963 self.add_lemma(pf)
        964 self.pop_goal()


    ValueError: ('auto failed on goal', [P!336];
    [And(ForAll(n, Implies(P!336[n], P!336[n - 1])),
        P!336[0],
        ForAll(n, Implies(P!336[n], P!336[n + 1]))),
     subset(Lambda(n, Or(n == 0, P!336[n - 1], P!336[n + 1])),
           P!336),
     subset(int, P!336)]
    ?|= ForAll(n, P!336[n]))

```python
@kd.Theorem(smt.ForAll([P], smt.ForAll([n], P[n], P[n-1]), P[0], smt.ForAll([n], P[n], P[n+1]),
                        smt.ForAll([n], int_[n], P[n])))
```

Hmm. So these sets are indcutive by defintion.
We can prove nat[n] => n >= 0, but then other dirction seems hard without primitive induction?

Video says  is more useful greatest fixed point characterization?

def natG(P):
    return natF(nat & P)
LFP(natG)

```python
@kd.Theorem(smt.ForAll([n], int_[n]))
def nat_all(l):
    n = l.fix()
    l.unfold(int_)
    l.beta()
    A = l.fix()
    l.intros()
    l.induct(n)
    n = l.fix()
    l.auto()
    l.auto()
    l.auto()
    l.qed()
```

```python
def natRF(S):
    x = smt.Real("x")
    return smt.Lambda([n], smt.Or(n == 0, S[n-1]))

natR = kd.define("natR", )


#kd.prove(LFP(evenF)(0))
#kd.prove(LFP(evenF)(2))
#kd.prove(smt.Implies(LFP(evenF)(n), LFP(evenF)(n+2)))
#kd.prove(smt.Implies(LFP(evenF)(n), LFP(evenF)(n+1)))
#kd.prove(LFP(evenF)(-2))
#kd.prove(LFP(evenF)(1))
```

```python
from kdrag.modal
def Signal(A):
    return smt.ArraySort(smt.IntSort(), A)
i,j,k = smt.Consts("i j k", Signal(smt.IntSort()))

Stream 
j == cons(, PIf(j < 20, i, k)
cons = kd.define("cons", [x, s], smt.IF)

```

```python
from kdrag.all import *

Stream = smt.DeclareSort("Stream")
Cons = smt.Function("Cons", )

```

```python
class EGraph():
    memo : dict[ENode, EId]
    defn : dict[EId, EId] # ENode Enode, EId ENode, ENode EId. 
    def __init__(self):
    def add_enode(self, node):
    def add_definition(self, name, body):
    def union(self, a, b):
        

```

```python

```

```python
cell = []
from dataclasses import dataclass, field
@dataclass
class App():
    f: str
    args: list = field(default_factory=list)


def is_eq(t : App, s : App, table : frozenset[tuple[int, int]]=frozenset()):
    if (id(t), id(s)) in table:
        return True
    if t.f != s.f or len(t.args) != len(s.args):
        return False
    table |= {(id(t), id(s))}
    return all(is_eq(ta,sa, table) for ta, sa in zip(t.args, s.args))

def f(*args):
    return App("f", list(args))
finf = f()
finf.args = [finf]
x = App("x", [])
assert is_eq(f0, f0)
is_eq(f(x), finf)

finf2 = f(finf)
assert is_eq(finf2, finf)
assert not is_eq(finf2, f(x))

finf0 = f()
finf3 = f(f(finf0))
finf0.args = [finf3]

assert is_eq(finf0, finf3)
assert is_eq(finf2, finf3)
finf3
```

    App(f='f', args=[App(f='f', args=[App(f='f', args=[...])])])

```python
def is_subterm(t, s, table=frozenset()):
    # is_subterm is a lest fixed point though?
    if (id(t), id(s)) in table:
        return False
    if is_eq(t,s):
        return True
    table |= {(id(t), id(s))}
    return any(is_subterm(ta, s, table) for ta  in t.args)

def g(*args):
    return App("g", list(args))

assert is_subterm(g(finf), finf)
assert not is_subterm(finf, g(finf))
assert is_subterm(f(finf), finf)


```

```python
@dataclass
class Var():
    name: str

def pmatch(pat, t):
    ...
```

use CF trick in pattern matching?

pmatch and replace

drags?

```python
class Zipper():
    ...
```

Contexts are never infinite?

```python

def is_eq(t, s, table):


def is_subterm()
```
