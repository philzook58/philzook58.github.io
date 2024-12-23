---
title: Symbolic Execution by Overloading `__bool__`
date: 2024-12-23
---

A few months ago I saw a talk on buildit, <https://buildit.so/> a really neat project that achieves staged metaprogramming as a C++ library. I love the central tenets of being in a mainstream language and not requiring a modified compiler. Right on, brother. One thing I came away with was a neat trick for getting non-overloadable syntax to be overloadable.

The interesting observation, which seems clear in hindsight (the best observations are), is that bool conversion _is_ overloadable by writing a `__bool__` function on the Z3 class. With a little hackery, you can record all the paths through a piece of fairly pure python code. In this way you can simply achieve symbolic execution of python code without the usual expected rigamarole, or symbolically reflect python code as pure z3 expressions.

# Partial Evaluation and Metaprogramming Z3

I have noted for a while after tinkering with [MetaOCaml](https://okmij.org/ftp/ML/MetaOCaml.html) that metaprogramming z3 in python has a lot of the flavor of staged metaprogramming (big surprise? Maybe there's not much content to the observation).

Some metaprogramming frameworks or styles look very different from unstaged code. You explicitly call all sorts of weird functions to construct code obects.

A really cool flavor of staged metaprogramming takes the unstaged code and adds some annotations to get staged code. The more similar the staged code looks to the original, the better. It probably takes some kind of language level feature like quotation, overloading, or introspection to achieve this.

A canonical example of staged metaprogramming is unrolling a power function (Ershov). Here is a simple example of an unstaged recursive power function operating on regular python ints.

```python
def mypow(x : int, n : int):
    if n == 0:
        return 1
    else:
        return x * mypow(x, n-1)
    
assert mypow(2, 3) == 8
mypow(2,3)
```

    8

You can instead use very similar looking code to codegen code-strings. The python [f-strings](https://docs.python.org/3/reference/lexical_analysis.html#f-strings) feature (which are being continually improved. I'm hopeful for [tagged strings](https://peps.python.org/pep-0750/)) make for some nice quotation mechanism. What is very cute is that the following looks just like the above. We interpret the parameter `n` as being known as "compile time"/static and the parameter `x` as being known as "run time"/dynamic.

```python
def Code(t):return str
def mypow(x : Code(int), n : int) -> Code(int):
    if n == 0:
        return "1"
    else:
        return f"{x} * {mypow(x, n-1)}"

assert mypow("x",3)  == "x * x * x * 1"
mypow("x",3)
```

    'x * x * x * 1'

A very similar but more structure thing occurs if we consider z3 expressions to be "code". This actually gives us a tree thing to work with.

```python
import z3
def code(typ):
    if typ == int:
        return z3.IntSort()
def mypow(x : Code(int), n : int) -> Code(int):
    if n == 0:
        return 1
    else:
        return x * mypow(x, n-1)

x = z3.Int("x")
assert mypow(x, 3).eq(x*(x*(x*1)))
mypow(x,3)
```

x&middot;x&middot;x&middot;1

The role of "static" compile time is played by regular python values abd the role of "dynamic" is played by Z3 expressions. You can mush around things between compile and run time, doing more or less in the solver. Things like unrolling loops have a correspondence in unrolling quantifiers. Because z3 uses python's overloading, the same code can be used in the different ways with light annotations.

I think of there being 2 notable design points of symbolic execution / . Do you throw all the branches into the solver or do you throw only a single path/trace into the solver over many queries. The difference between these approaches could be seen as stage mushing. Is the return value of the branch condition a static or dynamic bool?

Some things in python really aren't overloadable though. `if-then-else` blocks, `while`, chained comparison, `and or not` operators are all not overloadable. So you need to change things around to use `z3.If`. This is kind of a bummer.

## Overloading `__bool__`

But actually, you can overload these features indirectly. When the conditions aren't bools, the overloadable `__bool__` function is called on the class. You can monkey patch in one to z3.

This alone doesn't quite get you there, you need to run the function in question multiple times to explore all the paths. This is a version of symbolic execution, which is of interest on its own.

You could probably do the same thing using the C++ Z3 bindings.

I find this particular interesting as a way of using python code as a DSL. For example, I was trying to use an "applicative" subset of python as a logic akin to how ACL2 uses a subset of common lisp <https://www.philipzucker.com/applicative_python/> but I was doing a traversal over the python AST, an ugly and verbose thing to do.

I've seen similar problems in the tensor compiling or MLIR worlds. People kind of want python syntax at least for playing around. It is quite difficult to get a maintainable system though.

```python
import random
from z3 import *
def symexec(*vs, limit=100):
    def wrapper(f):
        trace = []
        traces = []
        # a shared solver being pushed and popped is probably more efficient
        s = Solver()
        def branch(self):
            # branch gets called on every branch (every time a z3 expression is asked to be converted to a concrete bool)
            s.push()
            s.add(And(trace)) # TODO: I could move push pop around to avoid this full push
            # flip a coin. Probably that means any individual run will end.
            # If there are no loops, being more deterministic is fine.
            if random.random() < 0.5:
                take = True
            else:
                take = False
            # Is it possible to take the branch?
            s.add(self == take)
            res = s.check()
            s.pop()
            if res == sat:
                # It was possible to take the branch
                trace.append(self == take)
                return take
            else:
                # it was not possible to take the branch
                trace.append(self == (not take))
                return not take
        BoolRef.__bool__ = branch # monkey patch in the __bool__ overload
        for i in range(limit):
            if s.check() == unsat: # If no more branches possible, stop
                break
            trace = [] # reset the trace
            res = f(*vs) # run the function
            # res = z3.simplify(res) # might be nice.
            traces.append((trace,res)) # record the result of the run
            s.add(Not(And(trace))) # disallow exact trace again
        BoolRef.__bool__ = None
        return traces
    return wrapper




@symexec(z3.Int("x"))
def foo(x):
    if x > 3:
        if x == 4:
            return x
        else:
            return x - 2
    else:
        return x*3
    
foo
```

    [([(x > 3) == True, (x == 4) == True], x),
     ([(x > 3) == True, (x == 4) == False], x - 2),
     ([(x > 3) == False], x*3)]

We can get niceties like comparator chaining

```python
@symexec(Int("x"), Int("y"))
def comparison_example(x,y):
    return y - 3 < x < y + 4 or x > 3
comparison_example
```

    [([(y - 3 < x) == True, (x < y + 4) == True], x < y + 4),
     ([(y - 3 < x) == False, (y - 3 < x) == False], x > 3),
     ([(y - 3 < x) == True, (x < y + 4) == False], x > 3)]

Or match statements

```python
@symexec(Int("x"))
def matcher(x):
    match x:
        case 0:
            return 1
        case 2:
            return x + 14
        case _:
            return x * 2 
matcher
```

    [([(x == 0) == False, (x == 2) == False], x*2),
     ([(x == 0) == False, (x == 2) == True], x + 14),
     ([(x == 0) == True], 1)]

Or bounded whiles

```python
@symexec(Int("x"))
def bwhile(x):
    if x > 0 and x < 10:
        acc = 0
        while x > 0:
            x -= 2
            acc += x
        return acc
bwhile
```

    [([(x > 0) == False], None),
     ([(x > 0) == True, (x < 10) == True, (x > 0) == True, (x - 2 > 0) == False],
      0 + x - 2),
     ([(x > 0) == True,
       (x < 10) == True,
       (x > 0) == True,
       (x - 2 > 0) == True,
       (x - 2 - 2 > 0) == False],
      0 + x - 2 + x - 2 - 2),
     ([(x > 0) == True,
       (x < 10) == True,
       (x > 0) == True,
       (x - 2 > 0) == True,
       (x - 2 - 2 > 0) == True,
       (x - 2 - 2 - 2 > 0) == True,
       (x - 2 - 2 - 2 - 2 > 0) == False],
      0 + x - 2 + x - 2 - 2 + x - 2 - 2 - 2 + x - 2 - 2 - 2 - 2),
     ([(x > 0) == True, (x < 10) == False], None),
     ([(x > 0) == True,
       (x < 10) == True,
       (x > 0) == True,
       (x - 2 > 0) == True,
       (x - 2 - 2 > 0) == True,
       (x - 2 - 2 - 2 > 0) == True,
       (x - 2 - 2 - 2 - 2 > 0) == True,
       (x - 2 - 2 - 2 - 2 - 2 > 0) == False],
      0 +
      x - 2 +
      x - 2 - 2 +
      x - 2 - 2 - 2 +
      x - 2 - 2 - 2 - 2 +
      x - 2 - 2 - 2 - 2 - 2),
     ([(x > 0) == True,
       (x < 10) == True,
       (x > 0) == True,
       (x - 2 > 0) == True,
       (x - 2 - 2 > 0) == True,
       (x - 2 - 2 - 2 > 0) == False],
      0 + x - 2 + x - 2 - 2 + x - 2 - 2 - 2)]

We can also seek unbounded whiles, but then the output will be incomplete.

```python
@symexec(Int("x"), limit=5)
def bfor(x):
    acc = 0
    while x > 0:
        x -= 1
        acc += x
    return acc
bfor
```

    [([(x > 0) == False], 0),
     ([(x > 0) == True, (x - 1 > 0) == False], 0 + x - 1),
     ([(x > 0) == True,
       (x - 1 > 0) == True,
       (x - 1 - 1 > 0) == True,
       (x - 1 - 1 - 1 > 0) == False],
      0 + x - 1 + x - 1 - 1 + x - 1 - 1 - 1),
     ([(x > 0) == True,
       (x - 1 > 0) == True,
       (x - 1 - 1 > 0) == True,
       (x - 1 - 1 - 1 > 0) == True,
       (x - 1 - 1 - 1 - 1 > 0) == False],
      0 + x - 1 + x - 1 - 1 + x - 1 - 1 - 1 + x - 1 - 1 - 1 - 1),
     ([(x > 0) == True,
       (x - 1 > 0) == True,
       (x - 1 - 1 > 0) == True,
       (x - 1 - 1 - 1 > 0) == True,
       (x - 1 - 1 - 1 - 1 > 0) == True,
       (x - 1 - 1 - 1 - 1 - 1 > 0) == False],
      0 +
      x - 1 +
      x - 1 - 1 +
      x - 1 - 1 - 1 +
      x - 1 - 1 - 1 - 1 +
      x - 1 - 1 - 1 - 1 - 1)]

# Bits and Bobbles

If I want to be careful, I should make sure limit is not reached and also if the result is ever None, a return was being forgotten.

Could combine the technique with hypothesis to get concolic testing.

I could probably recapture loops by noticing we have returned to a previously seen position by inspecting the stack that called `__bool__`. It would be awkeard though. Maybe one could also do it by recording way more info in the overloads, but this is a lot more work.

<https://docs.python.org/3/library/codecs.html#codecs.register>
<https://docs.python.org/3/reference/import.html>
<https://news.ycombinator.com/item?id=41322758> python's preprocessor. Fiendish macros.

I have seen people do special stuff in jupyter. I don't rerally liek any of that

Nelli
Ast. Rewrite if elif else -> If
rewrite return to null?
Overloading kind of works, except
and or not to And Or Not
If
rewrite x <= y <= z

Some MLIR and other pytonh syntax using DSLs

- <https://github.com/makslevental/mlir-python-extras>
- <https://github.com/spcl/pymlir> - lark parse into mirrored thing
- <https://mlir.llvm.org/OpenMeetings/2023-12-21-PyDSL.pdf> pydsl
- <https://github.com/SRI-CSL/filia>
- <https://arxiv.org/pdf/2307.16080> nelli <https://github.com/makslevental/nelli> hmm. archived.
Maybe these techniques could be useful for z3 reification.
Rewrite AST + rewrite bytecode + overloading

exocompiler and others.
<https://cap.csail.mit.edu/sites/default/files/research-pdfs/Codon-%20A%20Compiler%20for%20High-Performance%20Pythonic%20Applications%20and%20DSLs.pdf> codon converts to llvm
<https://github.com/exaloop/codon>

could convert ifthenelse to `x if c else`.
Nah.

chococpy
codon
mypyc

buildit style

- <https://buildit.so/>
- <https://intimeand.space/docs/buildit.pdf>

Thermometer continuations

- <https://calwoo.github.io/posts/2020-02-12-thermometer_p1.html>
- <https://github.com/jkoppel/thermometer-continuations>
- <https://arxiv.org/abs/1710.10385> Capturing the Future by Replaying the Past

dialectica and probing. Pierre Marie-Pedrot

Symbolic execution by overloading __bool__

Honestly using C++ in this way might be on the table. It is not easy to symbolically execute C++. Klee of course. But klee is quite an effort.

Symcc has a partial evaluation vibe

Using the same idea for partial eval? The trace starts by setting some variables.
Concolic

Actually detecting the loops seems hard since it isn't that we reach the loop again with the same expression.

Concolic by using hypothesis.
Decorator "partial evals"

What does Rosette really offer over python + z3? I've never been clear on that <https://docs.racket-lang.org/rosette-guide/index.html>
It does over the racket make a dsl thing if you're into that.

Could switch out for Not based form.

Tagging the code string with other metadata is probable quite useful.
You want it to fail early if the types make no sense.
But then you can't use fstrings. :(

```python
from dataclasses import dataclass
from typing import TypeVar
T = TypeVar('T')
@dataclass
class Code[T]:
    typ : T
    code : str

    def __add__(self):

```

```python
def mypow(x:int,n:int) -> int:
    assert n >= 0
    if n == 0:
        return 1
    else:
        x * mypow(x,n-1)

# accumulator version?

# string version
# strings are a universal but somewhat structure free rep of code.
Code = str
def mypow2(n:int, x:Code) -> Code:
    if x == 0:
        return "1"
    else:
        f"{x} * {mypow2(x,n-1)}"

mypow = lambda x,n: 1 if n <= 0 else x * mypow(x,n-1)

mypow = Function("mypow", IntSort(), IntSort(), IntSort())
mypow_def = ForAll([x,n], mypow(n, x) == If(n <= 0, 1, x * mypow(n-1, x)))

# Partially evaled
def mypow(x:ExprRef, n:int) -> ExprRef:
    if n == 0:
        return IntVal(1)
    else:
        return x * mypow(x,n-1)


```

```python
class Bool():
    def __bool__(self):
        print("asked")
        return True
    

b = Bool()
if b:
    print("yes")
else:
    print("no")

import z3

ctx = None
path = []
s = Solver()
def record_bool():
    s.check()
    path.append()

z3.BoolRef.__bool__ = lambda self, 
def reify(f, vs):
    global ctx
    ctx = [m]
    while True:
        retval = f(vs)
        
    ctx = None

@reify
def example(x):
    if x == 7:
        return 3
    else:
        if x > 14:
            return 4
        else:
            return 5
```

```python
from z3 import *
import kdrag.smt as smt
traces = []
trace  = []
def reset():
    global trace

    trace = []
def record(self):
    s = Solver()
    for tr,res in traces:
        s.add(smt.Not(smt.And(tr))) # we can't repeat the same trace.
    s.add(smt.And(trace)) # currently this is true
    s.add(self) # bias towards taking the branch
    res = s.check()
    if res == sat:
        trace.append(self == True)
        return True
    else:
        trace.append(self == False)
        return False
BoolRef.__bool__ = record
x = Int("x")

def foo(x):
    if x > 3:
        if x == 4:
            return x
        else:
            return x-1
    else:
        return x*3

while True:
    trace = []
    res = foo(x)
    if len(traces) > 0 and all( c1.eq(c2) for c1,c2 in zip(traces[-1][0],trace)):
        break 
    traces.append((trace,res))
traces

# maybe a brute force is better?
# could rejoin cases
# could be way more efficient with sat solver queries.
# loop detection?
```

Hmm. Actually, doing it in order might be important for proper if then else resolution? No. I don't think so.

```python

```

    [v0] []
    [v0] [([(v0 > 3) == True, (v0 == 4) == True], v0)]
    [v0] [([(v0 > 3) == True, (v0 == 4) == True], v0), ([(v0 > 3) == False], v0*3)]





    [([(v0 > 3) == True, (v0 == 4) == True], v0),
     ([(v0 > 3) == False], v0*3),
     ([(v0 > 3) == True, (v0 == 4) == False], v0 - 2)]

```python
@symexec(IntSort())
def comp(x):
    return x + 3 < x < x - 4 or x > 3
comp
```

    [v0] []





    [([(v0 + 3 < v0) == False, (v0 + 3 < v0) == False], v0 > 3)]

Some ideas about compressing making prettier the output.

We may wnat ot compile into if then else trees, then maybe how we'd arrange things is a big different.

```python
def lookup_trie(trie, key):
    node = trie
    for k in key:
        node = node.get(k)
        if node is None:
            return None
    return node

def store_trie(trie, key, value):
    node = trie
    for k in key:

        if k not in node:
            node[k] = {}
        node = node[k]
    node["result"] = value

def trace_trie(traces):
    trie = {}
    for trace,res in traces:
        print(trie)
        store_trie(trie, trace, res)
    return trie

def compress_trie(traces):
    # If only one path, compress away that node
    # If all paths have same result, compress away.
    # probably best to do bottom up
    pass

t = {}
store_trie(t, "abc" ,3 )

trace_trie(foo)
t
```

    {}
    {(v0 > 3) == True: {(v0 == 4) == True: {'result': v0}}}
    {(v0 > 3) == True: {(v0 == 4) == True: {'result': v0}}, (v0 > 3) == False: {'result': v0*3}}



    ---------------------------------------------------------------------------

    TypeError                                 Traceback (most recent call last)

    Cell In[29], line 34
         31 t = {}
         32 store_trie(t, "abc" ,3 )
    ---> 34 trace_trie(foo)
         35 t


    Cell In[29], line 22, in trace_trie(traces)
         20 for trace,res in traces:
         21     print(trie)
    ---> 22     store_trie(trie, trace, res)
         23 return trie


    Cell In[29], line 13, in store_trie(trie, key, value)
         10 node = trie
         11 for k in key:
    ---> 13     if k not in node:
         14         node[k] = {}
         15     node = node[k]


    TypeError: 'NoneType' object is not callable
