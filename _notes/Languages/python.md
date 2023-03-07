---
layout: post
title: Python
---

# Venv
Venv makes an isolated python environment

```
python3 -m venv .venv
source ./venv/bin/activate 
```

# Django

https://www.djangoproject.com/

Models create database entries for you. There is mapping of fields to databae
Many-to-one relatioships. You can talk back

Views
Templates
Generic views



Admin page

Django rest framework
Django channels




# Generators

# Collections

# Protocols

# Abstract Base classes
Metaclasses


# Modules

sqlite


### python internals
https://devguide.python.org/
https://github.com/python/cpython
https://devguide.python.org/exploring/

Python/python.c
MOdules/main.c


python -h. when was the last time I looked at that?

[understanding python bytecode](https://towardsdatascience.com/understanding-python-bytecode-e7edaae8734d)
[the `dis` module](https://docs.python.org/3/library/dis.html) 
[Hacking the CPython Interpreter](https://www.youtube.com/watch?v=1SqRRrmQHx0)


# Venv
venv virtualenv conda pyenv

# Async

# Type Hints
mypy

# stdlib

pickle
copy
functools
itertools

re expressions
sqlite
# C interop

Cython

# Pypy

Huh. There's good stuff here. Yeah, it's a faster python intepreter. But it's a library too?
# Hashcons

```python
class HashCons():
    def __init__(self):
        self.dict = {}
        #self.unique = -1
        self.data = []
    def term(self, *args):
        v = self.dict.get(args)
        if v == None:
            #self.unique += 1 
            v = len(self.data)
            self.data.append(args)
            self.dict[args] = v
            return v
        else:
            return v

h = HashCons()
print(h.term(1,2))
print(h.term(1,2))
print(h.term(3,2))
print(h.data[0])
print( (1,2) is (1,2) )
x = (1,(2,3))

print(x is x)
z = (1,2,3,4)
y = (1,(2,3))
print(x is y)
# Ok. Bu we can't fast hash if I use physical equality
# 
h = HashCons()


def foo(x,y):
    return h.term("foo",x,y)
def bar(x):
    return h.term("bar",x)
a = h.term("a")
b = h.term("b")

print(bar(foo(a,b)))
print(h.data)
```

```python

class Rewrite():
    def __init__(self):
        self.simp = {}
        self.eqs = [] #???
    def root(self,a):
        #if isinstance(a, tuple):
        #    a = tuple(self.root(x) in a)
        #return self.simp.get(a, a)
        #while self.simp.get(a1, a1) != a1:
        #    a1 = self.simp.get(a1,a1)
    def add_eq(self,a,b):
        # This is union with a priori order
        a = self.root(a)
        b = self.root(b)
        if a <= b:
            self.simp[a] = b
        else:
            self.simp[b] = a
    def norm(self):
        # eager compression
        for a,b in self.simp:
            # congruence
            if isinstance(b, tuple): 
                b = tuple(self.root(x) for x in b)
            self.simp[a] = self.root(b)

            
        
# if terminating and confluent then maxmial simplified is a functional mapping.
# Hmm. confluence... that is not at all obvious.
# ground equations are orientable.


```

# Holpy

```python
import sys
sys.path.insert(0, "/home/philip/Documents/python/holpy")
 
from kernel.type import TFun, BoolType, NatType, IntType, RealType, TVar, STVar
from kernel import term
from kernel.term import Var, Const, Comb, Term, true, false, And, Or, Implies, Not, \
    Eq, Nat, Real, NatVars, BoolVars, SVar, Lambda, Forall
from syntax.settings import settings
#from data import nat
#from data import real
#from logic import basic
from logic import matcher


##basic.load_theory('real')
# Not so different from z3 api

x = SVar("x", BoolType)
x = Const("x", BoolType)
x = Var("x",BoolType)
t = STVar("t")
print(t) # schematic type variable
# I'm a little confused what the difference is between const, var, and svar. var is bound variable in context and svar is a metavairable?
print(And(x,x))
print(x == x)
print(Eq(x,x))
settings.unicode = True
print(Lambda(x,x))
print(Lambda(x,Or(x,x)).checked_get_type())
f = Lambda(x,Or(x,x))
print(f(true))
print(f(true).beta_norm()) # beta_conv does just outer layer

print(repr(f)) # de bruijn indices are visible. Abs and Bound constructor
print(repr(Forall(x,x))) # all(Lambda(x,x))
#print(term.all(f)) # Hmm. I don't know where it is though

from kernel.thm import Thm
A = Var("A", BoolType)
B = Var("B", BoolType)
C = Var("C", BoolType)
th = Thm(C, A, B) # A,B |- C. Concsequent comes first
print(th)
th.check_thm_type()
print(th.hyps)
print(th.concl)
```

# Lark
python parser generator. Pretty nice. 
```python
import lark
#https://github.com/bzhan/holpy/blob/main/geometry/parser.py
from lark import Lark, Transformer, v_args, exceptions  # type: ignore

grammar = r"""
    
    PRE: ("¬"|CNAME) (CNAME)*
    
    ?fact: PRE "(" CNAME ("," CNAME)* ")"
    ?rule: fact ":-" fact ("," fact)*
    
    %import common.DIGIT
    %import common.WS
    %import common.LETTER
    %import common.CNAME
    %ignore WS
"""
#fact_parser = Lark(grammar, start="fact", parser="lalr", transformer=GeometryTransformer())
rule_parser = Lark(grammar, start="rule", parser="lalr")
print(rule_parser.parse("a(x) :- b(y)"))
```

# libraries


numpy
scipy
pandas
matplotlib
tensroflow
pytorch
scikitlearn
networkx 
opencv
pygame
beautiful soup

pwntools
[poetry](https://python-poetry.org/) dependency management
Dask
nltk
cvxpy

flake8

pytest
hypothesis

[FASTAPI](https://fastapi.tiangolo.com/) combining
starlette - asynchronosusw api
pydantic - type hinting into enfrocmeent

```python
from fastapi import FastAPI

app = FastAPI()


@app.get("/")
async def root():
    return {"message": "Hello World"}


```

[Memray is a memory profiler for Python](https://github.com/bloomberg/memray)

[cupy](https://github.com/cupy/cupy)

pyiodide

[taichi](https://github.com/taichi-dev/taichi) high performance programming in python

[python decompiler](https://github.com/rocky/python-decompile3) why would you even want this?

[Gooey](https://github.com/chriskiehl/Gooey) autoconvert cli to gui app

[aesara](https://github.com/aesara-devs/aesara) Aesara is a Python library for defining, optimizing, and efficiently evaluating mathematical expressions involving multi-dimensional arrays.

[hpy](https://hpyproject.org/) HPy provides a new API for extending Python in C. In other words, you use `#include <hpy.h>` instead of `#include <Python.h>`.

[pypy talks](https://www.youtube.com/@cfbolz)

[pydrofoil](https://github.com/pydrofoil/pydrofoil)

https://github.com/JonnyWalker/PySNES

https://github.com/bivab/eqsat

https://github.com/bivab/pytri petri net model checker

https://github.com/AntonLydike/riscemu risc v emulator

[](https://github.com/hsinhaoyu/cont_frac) bill gosper's continued fractions