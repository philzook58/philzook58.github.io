---
layout: post
title: Python
---
- [Venv](#venv)
- [Django](#django)
- [CFFI](#cffi)
- [Jupyter](#jupyter)
- [Generators](#generators)
- [Collections](#collections)
- [Protocols](#protocols)
- [Abstract Base classes](#abstract-base-classes)
- [Modules](#modules)
- [python internals](#python-internals)
- [Venv](#venv-1)
- [Async](#async)
- [Type Hints](#type-hints)
- [stdlib](#stdlib)
- [C interop](#c-interop)
- [Pypy](#pypy)
- [Hashcons](#hashcons)
- [Holpy](#holpy)
- [Lark](#lark)
- [libraries](#libraries)
- [Misc](#misc)

# Venv

Venv makes an isolated python environment

```
python3 -m venv .venv
source ./venv/bin/activate 
```

# Django

whitenoise
<https://whitenoise.readthedocs.io/en/stable/#>
guvicorn
gunicorn

<https://www.djangoproject.com/>

Models create database entries for you. There is mapping of fields to databae
Many-to-one relatioships. You can talk back

Views
Templates
Generic views

Admin page

Django rest framework <https://www.django-rest-framework.org/>
Django channels

```python
import django

```

```bash

cd /tmp
django-admin startproject mysite
cd mysite
ls # manage.py mysite
#python3 manage.py runserver # 0.0.0.0:8000 optionally pick a port
#cd mysite
#ls # asgi.py  __init__.py  __pycache__  settings.py  urls.py  wsgi.py
python3 manage.py startapp polls
python3 manage.py
python3 manage.py migrate
python3 manage.py createsuperuser --username admin --email admin@example.com
```

manage.py

# CFFI

Ctypes is standard clib cffi is higher level one

```python
from cffi import FFI
ffi = FFI()
ffi.cdef("""
     int printf(const char *format, ...);   // copy-pasted from the man page
 """)
C = ffi.dlopen(None)                     # loads the entire C namespace
arg = ffi.new("char[]", b"world")        # equivalent to C code: char arg[] = "world";
C.printf(b"hi there, %s.\n", arg)        # call printf

```

```bash
echo "
int foo(int x){
    return x + 4;
}
" > /tmp/foo.c
gcc -shared -fPIC /tmp/foo.c -o /tmp/foo.so
```

```python
import cffi

ffi = cffi.FFI()
ffi.cdef("int foo(int x);")
foolib = ffi.dlopen("/tmp/foo.so")
print(foolib.foo(3)) # 7

```

```python
# https://youtu.be/2BB39q6cqPQ?t=345
import ctypes
import mmap

addr = mmap.mmap(-1, 4096, mmap.PROT_READ | mmap.PROT_READ | mmap.PROT_EXEC,
                 mmap.MAP_PRIVATE | mmap.MAP_ANONYMOUS, -1, 0)

import pwntools
code = asm()
ctypes.memmove(addr, code, len(code))
myfun = ctypes.cast(addr, ctypes.CFUNCTYPE(ctypes.c_long))
print(myfun())

```

# Jupyter

`%%bash`

# Generators

# Collections

# Protocols

# Abstract Base classes

Metaclasses

# Modules

sqlite

# python internals

[python runtime services](https://docs.python.org/3/library/python.html)
The `sys` module

```python
import sys
print(sys.displayhook("foo"))
print(sys.modules)
print(sys.getsizeof(3))
print(sys.getsizeof("fooo"))

```

<https://devguide.python.org/>
<https://github.com/python/cpython>
<https://devguide.python.org/exploring/>

Python/python.c
MOdules/main.c

python -h. when was the last time I looked at that?

[understanding python bytecode](https://towardsdatascience.com/understanding-python-bytecode-e7edaae8734d)
[the `dis` module](https://docs.python.org/3/library/dis.html)
[Hacking the CPython Interpreter](https://www.youtube.com/watch?v=1SqRRrmQHx0)

`id` is apparently a pointer

<https://mcla.ug/blog/cpython-hackage.html>
<https://gist.github.com/mahmoudimus/295200> monkey patch built in types
`ctypes.memmove`

```python
l = [1,2,3]
print(id(l))
import sys
import ctypes

# Example object
obj = 0x123456789
#obj = 0x1234
# Getting the memory address and size of the object
memory_address = id(obj)
size_in_bytes = sys.getsizeof(obj)

memory_address, size_in_bytes
# Create a byte array at the memory address
num_bytes = size_in_bytes
byte_values = (ctypes.c_char * num_bytes).from_address(memory_address)

# Extracting the raw bytes
raw_memory_content = bytearray(byte_values)

print(raw_memory_content)

"""
struct _longobject {
    PyObject_VAR_HEAD
    digit ob_digit[1];
};

typedef struct {
    PyObject ob_base;
    Py_ssize_t ob_size; /* Number of items in variable part */
} PyVarObject;

typedef struct _object {
    _PyObject_HEAD_EXTRA
    Py_ssize_t ob_refcnt;
    PyTypeObject *ob_type;
} PyObject;
"""

ctypes.c_ssize_t
ctypes.c_void_p
ctypes.POINTER(ctypes.c_uint)

class PyObj(ctypes.Structure):
    _fields_ = [
        ("ob_refcnt", ctypes.c_ssize_t),
        ("ob_type", ctypes.c_void_p),
    ]
class PyVarObj(ctypes.Structure):
    _fields_ = [
        ("ob_base", PyObj),
        ("ob_size", ctypes.c_ssize_t),
    ]
class PyLong(ctypes.Structure):
    _fields_ = [
        ("head", PyVarObj),
        ("ob_digit",  ctypes.c_uint * 10) #ctypes.POINTER(ctypes.c_uint)),
    ]
o = PyLong.from_address(id(obj))
#print(o.ob_digit[0])
varobj = o.head
print(varobj.ob_base.ob_refcnt)
varobj.ob_base.ob_refcnt += 10
print(sys.getrefcount(obj)) # cooool
print(varobj.ob_base.ob_refcnt)
print(varobj.ob_base.ob_type)

print(varobj.ob_size)
print(size_in_bytes)

print(o.ob_digit[0])
print(obj)

print(o.ob_digit[0] + o.ob_digit[1] * 2**30)
```

```python
import os
import sysconfig

def find_python_h():
    include_path = sysconfig.get_path('include')
    python_h_path = os.path.join(include_path, 'Python.h')
    return python_h_path

print("Python.h should be located at:", find_python_h())

from cffi import FFI
ffi = FFI()

ffi.cdef("#include <elf.h>")
arg = ffi.new("char[]", b"world") 
print(dir(arg))
```

```python
from cffi import FFI
ffibuilder = FFI()

# cdef() expects a single string declaring the C types, functions and
# globals needed to use the shared object. It must be in valid C syntax.
ffibuilder.cdef("""
    float pi_approx(int n);
""")

# set_source() gives the name of the python extension module to
# produce, and some C source code as a string.  This C code needs
# to make the declarated functions, types and globals available,
# so it is often just the "#include".
ffibuilder.set_source("_pi_cffi",
"""
     #include "pi.h"   // the C header of the library
""",
     libraries=['piapprox'])   # library name, for the linker

if __name__ == "__main__":
    ffibuilder.compile(verbose=True)
```

```python
print(dir(int))
```

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

<https://www.youtube.com/watch?v=DKns_rH8rrg&t=974s&ab_channel=EuroPythonConference> jit compiler in 30 minutes.
mmap huh.

<https://github.com/Maratyszcza/PeachPy>

[hpy](https://hpyproject.org/) HPy provides a new API for extending Python in C. In other words, you use `#include <hpy.h>` instead of `#include <Python.h>`.

[pypy talks](https://www.youtube.com/@cfbolz)

[pydrofoil](https://github.com/pydrofoil/pydrofoil)

<https://github.com/JonnyWalker/PySNES>

<https://github.com/bivab/eqsat>

<https://github.com/bivab/pytri> petri net model checker

<https://github.com/AntonLydike/riscemu> risc v emulator

[](https://github.com/hsinhaoyu/cont_frac) bill gosper's continued fractions

# Misc

<https://bernsteinbear.com//blog/typed-c-extensions/> Type information for faster Python C extensions <https://news.ycombinator.com/item?id=38988982>
