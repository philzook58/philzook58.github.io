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

# Holpy



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