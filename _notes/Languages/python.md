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
