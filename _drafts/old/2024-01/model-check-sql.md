
Model checking is the problem of given a logical formula and some kind of object/database/transition system, does the system obey the logical formula?

This is most often referred to in the transition system context with respect to some kind of temporal lgic formula descirbing good behavior for the system, but it is a generic idea across many other logics.

In the basic logics of boolean and first order logic, the problem maybe just seems too trivial to say much about? For boolean logic, you are given an assignment to booleans and just need to evaluate the formula and see if it comes out true.
(maybe there is something more interesting to say for intuitionistic propositional logic?)

While datalog systems can discuss some kind of fixed point, bog standard sql is a system that can model check first order formula.

SQL engines are super engineered, and I find it interesting to consider their capabilities in the same light as solvers like Z3, minizinc, or SAT solvers.

```python
def pythonize(fm,model):
    match fm:
        case ("And", x, y):
            return pythonize(x,model) and pythonize(y,model)
        case ("Or", x, y):
            return pythonize(x,model) or pythonize(y,model)
        case ("Not", x):
            return not pythonize(x,model)
        case ("Implies", x, y):
            return not pythonize(x,model) or pythonize(y,model)
        case ("Forall", x, y):
            return all(pythonize(y,extend(model,x,v)) for v in x.domain)
        case ("Exists", x, y):
            return any(pythonize(y,extend(model,x,v)) for v in x.domain)
        case ("Atom", (R, *args)):
            return model[R](*args)
```

```python

def sqlize(fm):
    match fm:
        case ("And", x, y):
            return f"({sqlize(x)} AND {sqlize(y)})"
        case ("Or", x, y):
            return f"({sqlize(x)} OR {sqlize(y)})"
        case ("Not", x):
            return f"(NOT {sqlize(x)})"
        case ("Implies", x, y):
            return f"(NOT {sqlize(x)} OR {sqlize(y)})"
        case ("Forall", x, y):
            return f"(NOT EXISTS {x} {sqlize(y)})"
        case ("Exists", x, y):
            return f"(EXISTS {x} {sqlize(y)})"
        case ("Atom", (R, *args))

```
