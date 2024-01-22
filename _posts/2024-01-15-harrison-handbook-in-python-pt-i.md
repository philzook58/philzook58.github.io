---
date : 2024-01-15
layout: post
title : "Harrison Handbook in Python pt 1"
---

New Years rolled around this year and I was wondering what would be a good resolution. Obviously, eating better, working out more yada yada. But I also wish I would blog more. My bar for a post has been slowly raising, which is bad. Write early, write often. Also my notes section (which I love) has started to absorb things that used to be posts. Notes has a never ending, no bow tieing aspect to it which is double edged. So I'm going to try and take Monday mornings to write something, anything, no matter how small.

As a straightforward task to get the ball rolling, let's implement some stuff out of John Harrison's book in python.

The Handbook of Practical Logic and Automated Reasoning is quite a book. You can find the ocaml code extracted here <https://www.cl.cam.ac.uk/~jrh13/atp/>. I really am just going straight down the files and translating them very directly. It's pretty mindless. I do think there is value in converting such things though. I remember distinctly a time I was quite comfortable in Haskell, but has never used OCaml. Of course I could kind of read code like this, but it takes comprehension down to 70% let's say. If you only know python, it becomes even harder. But the true contents is not language specific.

I'm doing this in a jupyter notebook in vs code and outputting to markdown via `jupyter nbconvert --to markdown myfile.ipynb`.

# Syntax Trees and Parsing

I have experimented with different styles of building tree data types in python. One method is the dataclass method. You make a class for the tree type and then a dataclass per constructor which subclasses this. It has some nice features.

I've been leaning towards a more lightweight style recently though, an "s-expression" style where you just use tuples where the first element is a string representing the constructor. The dataclass style has a lot of boiler plate.

It might also be nice to use an enum rather than string tags, but I'd have to look up the library every time probably. Again this is more boiler plate that it isn't 100% clear gains me anything in the python context. In a more rigid language at least I'd get compile time checking. This is not necessarily the style I'd endorse for a large or collaborative project. Automatic sanity checking is more useful in that context.

```python
# some helpers for nicer notation
# could do it this way, but it is a little verbose
add = lambda x,y : ("add",x, y)


def Function(name):
    # makes a function that returns a tuple with the name as the first element
    return lambda *args: (name, *args)
def Functions(names):
    return map(Function, names.split())
var = Function("var")
const = Function("const")
add = Function("add")
mul = Function("mul")

```

Here's a basic recursive simplifier or arithmetic expressions. It is clever to separate out into a base case function and the recursive function. I could probably make `simplify` more generic by just checking the number of args. The new addition of `match` statements in python makes it quite pleasant to read this code and easier to translate from the ocaml.
Allowing "or" patterns `|` let's me compact a couple cases, which is nice.

```python
def simplify1(x):
    match x:
        case ("add", ("const", m), ("const", n)):
            return ("const", m + n)
        case ("mul", ("const", m), ("const", n)):
            return ("const", m * n)
        case ("add", ("const", 0), y) | ("add", y, ("const", 0)):
            return y
        case ("mul", ("const", 0), y) | ("mul", y, ("const", 0)) :
            return ("const", 0)
        case ("mul", ("const", 1), y) | ("mul", y, ("const", 1)):
            return y
        case _:
            return x
def simplify(expr):
    match expr:
        case ("add", x, y):
            return simplify1(("add", simplify(x), simplify(y)))
        case ("mul", x, y):
            return simplify1(("mul", simplify(x), simplify(y)))
        case _:
            return simplify1(expr)
simplify(add(const(3), const(4)))
```

    ('const', 7)

For parsing, I'm quite enamored with the lark library. It makes it very easy to define grammars. I'm thinking about using it to make the analog of an extensible notation mechanism in knuckledragger. This example is ripped right from the lark docs.

```python
from lark import Lark, Transformer, v_args
# https://lark-parser.readthedocs.io/en/latest/examples/calc.html#sphx-glr-examples-calc-py
calc_grammar = """
    ?start: add

    ?add: mul
        | add "+" mul   -> add

    ?mul: atom
        | mul "*" atom  -> mul

    ?atom: NUMBER           -> const
         | NAME             -> var
         | "(" add ")"

    %import common.CNAME -> NAME
    %import common.NUMBER
    %import common.WS_INLINE

    %ignore WS_INLINE
"""

def lift1(f):
    return lambda x,*args: f(*args)
@v_args(inline=True)    # Affects the signatures of the methods
class CalculateTree(Transformer):
    # This is a little weird and clunky and boilerplaty. Oh well.
    var =  lambda self, x: var(str(x))
    const = lambda self, x: const(int(x))
    add = lift1(add)
    mul = lift1(mul)

calc_parser = Lark(calc_grammar, parser='lalr', transformer=CalculateTree())
calc = calc_parser.parse

simplify(calc("1 + 1 + 1 + 0 * x * 3 + 4"))

```

    ('const', 7)

# Formulas

Z3, pysmt, sympy, and pyres already have python formula types. Why not another?
Anyway, let's just copy out the book's examples.

Hmm. I don't have the precedence ironed out very well.

The constants `True` and `False` are annoying. It's tempting to remove the layer of tuple around them, but that makes the system less uniform. Also tempting it to identify them with python `True` and `False`. I'm not sure what is for the best. It makes for unnecessarily awkward pattern matching later too.

```python
False_, True_, Atom, Not, And, Or, Imp, Iff, Forall, Exists = Functions("False True Atom Not And Or Imp Iff Forall Exists")

from lark import Lark, Transformer, v_args
# https://lark-parser.readthedocs.io/en/latest/examples/calc.html#sphx-glr-examples-calc-py
prop_grammar = """
    ?start: iff

    ?iff: imp
        | iff "<=>" iff -> iff

    ?imp: disj
        | disj "==>" imp -> imp

    ?disj: conj
        | disj "|" conj   -> or_

    ?conj: atom
        | conj "&" atom  -> and_

    ?atom: "false"           -> false_
         | "true"            -> true_
         | "~" atom         ->  not_
         | NAME              -> atom
         | "(" iff ")"

    %import common.CNAME -> NAME
    %import common.NUMBER
    %import common.WS_INLINE

    %ignore WS_INLINE
"""

def lift1(f):
    return lambda x,*args: f(*args)
@v_args(inline=True)    # Affects the signatures of the methods
class PropTree(Transformer):
    false_, true_, atom, not_, and_, or_, imp, iff, Forall, Exists = map(lift1, [False_, True_, Atom, Not, And, Or, Imp, Iff, Forall, Exists])
    atom = lambda self, x: Atom(str(x))

prop_parser = Lark(prop_grammar, parser='lalr', transformer=PropTree())
prop = prop_parser.parse

prop("a ==> b ==> c")
prop("a <=> a | b & c")
prop("a & c | b ==> d")

```

    ('Imp',
     ('Or', ('And', ('Atom', 'a'), ('Atom', 'c')), ('Atom', 'b')),
     ('Atom', 'd'))

```python
False_()
```

    ('False',)

We can evaluate in a model. BTW, github copilot rules for filling out these cases.

```python
def eval_prop(fm, v):
    match fm:
        case ("False",):
            return False
        case ("True",):
            return True
        case ("Atom", x):
            return v[x]
        case ("Not", x):
            return ~ eval_prop(x, v)
        case ("And", x, y):
            return eval_prop(x, v) & eval_prop(y, v)
        case ("Or", x, y):
            return eval_prop(x, v) | eval_prop(y, v)
        case ("Imp", x, y):
            return ~eval_prop(x, v) | eval_prop(y, v)
        case ("Iff", x, y):
            return eval_prop(x, v) == eval_prop(y, v)
        case _:
            assert False, f"unknown formula {fm}"
import z3 
# Some hackery to eval directly into z3. probably ill advised.
class BoolDummy:
    def __getitem__(self,x):
        return z3.Bool(x)
z3.BoolRef.__and__ = lambda x,y: z3.And(x,y)
z3.BoolRef.__or__ = lambda x,y: z3.Or(x,y)
z3.BoolRef.__invert__ = lambda x: z3.Not(x)
def eval_z3(fm):
    return eval_prop(fm,BoolDummy())

eval_prop(prop("true & false"), [])
eval_z3(prop("~a | b ==> c ==> d"))
```

&not;(&not;a &or; b) &or; &not;c &or; d

```python
def dual(fm):
    match fm:
        case ("False_"):
            return True_
        case ("True_"):
            return False_
        case ("Atom", x):
            return fm
        case ("Not", x):
            return dual(x)
        case ("And", x, y):
            return Or(dual(x), dual(y))
        case ("Or", x, y):
            return And(dual(x), dual(y))
        case ("Imp", x, y):
            return And(x, dual(y))
        case ("Iff", x, y):
            return Iff(x, dual(y))
dual(prop("a ==> b ==> c"))
```

    ('And', ('Atom', 'a'), ('And', ('Atom', 'b'), ('Atom', 'c')))

```python
def psimplify1(fm):
    match fm:
        case ("Not", ("False",)):
            return True_()
        case ("Not", ("True",)):
            return False_()
        case ("Not", ("Not", x)):
            return p
        case ("And", ("False",), y) | ("And", y, ("False",)):
            return False_()
        case ("And", ("True",), y) | ("And", y, ("True",)):
            return y
        case ("Or", ("False",), y) | ("Or", y, ("False",)):
            return y
        case ("Or", ("True",), y) | ("Or", y, ("True",)):
            return True_()
        case ("Imp", ("False",), y) | ("Imp", y, ("True",)):
            return True_()
        case ("Imp", ("True",), y):
            return y
        case ("Imp", x, ("False",)):
            return Not(x)
        case ("Iff", ("True",), y) | ("Iff", y, ("True",)):
            return y
        case ("Iff", ("False",), y) | ("Iff", y, ("False",)):
            return Not(y)
        case _:
            return fm

def psimplify(fm):
    match fm:
        case ("Not", p):
            return psimplify1(Not(psimplify(p)))
        case ("And", x, y):
            return psimplify1(And(psimplify(x), psimplify(y)))
        case ("Or", x, y):
            return psimplify1(Or(psimplify(x), psimplify(y)))
        case ("Imp", x, y):
            return psimplify1(Imp(psimplify(x), psimplify(y)))
        case ("Iff", x, y):
            return psimplify1(Iff(psimplify(x), psimplify(y)))
        case _:
            return fm

psimplify(prop("b & false ==> c ==> d"))

        
```

    ('True',)

Negation normal form. Push down all the nots and convert Imp and Iff into And/Or forms
This is a useful transformation.

```python
def nnf(fm):
    match fm:
        case ("And", p, q):
            return And(nnf(p), nnf(q))
        case ("Or", p, q):
            return Or(nnf(p), nnf(q))
        case ("Imp", p, q):
            return Or(nnf(Not(p)), nnf(q))
        case ("Iff", p, q):
            return Or(And(nnf(p), nnf(q)), And(nnf(Not(p)), nnf(Not(q))))
        case ("Not", ("Not", p)):
            return nnf(p)
        case ("Not", ("And", p, q)):
            return Or(nnf(Not(p)), nnf(Not(q)))
        case ("Not", ("Or", p, q)):
            return And(nnf(Not(p)), nnf(Not(q)))
        case ("Not", ("Imp", p, q)):
            return And(nnf(p), nnf(Not(q)))
        case ("Not", ("Iff", p, q)):
            return Or(And(nnf(p), nnf(Not(q))), And(nnf(Not(p)), nnf(q)))
        case _:
            return fm
    
nnf(prop("a ==> b ==> c"))
```

    ('Or', ('Not', ('Atom', 'a')), ('Or', ('Not', ('Atom', 'b')), ('Atom', 'c')))

# Conclusion

And so on. I'm bored for today and let's stop here.

We didn't get to anything really juicy today. It is nice to see how easy it can be to implement a tree type and basic simplifier in python, especially with pattern matching syntax.
I was tinkering with converting to rust and it was much more laborious feeling. <https://github.com/philzook58/res-rs/tree/main/src/harrison>

See ya next week hopefully! Or maybe I'll tinker on something a bit different.
Some ideas:

- inductive types in knuckledragger
- metamath provenance for datalog
- more cbmc tricks
- linker hacking
- td4 cpu
