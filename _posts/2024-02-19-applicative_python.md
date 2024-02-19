---
date: 2024-02-19
title: Applicative Python a la ACL2
---

I've been reading about [ACL2](https://www.cs.utexas.edu/users/moore/acl2/), a theorem prover designed for common lisp. It has good automation and has been quite successfully applied to significant [software/hardware verification](https://royalsocietypublishing.org/doi/10.1098/rsta.2015.0399) and mathematics.

Python and lisp are actually similar in a lot of ways (dynamic typed, GC). Something not sufficiently explored is how to apply the ACL2 design pattern in more popular languages like python. This blog post is some first steps.

ACL2's logic is based on an applicative subset of common lisp (pure functions). This design has a number of good points

- The constructs of the logic are familiar programming constructs.
- Your specs are executable. "Logical" specs often take the form of an interpreter, model, or emulator of the system in question. Then you ask about properties of this interpreter.

One step towards porting such a thing is describing an applicative subset of python. This is a subset of python that is pure and has a simple(er) mathematical semantics.

There is a design balance to be struck here. The subset should be small enough to be easily understood and reasoned about, but large enough to be useful and not feel constraining.

I think I tend to use pretty close to pure python programming naturally, so this isn't so bad.

## What about the types?

Most theorem prover languages are strongly typed. This is not ACL2's design nor would it make sense for the untyped language of python.

There is a standard method for relating the two worlds. You can model an untyped language by making an algebraic datatype of all the possible values. This is an inefficient thing to do from the perspective of typed languages, but it works. Sometimes "untyped" languages are referred to as ["unityped"](https://news.ycombinator.com/item?id=8206562) for this reason

In Ocaml, this type would be something like

```ocaml
type univ = 
 | Cons of univ * univ
 | Nil
 | Bool of bool
 | Float of float
 | Int of int
```

In z3, you can build something similar. We could perhaps start to chase down more extensions, like immutable dictionaries or certain kinds of higher order functions (there be dragons here), but this is a good start.

```python
from z3 import *
U = Datatype('Univ') # Basic PyObject
U.declare('cons', ('car', U), ('cdr', U))
U.declare('bool', ('bool_val', BoolSort()))

# Interesting but questionable
#U.declare('real', ('real_val', RealSort()))
#U.declare('float', ('float_val', FloatSort())
U.declare('string', ('string_val', StringSort()))
U.declare('int', ('int_val', IntSort()))
U.declare('nil') # None

U = U.create()

U.cons(U.string(StringVal('fred')), 
U.cons(U.int(42), 
U.cons(U.cons(U.bool(True), 
       U.cons(U.bool(False), 
       U.nil)),
U.nil)))
```

```
cons(string("fred"),
     cons(int(42),
          cons(cons(bool(True), cons(bool(False), nil)),
               nil)))
```

Note, that while python tuple are flat, it is easiest to model them as linked lists. Hence the python tuple `("fred", 42, (True, False))` would be `Cons("fred", Cons(42, Cons(Cons(True, Cons(False, Nil)), Nil)))`

# What about statements?

One can take a look at the python ast to get some clarity on what is available as expressions and statements. <https://greentreesnakes.readthedocs.io/en/latest/nodes.html>

Python expressions are mostly ok from a purely functional perspective.

However, python is not a expression oriented language. It is mostly oriented around statement and imperative programming. To restrict ourselves to only expressions is close to impossible and very awkward.

However, I think there is a reasonable subset of imperative python that is effectively pure (applicative). We can consider statements of the following form as syntax sugar for a purely applicative equivalent.

- Sequences of assignments are allowed and are interpreted as `let` expressions scoped to the end of the block.
- Every sequence of statements is terminated by a `return` or an `if then else` statement. Recursively, the bodies of the `if else` do eventually terminate in a `return`.`
- `if` `else` statements are allowed and are interpreted as `if` expressions.
- Many expressions are allowed. tuples, strings, integers are immutable and allowed.

What is disallowed:

- `indexed` assignment like `foo.a = 3` or `bar[7] = 8`
- mutable data structures like lists, dicts, sets, etc. We could perhaps skirt by this by just disallowing the mutating functions. The loss of dictionaries is close to unacceptable.
- Nonterminating functions. More on this another day.

Overloading in python is a nice language feature that can make for some clean and fun library design. This is nice for example when you are writing logical expressions for a theorem prover like z3. It is somewhat unfortunate that you can't overload some particular constructs like `if else`, `and`, `or`, `not` expressions, comprehensions or `for`, `while`, `assert` statements. On choice is you can switch over to a bit clunkier syntax of using functions like `If(cond,the,else)`

I did show a style of doing this for a weakest precondition analysis here. <https://www.philipzucker.com/weakest-precondition-z3py/>

But a powerful, intriguing, but probably in poor taste thing to do is to get your hands on the python syntax tree. You can do this, python has very high amounts of metaprogrammability.

Here I wrote some functions and a decorator to recognize the aforementioned applicative python and convert it to a z3 expression.

An awkward piece is that everything needs to be wrapped in order to use the `Univ` unitype. I would need to write down axioms to define these.

```python
from ast import *
import ast
import z3
import functools
def applpy_const(x):
    # helper to convert from python value to Univ value
    if isinstance(x, int):
        return U.int(z3.IntVal(x))
    elif isinstance(x, str):
        return U.string(z3.StringVal(x))
    elif isinstance(x, bool):
        return U.bool(z3.BoolVal(x))
    elif isinstance(x,tuple):
        assert False # todo
    else:
        raise ValueError("Unknown constant", x)

def op_pretty(op):
    # Hack to convert str rep of binop to just name
    #<class 'ast.Eq'>
    return str(type(op))[12:-2]

def uite(test, then, els):
    # If then else construct that uses Univ
    f = z3.Function("Uite", U, U, U, U)
    return f(test, then, els)

def applpy_expr(expr: ast.expr) -> z3.ExprRef:
    """ Expressions are mostly unproblematic to convert to z3. We could even eval them"""
    match expr:
        case Constant(value, kind=None):
            return applpy_const(value)
        case UnaryOp(op, operand):
            assert type(op) in (UAdd, USub, Not, Invert)
            f = z3.Function(op_pretty(op), U, U)
            return f(applpy_expr(operand))
        case BinOp(left, op, right):
            assert type(op) in (Add, Sub, Mult, MatMult, Div, Mod, Pow, LShift, RShift, BitOr, BitXor, BitAnd, FloorDiv)
            f = z3.Function(op_pretty(op), U, U, U)
            return f(applpy_expr(left), applpy_expr(right))
        case BoolOp(op, values):
            assert type(op) in (And, Or)
            f = z3.Function(op_pretty(op), U, U, U)
            return functools.reduce(f, map(applpy_expr, values))
        case Compare(left, [op], [right]):
            #for op in ops:
            #    assert type(op) in (Eq, NotEq, Lt, LtE, Gt, GtE, Is, IsNot, In, NotIn)
            #print(dump(left))
            #acc = left
            #res = U.bool(True)
            #UAnd = z3.Function(repr(type(op)), U, U, U)
            # TODO handle multiple ops
            #for op, right in zip(ops, comparators):
            #    f = z3.Function(repr(type(op)), U, U, U)
            #    res =   UAnd(res, cur, applpy_expr(right)
            f = z3.Function(op_pretty(op), U, U, U)
            return f(applpy_expr(left), applpy_expr(right))
        case Call(Name(id,ctx), args, keywords):
            assert keywords == []
            targs = [U] * (len(args) + 1)
            f = z3.Function(id, *targs)
            return f(*map(applpy_expr, args))
        case IfExp(test, body, orelse):
            return uite(applpy_expr(test), applpy_expr(body), applpy_expr(orelse))
        case Name(id, ctx):
            return z3.Const(id, U)
        case Tuple(elts, ctx):
            res = U.nil
            for e in reversed(elts):
                res = U.cons(applpy_expr(e), res)
            return res
        case x:
            print("non applpy expresion", x)
            assert False

def applpy_stmts(stmts: list[ast.stmt]) -> z3.ExprRef:
    match stmts[-1]:
        case Return(value):
            res = applpy_expr(value)
        case If(test, body, orelse):
            res = uite(applpy_expr(test), applpy_stmts(body), applpy_stmts(orelse))
        case _:
            raise ValueError("last statement must be a return or ifthenelse", stmts[-1])
    for stmt in stmts[-2::-1]:
        match stmt:
            case Assign([Name(id,ctx)], value):
                e = applpy_expr(value)
                res = z3.substitute(res, (z3.Const(id, U), e))
            case _:
                raise ValueError("intermediate statement must be assignment", dump(stmt))
    return res


applpy_db = {}
def fundef(ast : ast.Module):
    # some nasty unpacking from module and functiondef to grab arguments
    assert len(ast.body) == 1
    ast = ast.body[0]
    assert isinstance(ast, FunctionDef)
    args  = [arg.arg for arg in ast.args.args]
    assert ast.args.posonlyargs == [] and ast.args.kwonlyargs == []
    targs = [U] * (len(args) + 1)
    f = z3.Function(ast.name,*targs)
    print("Applypydef", f(*map(lambda x: z3.Const(x,U), args)), "==", applpy_stmts(ast.body))
    applpy_db[ast.name] = (ast.args, applpy_stmts(ast.body))
    return f

# inspect lets us grab the source of a function
import inspect

def applpy(f):
    """Decorator to grab and register applicative python function"""
    fun = ast.parse(inspect.getsource(f))
    z3_f = fundef(fun)
    return z3_f

@applpy
def foo(x):
    return not x

@applpy
def bar(x,y):
    z = 3
    q = (1,2,3,4 + 5)
    return x + z, 4, q

@applpy
def fact(n):
    if n == 0:
        return 1
    else:
        return n * fact(n-1)
# Hmm. Using python bytecode might be interesting.
# Combined with C interpreter...
fact(U.int(3))
#act(3)
```

    Applypydef foo(x) == Not(x)
    Applypydef bar(x, y) == cons(Add(x, int(3)),
         cons(int(4),
              cons(cons(int(1),
                        cons(int(2),
                             cons(int(3),
                                  cons(Add(int(4), int(5)), nil)))),
                   nil)))
    Applypydef fact(n) == Uite(Eq(n, int(0)), int(1), Mult(n, fact(Sub(n, int(1)))))

# What about Errors?

Indexing into a field that does not exist for example. What do we do? The ACL2 way is totalizing the function by returning `None` basically in this case. This does not strike me as elegant, but it's workable.

# Bits and Bobbles

I'm undecided how to deal with generators. One could perhaps treat them as coinductive, but that is a can of worms.

I haven't handled unpacking or python case statements. These are very useful, and should be unproblematic with the caveat they failing to unpack mst result in some default value error.

Class might be ok if immutable.

To be clear, if one really wanted to attack the totality of python as it stands, you'd have to go a more Hoare logic / weakest precondtion route.

- WhyML has a [pseudo python](https://www.why3.org/doc/input_formats.html#micro-python) notation,
- Viper has Nagini <https://github.com/marcoeilers/nagini>
- <https://deal.readthedocs.io/index.html>
- <https://github.com/pschanely/CrossHair>

I'd like to use external termination checkers like aprove.

[Imandra](https://docs.imandra.ai/imandra-docs/notebooks/welcome/) has a language that is like an acl2 for Ocaml. It actually can be imported as a python package. Maybe what I want is to just pretty print applicative python as ocaml and toss it in there.

```python
import imandra

with imandra.session() as s:
    verify_result = s.verify("fun x -> x * x = 0 ")
print("\n", verify_result)
# oh wait... Its only a cloud service? I can't run it locally? I'm pretty sure I did ths before
```

 They are untyped and garbage collected. There are first class functions and other features that are. Python is missing the rich macro system of lisp. Somehow or other, common lisp has a reputation of being performant because it has good jits I believe.

These points are shared by common theorem proving languages like Coq, Isabelle, and Agda. Proof by reflection. However, these languages are not as familiar to the average programmer. They are more ambitious in their descriptive power as well.

<https://news.ycombinator.com/item?id=1803815> norvig and python

# ACL2

ACL2 is a theorem prover in Common Lisp. The logic is a simplified and purified variation of common lisp itself.

It is a very powerful (in the automation and polish sense) semiautomated system. The logic itself it offers is quite weak by logical standards. This perhaps good

It is somewhat natural to look to this design for inspiration for one that might be appropriate for python. Python shares many properties with lisp. It's a dynamic language with first class functions.

- Untyped lispy terms
- Quantifier free

```python
from z3 import *
U = Datatype('Univ') # PyObject
U.declare('cons', ('car', U), ('cdr', U))
U.declare('bool', ('bool_val', BoolSort()))
U.declare('real', ('real_val', RealSort()))
U.declare('string', ('string_val', StringSort()))
U.declare('int', ('int_val', IntSort()))
U.declare('nil') # None
# float
U = U.create()
print(dir(U))
print(simplify(U.is_bool(U.bool(True))))
print(simplify(U.int_val(U.int(1))))
print(U.cons(U.int(1), U.nil))

# Can I add operations?
#U.__add__ = lambda self, other: U.int(self, other)
car = U.car
cdr = U.cdr
cons = U.cons
nil = U.nil

def atom(x):
    return Not(U.is_cons(x))
def consp(x):
    return U.is_cons(x)
def integerp(x):
    return U.is_int(x)

#Function("ite")

"""
Function("order", U, U, BoolSort())
= RecursiveFunc()
If(is_cons(x),
  And(e0_ordinalp(car(x)), car(x) != U.int(0), 
      e0_ordinalp(cdr(x)), 
      Or(atom(cdr(x)), 
      Not(e0-ord-<(car(x), cadr(x)))),
  And(integerp(x), U.int_val(x) >= 0)))
"""
```

    ['__bool__', '__class__', '__copy__', '__deepcopy__', '__del__', '__delattr__', '__dict__', '__dir__', '__doc__', '__eq__', '__format__', '__ge__', '__getattribute__', '__gt__', '__hash__', '__init__', '__init_subclass__', '__le__', '__lt__', '__module__', '__ne__', '__new__', '__nonzero__', '__reduce__', '__reduce_ex__', '__repr__', '__setattr__', '__sizeof__', '__str__', '__subclasshook__', '__weakref__', '_repr_html_', 'accessor', 'as_ast', 'ast', 'bool', 'bool_val', 'car', 'cast', 'cdr', 'cons', 'constructor', 'ctx', 'ctx_ref', 'eq', 'get_id', 'hash', 'int', 'int_val', 'is_bool', 'is_cons', 'is_int', 'is_nil', 'is_real', 'is_string', 'kind', 'name', 'nil', 'num_constructors', 'real', 'real_val', 'recognizer', 'sexpr', 'string', 'string_val', 'subsort', 'translate', 'use_pp']
    True
    1
    cons(int(1), nil)





    '\nFunction("order", U, U, BoolSort())\n= RecursiveFunc()\nIf(is_cons(x),\n  And(e0_ordinalp(car(x)), car(x) != U.int(0), \n      e0_ordinalp(cdr(x)), \n      Or(atom(cdr(x)), \n      Not(e0-ord-<(car(x), cadr(x)))),\n  And(integerp(x), U.int_val(x) >= 0)))\n'

```python
@applpy
def foo(x):
    match x:
        case "fred":
            return 7
        case (y,z):
            return 1
        case _:
            return 10
```

    ---------------------------------------------------------------------------

    ValueError                                Traceback (most recent call last)

    Cell In [14], line 2
          1 @applpy
    ----> 2 def foo(x):
          3     match x:
          4         case "fred":


    Cell In [13], line 114, in applpy(f)
        112 """Decorator to grab and register applicative python function"""
        113 fun = ast.parse(inspect.getsource(f))
    --> 114 z3_f = fundef(fun)
        115 return z3_f


    Cell In [13], line 104, in fundef(ast)
        102 targs = [U] * (len(args) + 1)
        103 f = z3.Function(ast.name,*targs)
    --> 104 print("Applypydef", f(*map(lambda x: z3.Const(x,U), args)), "==", applpy_stmts(ast.body))
        105 applpy_db[ast.name] = (ast.args, applpy_stmts(ast.body))
        106 return f


    Cell In [13], line 83, in applpy_stmts(stmts)
         81         res = uite(applpy_expr(test), applpy_stmts(body), applpy_stmts(orelse))
         82     case _:
    ---> 83         raise ValueError("last statement must be a return or ifthenelse", stmts[-1])
         84 for stmt in stmts[-2::-1]:
         85     match stmt:


    ValueError: ('last statement must be a return or ifthenelse', <ast.Match object at 0x7ffaeca2f940>)

#

One of the appeals of the ACL2 approach is that it is an pplicative susbet of the underlying language common lisp. Then your specs or models are programs by definition and you can "extract" these simulators. Also perhas some kind of normalization by eval?

# Applicative Python

If I wanted to really hew close to ACL2's design, I could take a subset of python that is purely functional. It'll be harder.

ApplPy (apple-pie)

So I could just use python expressions and be ok.
But "let" statements are pretty sweet.

I could use assignment but only a sequence of them such that the last is a return.
No

if expressions are wonky. I'd like to use if statement syntax.
If I allow joining of the if, it's annoying. I could restrict variables to be scoped to a block (local if) ?
These weird restrictions might be hard to enforce

Could also desugar loops to recursive calls.

```python
# https://greentreesnakes.readthedocs.io/en/latest/nodes.html 
from ast import *
import z3

def applpy_const(x):
    if isinstance(x, int):
        return U.int(z3.IntVal(x))
    else:
        raise ValueError("unsupported constant", x)
def applpy_expr(expr):
    match expr:
        case Constant(value, kind=None):
            print(value)
            return applpy_const(value)
        case UnaryOp(op, operand):
            print(op)
            print(Not)
            assert type(op) in (UAdd, USub, Not, Invert)
            print(type(op))
            print(dump(operand))
            f = z3.Function(str(op), U, U)
            return f(applpy_expr(operand))
        case BinOp(left, op, right):
            assert op in (Add, Sub, Mult, MatMult, Div, Mod, Pow, LShift, RShift, BitOr, BitXor, BitAnd, FloorDiv)
            print(dump(left))
            print(dump(right))
            f = z3.Function(str(op), U, U, U)
            return f(applpy_expr(left), applpy_expr(right))
        case BoolOp(op, values):
            assert op in (And, Or)
            for v in values:
                print(dump(v))
        case Compare(left, ops, comparators):
            for op in ops:
                assert op in (Eq, NotEq, Lt, LtE, Gt, GtE, Is, IsNot, In, NotIn)
            print(dump(left))
            for c in comparators:
                print(dump(c))
        case Call(func, args, keywords):
            assert keywords == []
            print(dump(func))
            for a in args:
                print(dump(a))
            targs = [U] * (len(args) + 1)
            f = z3.Function("call", *targs)
            f(*map(applpy_expr, args))
        case IfExp(test, body, orelse):
            print(dump(test))
            print(dump(body))
            print(dump(orelse))
            
        case Attribute(value, attr, ctx):
            print(dump(value))
        case Subscript(value, slice, ctx):
            print(dump(value))
        case Name(id, ctx):
            print(id)
            return z3.Const(id, U)
        case List(elts, ctx):
            for e in elts:
                print(dump(e))
        case Tuple(elts, ctx):
            for e in elts:
                print(dump(e))
        case Dict(keys, values):
            for k, v in zip(keys, values):
                print(dump(k))
                print(dump(v))
        case Set(elts):
            for e in elts:
                print(dump(e))
        case ListComp(elt, generators):
            print(dump(elt))
            for g in generators:
                print(dump(g))
        case SetComp(elt, generators):
            print(dump(elt))
            for g in generators:
                print(dump(g))
        case DictComp(key, value, generators):
            print(dump(key))
            print(dump(value))
            for g in generators:
                print(dump(g))
        case GeneratorExp(elt, generators):
            print(dump(elt))
            for g in generators:
                print(dump(g))
        case comprehension(target, iter, ifs, is_async):
            print(dump(target))
            print(dump(iter))
            for i in ifs:
                print(dump(i))
        # not going to handle Await, Yield, YieldFrom, FormattedValue, JoinedStr
        case x:
            print("non applpy expresion", x)
            assert False

def lvalue(expr):
    match expr:
        case Name(id, Store):
            print(id)
        # Starred could be handled.
        #case Tuple(elts, Store):
        case x:
            print("disallowed lvalue", x)
            assert False

def applpy_stmt(stmt):
    match stmt:
        case Assign(targets, value):
            for t in targets:
                print(dump(t))
            print(dump(value))
        case Return(value):
            print(dump(value))
            applpy_expr(value)
        case _:
            assert False

def fundef(ast):
    assert isinstance(ast, Module)
    assert len(ast.body) == 1
    ast = ast.body[0]
    assert isinstance(ast, FunctionDef)
    print(ast.name)
    print(ast.args)
    assert ast.args.posonlyargs == [] and ast.args.kwonlyargs == []
    print(ast.body)
    for stmt in ast.body:
        applpy_stmt(stmt)
    print(ast.decorator_list)
    print(ast.returns)
    print(ast.type_comment)
    
tree = parse("not 3", mode="eval")
print(dump(tree))
#apy(tree.body)

import inspect
def applpy(f):
    print(dir(f))
    print(dir(f.__code__))
    print(f.__code__.co_code)
    print(inspect.getsource(f))
    fun = parse(inspect.getsource(f))
    print(dump(fun))
    print(fundef(fun))
    return f

@applpy
def foo(x):
    return not x

# Hmm. Using python bytecode might be interesting.
# Combined with C interpreter...


```

    Expression(body=UnaryOp(op=Not(), operand=Constant(value=3)))
    ['__annotations__', '__builtins__', '__call__', '__class__', '__closure__', '__code__', '__defaults__', '__delattr__', '__dict__', '__dir__', '__doc__', '__eq__', '__format__', '__ge__', '__get__', '__getattribute__', '__globals__', '__gt__', '__hash__', '__init__', '__init_subclass__', '__kwdefaults__', '__le__', '__lt__', '__module__', '__name__', '__ne__', '__new__', '__qualname__', '__reduce__', '__reduce_ex__', '__repr__', '__setattr__', '__sizeof__', '__str__', '__subclasshook__']
    ['__class__', '__delattr__', '__dir__', '__doc__', '__eq__', '__format__', '__ge__', '__getattribute__', '__gt__', '__hash__', '__init__', '__init_subclass__', '__le__', '__lt__', '__ne__', '__new__', '__reduce__', '__reduce_ex__', '__repr__', '__setattr__', '__sizeof__', '__str__', '__subclasshook__', 'co_argcount', 'co_cellvars', 'co_code', 'co_consts', 'co_filename', 'co_firstlineno', 'co_flags', 'co_freevars', 'co_kwonlyargcount', 'co_lines', 'co_linetable', 'co_lnotab', 'co_name', 'co_names', 'co_nlocals', 'co_posonlyargcount', 'co_stacksize', 'co_varnames', 'replace']
    b'|\x00\x0c\x00S\x00'
    @applpy
    def foo(x):
        return not x
    
    Module(body=[FunctionDef(name='foo', args=arguments(posonlyargs=[], args=[arg(arg='x')], kwonlyargs=[], kw_defaults=[], defaults=[]), body=[Return(value=UnaryOp(op=Not(), operand=Name(id='x', ctx=Load())))], decorator_list=[Name(id='applpy', ctx=Load())])], type_ignores=[])
    foo
    <ast.arguments object at 0x7f50a81efac0>
    [<ast.Return object at 0x7f5083aa41f0>]
    UnaryOp(op=Not(), operand=Name(id='x', ctx=Load()))
    <ast.Not object at 0x7f50afc17c70>
    <class 'ast.Not'>
    <class 'ast.Not'>
    Name(id='x', ctx=Load())
    x
    [<ast.Name object at 0x7f5083aa4280>]
    None
    None
    None

```python

```

    Applypydef fact(n) == ite(Eq(n, int(0)), int(1), Mult(n, fact(Sub(n, int(1)))))

fact(int(3))

```python
def is_int(x):
    return U.bool(U.is_int(x))
def pred(f):
    def res(*args):
        return U.bool(f(*args))
    return res
Add_ = RecFunction('UAdd',U,U)
n = FreshConst(U)
RecAddDefinition(Negate, ,  z3.If(   , , U.int(   )  )

```

```python
import pysmt

```

```python
[1,2,3,4,5,6][-2::-1]
```

    [5, 4, 3, 2, 1]

```python
dump(Add)
```

    ---------------------------------------------------------------------------

    TypeError                                 Traceback (most recent call last)

    Cell In [46], line 1
    ----> 1 dump(Add)


    File /usr/lib/python3.10/ast.py:174, in dump(node, annotate_fields, include_attributes, indent)
        171     return repr(node), True
        173 if not isinstance(node, AST):
    --> 174     raise TypeError('expected AST, got %r' % node.__class__.__name__)
        175 if indent is not None and not isinstance(indent, str):
        176     indent = ' ' * indent


    TypeError: expected AST, got 'type'

```python
Add
```

    ast.Add

```python
#should  applypy decorator overload the function in question?
"""
    def res(*args):
        if all(not isinstance(args, z3.AstRef) for arg in args):
           f(*args)
        else:
           z3_f(*args) 
    return res
    """
```

# Termination

We want the ability to make recursive definitions of functions.
Without carefulness these definitions may not terminate or be partial in other ways
This is something to be careful about.

AProve
Dafny termination
ACL2 termination. Ordinal.

Show how to do manually.
Then pythonize
<https://aprove.informatik.rwth-aachen.de/>

```python
%%file /tmp/ex.trs
(VAR x y)
(RULES
    plus(0,y) -> y
    plus(s(x),y) -> s(plus(x,y))
)
```

    Writing /tmp/ex.trs

```python
! java -ea -jar ~/Downloads/aprove.jar -m wst /tmp/ex.trs -p cpf
```

    YES
    <?xml version="1.0" encoding="UTF-8" standalone="no"?><?xml-stylesheet type="text/xsl" href="cpfHTML.xsl"?><certificationProblem xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance" xsi:noNamespaceSchemaLocation="cpf.xsd"><input><trsInput><trs><rules><rule><lhs><funapp><name>plus</name><arg><funapp><name>0</name></funapp></arg><arg><var>y</var></arg></funapp></lhs><rhs><var>y</var></rhs></rule><rule><lhs><funapp><name>plus</name><arg><funapp><name>s</name><arg><var>x</var></arg></funapp></arg><arg><var>y</var></arg></funapp></lhs><rhs><funapp><name>s</name><arg><funapp><name>plus</name><arg><var>x</var></arg><arg><var>y</var></arg></funapp></arg></funapp></rhs></rule></rules></trs></trsInput></input><cpfVersion>2.1</cpfVersion><proof><trsTerminationProof><ruleRemoval><orderingConstraintProof><redPair><knuthBendixOrder><w0>1</w0><precedenceWeight><precedenceWeightEntry><name>0</name><arity>0</arity><precedence>0</precedence><weight>1</weight></precedenceWeightEntry><precedenceWeightEntry><name>s</name><arity>1</arity><precedence>1</precedence><weight>1</weight></precedenceWeightEntry><precedenceWeightEntry><name>plus</name><arity>2</arity><precedence>2</precedence><weight>0</weight></precedenceWeightEntry></precedenceWeight></knuthBendixOrder></redPair></orderingConstraintProof><trs><rules/></trs><trsTerminationProof><rIsEmpty/></trsTerminationProof></ruleRemoval></trsTerminationProof></proof><origin><proofOrigin><tool><name>AProVE</name><version>AProVE Commit ID: 314de9e47ad18e927546098510ed7c36e443eb6d jan-christoph 20231211 unpublished
    </version><strategy>Statistics for single proof: 100.00 % (2 real / 0 unknown / 0 assumptions / 2 total proof steps)</strategy><url>http://aprove.informatik.rwth-aachen.de</url></tool><toolUser><firstName>John</firstName><lastName>Doe</lastName></toolUser></proofOrigin><inputOrigin/></origin></certificationProblem>

```python
import subprocess
res = subprocess.run(["java", "-ea", "-jar", "/home/philip/Downloads/aprove.jar", "/tmp/ex.trs", "-p", "cpf"], capture_output=True, check=True)
print(res)
print(dir(res.stdout))
import xml.etree.ElementTree as ET
tree = ET.fromstring(res.stdout.decode())
print(tree)
print(tree.tag)

```

    CompletedProcess(args=['java', '-ea', '-jar', '/home/philip/Downloads/aprove.jar', '/tmp/ex.trs', '-p', 'cpf'], returncode=0, stdout=b'<?xml version="1.0" encoding="UTF-8" standalone="no"?><?xml-stylesheet type="text/xsl" href="cpfHTML.xsl"?><certificationProblem xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance" xsi:noNamespaceSchemaLocation="cpf.xsd"><input><trsInput><trs><rules><rule><lhs><funapp><name>plus</name><arg><funapp><name>0</name></funapp></arg><arg><var>y</var></arg></funapp></lhs><rhs><var>y</var></rhs></rule><rule><lhs><funapp><name>plus</name><arg><funapp><name>s</name><arg><var>x</var></arg></funapp></arg><arg><var>y</var></arg></funapp></lhs><rhs><funapp><name>s</name><arg><funapp><name>plus</name><arg><var>x</var></arg><arg><var>y</var></arg></funapp></arg></funapp></rhs></rule></rules></trs></trsInput></input><cpfVersion>2.1</cpfVersion><proof><trsTerminationProof><ruleRemoval><orderingConstraintProof><redPair><knuthBendixOrder><w0>1</w0><precedenceWeight><precedenceWeightEntry><name>0</name><arity>0</arity><precedence>0</precedence><weight>1</weight></precedenceWeightEntry><precedenceWeightEntry><name>s</name><arity>1</arity><precedence>1</precedence><weight>1</weight></precedenceWeightEntry><precedenceWeightEntry><name>plus</name><arity>2</arity><precedence>2</precedence><weight>0</weight></precedenceWeightEntry></precedenceWeight></knuthBendixOrder></redPair></orderingConstraintProof><trs><rules/></trs><trsTerminationProof><rIsEmpty/></trsTerminationProof></ruleRemoval></trsTerminationProof></proof><origin><proofOrigin><tool><name>AProVE</name><version>AProVE Commit ID: 314de9e47ad18e927546098510ed7c36e443eb6d jan-christoph 20231211 unpublished\n</version><strategy>Statistics for single proof: 100.00 % (2 real / 0 unknown / 0 assumptions / 2 total proof steps)</strategy><url>http://aprove.informatik.rwth-aachen.de</url></tool><toolUser><firstName>John</firstName><lastName>Doe</lastName></toolUser></proofOrigin><inputOrigin/></origin></certificationProblem>', stderr=b'')
    ['__add__', '__class__', '__contains__', '__delattr__', '__dir__', '__doc__', '__eq__', '__format__', '__ge__', '__getattribute__', '__getitem__', '__getnewargs__', '__gt__', '__hash__', '__init__', '__init_subclass__', '__iter__', '__le__', '__len__', '__lt__', '__mod__', '__mul__', '__ne__', '__new__', '__reduce__', '__reduce_ex__', '__repr__', '__rmod__', '__rmul__', '__setattr__', '__sizeof__', '__str__', '__subclasshook__', 'capitalize', 'center', 'count', 'decode', 'endswith', 'expandtabs', 'find', 'fromhex', 'hex', 'index', 'isalnum', 'isalpha', 'isascii', 'isdigit', 'islower', 'isspace', 'istitle', 'isupper', 'join', 'ljust', 'lower', 'lstrip', 'maketrans', 'partition', 'removeprefix', 'removesuffix', 'replace', 'rfind', 'rindex', 'rjust', 'rpartition', 'rsplit', 'rstrip', 'split', 'splitlines', 'startswith', 'strip', 'swapcase', 'title', 'translate', 'upper', 'zfill']
    <Element 'certificationProblem' at 0x7f07274c90d0>
    certificationProblem

```python
tree.tag
tree.attrib
print([elem.tag for elem in tree])
input = tree.find("input")
print(dir(input))
input.text
ET.tostring(input)
ET.dump(input)
```

    ['input', 'cpfVersion', 'proof', 'origin']
    ['__class__', '__copy__', '__deepcopy__', '__delattr__', '__delitem__', '__dir__', '__doc__', '__eq__', '__format__', '__ge__', '__getattribute__', '__getitem__', '__getstate__', '__gt__', '__hash__', '__init__', '__init_subclass__', '__le__', '__len__', '__lt__', '__ne__', '__new__', '__reduce__', '__reduce_ex__', '__repr__', '__setattr__', '__setitem__', '__setstate__', '__sizeof__', '__str__', '__subclasshook__', 'append', 'attrib', 'clear', 'extend', 'find', 'findall', 'findtext', 'get', 'insert', 'items', 'iter', 'iterfind', 'itertext', 'keys', 'makeelement', 'remove', 'set', 'tag', 'tail', 'text']
    <input><trsInput><trs><rules><rule><lhs><funapp><name>plus</name><arg><funapp><name>0</name></funapp></arg><arg><var>y</var></arg></funapp></lhs><rhs><var>y</var></rhs></rule><rule><lhs><funapp><name>plus</name><arg><funapp><name>s</name><arg><var>x</var></arg></funapp></arg><arg><var>y</var></arg></funapp></lhs><rhs><funapp><name>s</name><arg><funapp><name>plus</name><arg><var>x</var></arg><arg><var>y</var></arg></funapp></arg></funapp></rhs></rule></rules></trs></trsInput></input>

```python
def etree_to_dict(t):
    d = {t.tag : map(etree_to_dict, t.getchildren())}
    d.update(('@' + k, v) for k, v in t.attrib.iteritems())
    d['text'] = t.text
    return d
```

```python
etree_to_dict(input)
```

    ---------------------------------------------------------------------------

    AttributeError                            Traceback (most recent call last)

    Cell In [77], line 1
    ----> 1 etree_to_dict(input)


    Cell In [76], line 2, in etree_to_dict(t)
          1 def etree_to_dict(t):
    ----> 2     d = {t.tag : map(etree_to_dict, t.getchildren())}
          3     d.update(('@' + k, v) for k, v in t.attrib.iteritems())
          4     d['text'] = t.text


    AttributeError: 'xml.etree.ElementTree.Element' object has no attribute 'getchildren'

```python
print(res)
```

    CompletedProcess(args=['java', '-ea', '-jar', '/home/philip/Downloads/aprove.jar', '/tmp/ex.trs', '-p', 'cpf'], returncode=0)

```python
%%file /tmp/term.c
extern int __VERIFIER_nondet_int(void);

int cstrlen(const char *s) {
    const char *p = s;
    while (*p != '\0')
        p++;
    return (int)(p - s);
}

int main() {
    int length = __VERIFIER_nondet_int();
    if (length < 1) {
        length = 1;
    }
    char* nondetString = __builtin_alloca(length * sizeof(char));
    nondetString[length-1] = '\0';
    return cstrlen(nondetString);
}
```

    Overwriting /tmp/term.c

```python
! jar tf ~/Downloads/aprove.jar  # table file
```

```python
! java -ea -jar ~/Downloads/aprove.jar -
```

    ^C

```python

```

    YES
    <?xml version="1.0" encoding="UTF-8" standalone="no"?><?xml-stylesheet type="text/xsl" href="cpfHTML.xsl"?><certificationProblem xmlns:xsi="http://www.w3.org/2001/XMLSchema-instance" xsi:noNamespaceSchemaLocation="cpf.xsd"><input><trsInput><trs><rules><rule><lhs><funapp><name>plus</name><arg><funapp><name>0</name></funapp></arg><arg><var>y</var></arg></funapp></lhs><rhs><var>y</var></rhs></rule><rule><lhs><funapp><name>plus</name><arg><funapp><name>s</name><arg><var>x</var></arg></funapp></arg><arg><var>y</var></arg></funapp></lhs><rhs><funapp><name>s</name><arg><funapp><name>plus</name><arg><var>x</var></arg><arg><var>y</var></arg></funapp></arg></funapp></rhs></rule></rules></trs></trsInput></input><cpfVersion>2.1</cpfVersion><proof><trsTerminationProof><ruleRemoval><orderingConstraintProof><redPair><knuthBendixOrder><w0>1</w0><precedenceWeight><precedenceWeightEntry><name>0</name><arity>0</arity><precedence>0</precedence><weight>1</weight></precedenceWeightEntry><precedenceWeightEntry><name>s</name><arity>1</arity><precedence>1</precedence><weight>1</weight></precedenceWeightEntry><precedenceWeightEntry><name>plus</name><arity>2</arity><precedence>2</precedence><weight>0</weight></precedenceWeightEntry></precedenceWeight></knuthBendixOrder></redPair></orderingConstraintProof><trs><rules/></trs><trsTerminationProof><rIsEmpty/></trsTerminationProof></ruleRemoval></trsTerminationProof></proof><origin><proofOrigin><tool><name>AProVE</name><version>AProVE Commit ID: 314de9e47ad18e927546098510ed7c36e443eb6d jan-christoph 20231211 unpublished
    </version><strategy>Statistics for single proof: 100.00 % (2 real / 0 unknown / 0 assumptions / 2 total proof steps)</strategy><url>http://aprove.informatik.rwth-aachen.de</url></tool><toolUser><firstName>John</firstName><lastName>Doe</lastName></toolUser></proofOrigin><inputOrigin/></origin></certificationProblem>

```python
! java -ea -cp ~/Downloads/aprove.jar aprove.CommandLineInterface.CFrontendMain /tmp/term.c
```

```python
! java -jar ~/Downloads/aprove.jar 
```

    ^C

```bash
%%bash
wget https://github.com/aprove-developers/aprove-releases/releases/download/master_2023_12_29/aprove.jar


```

```python
%%file


```

```python
! java -jar aprove.jar -i test.smt2 -o test.out
```
