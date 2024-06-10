---
title: Knuckledraggin' Kleene Algebra
date: 2024-06-10
---

I was in the audience watching Alexandra Silva teach Kleene Algebra with tests last week
<https://www.cs.uoregon.edu/research/summerschool/summer24/topics.php#Silva>

She gave some example problems

```
a* a* = a*
a** = a*
goal = Implies(x*y == y*z, star(x) * y == y * star(z))

```

I thought it's a fun example to try out [knuckledragger](https://github.com/philzook58/knuckledragger), my z3 based python proof assistant.

Kleene algebra is also very interesting in that it has an axiom that is the analog of induction, but does not require persay bringing in higher order logic. Food for thought.

First I define the signature and backhack in operator overloading on z3 `ExprRef`. I've got some ideas on how to add this to the library in a more principled way ([singledispatch](https://docs.python.org/3/library/functools.html#functools.singledispatch) style overloading on ExprRef's operators using z3 sorts to disambiguate. I'm trying to stick to things that are pythonic)

```python

from knuckledragger import lemma, axiom
from z3 import *


K = DeclareSort("K")
o = Const("0", K)
l = Const("1", K)
char = Function("char", StringSort(), K) # injective btw
a = char(StringVal("a"))
b = char(StringVal("b"))
seq = Function("seq", K,K,K)
par = Function("par", K,K,K)
star = Function("star", K,K)

ExprRef.__mul__ = lambda x,y: seq(x,y)
ExprRef.__add__ = lambda x,y: par(x,y)
ExprRef.__le__ = lambda x,y: x + y == y

sig = [K, o, l, seq, par, star]

x,y,z,e,f = Consts("x y z e f", K)



```

Here's the axioms from lecture. There was some discussion

```python
#  kozen axioms
# from egglog https://github.com/philzook58/egg-smol/blob/scratchpad2/tests/kleene.egg
par_assoc = axiom(ForAll([x,y,z], x + (y + z) == (x + y) + z))
par_comm = axiom(ForAll([x,y], x + y == y + x))
par_idem = axiom(ForAll([x], x + x == x))
par_zero = axiom(ForAll([x], x + o == x))

seq_assoc = axiom(ForAll([x,y,z], x * (y * z) == (x * y) * z))
seq_zero = axiom(ForAll([x], x * o == o))
seq_one = axiom(ForAll([x], x * l == x))

rdistrib = axiom(ForAll([x,y,z], x * (y + z) == x * y + x * z))
ldistrib = axiom(ForAll([x,y,z], (y + z) * x == y * x + z * x))

unfold = axiom(ForAll([e], star(e) == l + e * star(e)))

# If a set shrinks, star(e) is less than it
least_fix = axiom(ForAll([x,e,f], Implies(f + e * x <= x, star(e) * f <= x)))

kleene = [par_assoc, par_comm, par_idem, par_zero, 
    seq_assoc,  seq_zero, seq_one, 
    ldistrib, rdistrib, unfold, least_fix] 
```

Some toy lemmas. I recently added an overload on the proof objects to pretty print with the turnstile. Maybe a bad idea.

```python
par_lzero = lemma(ForAll([x], o + x == x), by=kleene)

par_monotone = lemma(ForAll([x,y,z], Implies(x <= y, x + z <= y + z)), by=kleene)
seq_monotone = lemma(ForAll([x,y,z], Implies(x <= y, x * z <= y * z)), by=kleene)

seq_monotone
```

&ctdot; &#8870;&forall;x, y, z :
 par(x, y) = y &rArr; par(seq(x, z), seq(y, z)) = seq(y, z)

The first problem is pretty easy actually. Unfolding and then reassociating and commutativity is enough. The `calc` combinator/tactic is useful. It's inspired by dafny/lean. I've done similar things in many systems

```python
def calc(*args, by=[], vars=[x]):
    lemmas = []
    for a,b in zip(args[:-1], args[1:]):
        lemmas.append(lemma(ForAll(vars,a == b), by=by))
    return lemma(ForAll(vars, args[0] == args[-1]), by=lemmas)

star_star = calc(star(x) * star(x),
    (l + x * star(x)) * (l + x * star(x)), # unfold
    (l + l) + (x * star(x) + x * star(x)), # reassoc
    l + x * star(x), # idem
    star(x),   #refold
    by=kleene
)

star_star
```

&ctdot; &#8870;&forall;x : seq(star(x), star(x)) = star(x)

The next one took a little thought.

```python
def xlemma(thm,by=[]):
    return lemma(ForAll([x], thm), by=by)

_1 = xlemma(Implies(star(x)*star(x) + l <= star(x), star(star(x)) <= star(x)), by=kleene)
_2 = calc(star(x)*star(x) + l <= star(x),   star(x) + l == star(x) , by=kleene)
_3 = calc(star(x) + l, star(x), by=kleene)
_4 = xlemma(star(star(x)) <= star(x), by=kleene + [_1,_2,_3])

xlemma(star(star(x)) == star(x), by=kleene + [_4])



```

&ctdot; &#8870;&forall;x : star(star(x)) = star(x)

# Bits and Bobbles

I'm flagging a bit on proving the others. Opportunity for another blog post!

Finishing out the homework problems.

Actually doing kleene algebra modulo tests could be neat.

But this has made it tempting that I would like something akin to an apply tactic and also the ability to toss into twee.

I also would like the ability to keep the ForAll implicit more easily.

Calc should go into the library

Proof pruning via unsat core would be helpful

Z3 has built in regex, so reflecting to them might be interesintg

Using general purpose equational reasoning for kleene algerba is obscene. There are special automata thingies for it. Some things are decidable. I think this is kind of the benefit of KAT.

A while back I did something similar in egglog inspired by something Greenberg was doing in egg 1 <https://github.com/philzook58/egg-smol/blob/scratchpad2/tests/kleene.egg>

KAT modulo theories. Port to python?

Ideas on overloading

```python
# This is kind of oleg's thing
__add_methods = {}
#ExprRef.__add__ = lambda self,other: __add_methods[self.sort()](self, other)
#ExprRef.__mul__ = 

# could also use multi dissatch
def register_add(sort, func):
    add_methods[sort] = func
def deregister_add()

# Hmm. It disdpatch on the python type though. No the z3 sort. 
from functools import singledispatch
@singledispatch
def add(x,y):
    raise NotImplementedError("Unsupported type")
ExprRef.__add__ = add

# Is this too overwrought?

class ExprDispatch(): # Sort dispatch
    def __init__(self):
        self.methods = {}
    def register(self, sort, func):
        self.methods(sort) = func
    def __call__(self, *args, **kwargs):
        return self.methods[args[0].sort()](args, kwargs)

add = ExprDispatch()
ExprRef.__add__ = add

mul = ExprDispatch()
ExprRef.__mul__ = mul

sub = ExprDispatch()
ExprRef.__sub__ = sub

matmul = ExprDispatch()
ExprRef.__matmul__ = matmul
```

The rawer non library form I was playing with.

```python
from z3 import *
def lemma(thm, by=[], admit=False):
    if admit:
        print("Admitted!!!")
    else:
        prove(Implies(And(by), thm))
    return thm


K = DeclareSort("K")
o = Const("0", K)
l = Const("1", K)
char = Function("char", StringSort(), K)
a = char(StringVal("a"))
b = char(StringVal("b"))
seq = Function("seq", K,K,K)
par = Function("par", K,K,K)
star = Function("star", K,K)

ExprRef.__mul__ = lambda x,y: seq(x,y)
ExprRef.__add__ = lambda x,y: par(x,y)
ExprRef.__le__ = lambda x,y: x + y == y

x,y,z,e,f = Consts("x y z e f", K)

#  kozen axioms
# from egglog https://github.com/philzook58/egg-smol/blob/scratchpad2/tests/kleene.egg
par_assoc = ForAll([x,y,z], x + (y + z) == (x + y) + z)
par_comm = ForAll([x,y], x + y == y + x)
par_idem = ForAll([x], x + x == x)
par_zero = ForAll([x], x + o == x)

seq_assoc = ForAll([x,y,z], x * (y * z) == (x * y) * z)
seq_zero = ForAll([x], x * o == o)
seq_one = ForAll([x], x * l == x)

rdistrib = ForAll([x,y,z], x * (y + z) == x * y + x * z)
ldistrib = ForAll([x,y,z], (y + z) * x == y * x + z * x)

unfold = ForAll([e], star(e) == l + e * star(e))

# If a set shrinks, star(e) is less than it
least_fix = ForAll([x,e,f], Implies(f + e * x <= x, star(e) * f <= x))




sig = [K, o, l, seq, par, star]
kleene = [par_assoc, par_comm, par_idem, par_zero, 
    seq_assoc,  seq_zero, seq_one, 
    ldistrib, rdistrib, unfold, least_fix] 

#lemma(ForAll([x], star(star(x)) == star(x)), by=kleene)

par_lzero = lemma(ForAll([x], o + x == x), by=kleene)

par_monotone = lemma(ForAll([x,y,z], Implies(x <= y, x + z <= y + z)), by=kleene)
seq_monotone = lemma(ForAll([x,y,z], Implies(x <= y, x * z <= y * z)), by=kleene)

def calc(*args, by=[]):
    for a,b in zip(args[:-1], args[1:]):
        prove(Implies(And(by), a == b))
    return args[0] == args[-1]

calc(
    star(x),
    star(x),
    by=kleene)

zero_star = lemma(star(o) == l, by=kleene)

lemma(ForAll([x], x <= star(x)), by=kleene)

star_0 = calc(star(o),        # unfold loop
    l + o * star(o), # o * x = x
    l,
    by=kleene
)

star_x_x = calc(star(x) + x,
   l + x * star(x) + x,
   l + x * star(x),
   star(x),
   by=kleene
)

lemma(ForAll([x], l <= star(x)), by=kleene)

calc(star(x) + l, #unfold
    l + l + x * star(x),
    l + x*star(x), # assoc and idem(1)
    star(x),
    by=kleene
)

calc(star(x) * star(x),
    (l + x * star(x)) * (l + x * star(x)), # unfold
    (l + l) + (x * star(x) + x * star(x)), # reassoc
    l + x * star(x), # idem
    star(x),   #refold
    by=kleene
)

expand_eq = lemma(ForAll([x,y], (x == y) == And(x <= y, y <= x)), by=kleene)



lemma(ForAll([x,e,f], Implies(e * x + l <= x, star(e) <= x)), by=kleene)


lemma(star(l) <= l, by=kleene)
one_star = lemma(star(l) == l, by=kleene)




#calc(star(star(x)) == star(x)



```

    proved
    proved
    proved
    proved
    proved
    proved
    proved
    proved
    proved
    proved
    proved
    proved
    proved
    proved
    proved
    proved
    proved
    proved
    proved
    proved
    proved
    proved
    proved

```python
# Am I being bellgrent here not using dataclasses?
def seq(a,b):
    return ("seq", a, b)
def par(a,b):
    return ("par", a, b)
def star(a):
    return ("star", a)
zero = ("zero",)
one = ("one",)

RE = "RE"
def E(x : RE) -> bool:
    match x:
        case ("zero",):
            return False
        case ("one",):
            return True
        case ("char", _):
            return False
        case ("seq",a, b):
            return E(a) and E(b)
        case ("par", a, b):
            return E(a) or E(b)
        case ("star", a):
            return True

assert E(seq(one,one)) 

# What. How did copilot fill this out.
def D(a : str, x : RE) -> RE:
    match x:
        case ("zero",):
            return zero
        case ("one",):
            return zero
        case ("char", c):
            if c == a:
                return one
            else:
                return zero
        case ("seq", b, c):
            return par(seq(D(a,b), c), seq(E(b), D(a,c)))
        case ("par", b, c):
            return par(D(a,b), D(a,c))
        case ("star", b):
            return seq(D(a,b), x)


```

Regular Sets and Regular Expressions

```python
from z3 import *
RE = Datatype("RE")
RE.declare("0")
RE.declare("1")
RE.declare("char", ("c", StringSort()))
RE.declare("seq", ("a", RE), ("b", RE))
RE.declare("par", ("a", RE), ("b", RE))
RE.declare("star", ("a", RE))
RE = RE.create()

denote = Function("denote", REsyn, RE)

# Note also that z3 supports regex
```

    ---------------------------------------------------------------------------

    NameError                                 Traceback (most recent call last)

    Cell In [15], line 11
          8 RE.declare("star", ("a", RE))
          9 RE = RE.create()
    ---> 11 denote = Function("denote", REsyn, RE)


    NameError: name 'REsyn' is not defined

```python





```

    proved
    proved
    proved
    proved
    proved

star(star(x)) = star(x)

```python
goal = Implies(x*y == y*z, star(x) * y == y * star(z))

def calc(*args, by=[], ctx=[]):
    for a,b in zip(args[:-1], args[1:]):
        prove(Implies(And(by), Implies(And(ctx), a == b)))
    return Implies(And(ctx), args[0] == args[-1])

calc(
    star(x) * y,
    (l + x * star(x)) * y,
    
    by=kleene,
    ctx = [x*y == y*z]
)


```

```python

```

    proved
    proved

```python
# twee style
import subprocess
sig = [
    "k : $tType",
    "* : k * k > k",
    "+ : k * k > k"
]
def lemma(th, by=[]):
    with open("/tmp/lemma.p", "w") as f:
        #for s in sig:
        #    f.write(f"type(type_def, type, {s}).\n")
        for hyp in by:
            f.write(f"fof(ax,axiom,{hyp}).\n")
        f.write(f"fof(mygoal, conjecture, {th}).\n")
        f.flush()
    res = subprocess.run(["/home/philip/Downloads/twee", "/tmp/lemma.p"], capture_output=True)
    print(res.stdout.decode())
    print(res.stderr.decode())






par_assoc = "![A,B,C]: A + (B + C) = (A + B) + C"
par_comm = "![A,B,C] : A + B = B + A"
par_idem = "![A] : A + A = A"
par_zero = "![A] : A + o = A"

seq_assoc = "![A,B,C] : A * (B * C) = (A * B) * C"
seq_rzero = "![A] : A * o = o"
seq_rone = "![A] : A * l = A"
seq_lzero = "![A] : o * A = o"
seq_lone = "![A] : l * A = A"

rdistrib = "![A,B,C] : A * (B + C) = (A * B) + (A * C)"
ldistrib = "![A,B,C] : (B + C) * A = (B * A) + (C * A)"



le_def = "![A,B] : ((A <= B) = (A + B = B))"
unfold = "![E] : (star(E) = l + (E * star(E)))"
least_fix = "![X,E,F] : ((X * F + E <=  X) => (star(E) * F <= X))"

kleene = [par_assoc, par_comm, par_idem, par_zero,
    seq_assoc,  seq_rzero, seq_rone, seq_lzero, seq_lone, unfold,
    ldistrib, rdistrib] # least_fix, le_def] 

#lemma("x + y = y + x",by=[par_comm])

#lemma("star(e) = l + e + star(e)", by=kleene)
#lemma("x + y = y + x",by=kleene)
lemma("star(l) = l + (l * star(l))", by=kleene)
lemma("star(l) = l + star(l)", by=kleene)
#lemma("star(l) = ")


```

    Here is the input problem:
      Axiom 1 (flattening): star2 = star(l).
      Axiom 2 (ax): X + X = X.
      Axiom 3 (ax): X + Y = Y + X.
      Axiom 4 (ax): X + o = X.
      Axiom 5 (ax): X * o = o.
      Axiom 6 (ax): X * l = X.
      Axiom 7 (ax): o * X = o.
      Axiom 8 (ax): l * X = X.
      Axiom 9 (flattening): *2 = l * star(l).
      Axiom 10 (ax): X + (Y + Z) = (X + Y) + Z.
      Axiom 11 (ax): X * (Y * Z) = (X * Y) * Z.
      Axiom 12 (ax): star(X) = l + (X * star(X)).
      Axiom 13 (flattening): +2 = l + (l * star(l)).
      Axiom 14 (ax): X * (Y + Z) = (X * Y) + (X * Z).
      Axiom 15 (ax): (X + Y) * Z = (X * Z) + (Y * Z).
      Goal 1 (mygoal): star(l) = l + (l * star(l)).
    
    1. star(l) -> star2
    2. X + X -> X
    3. X + Y <-> Y + X
    4. X + o -> X
    5. X * o -> o
    6. X * l -> X
    7. o * X -> o
    8. l * X -> X
    9. star2 -> *2
    10. (X + Y) + Z -> X + (Y + Z)
    11. (X * Y) * Z -> X * (Y * Z)
    12. l + (X * star(X)) -> star(X)
    13. *2 -> +2
    14. (X * Y) + (X * Z) -> X * (Y + Z)
    15. (X * Y) + (Z * Y) -> (X + Z) * Y
    16. star(o) -> l
    17. o + X -> X
    18. +2 + l -> +2
    
    The conjecture is true! Here is a proof.
    
    Axiom 1 (ax): star(X) = l + (X * star(X)).
    
    Goal 1 (mygoal): star(l) = l + (l * star(l)).
    Proof:
      star(l)
    = { by axiom 1 (ax) }
      l + (l * star(l))
    
    RESULT: Theorem (the conjecture is true).
    
    
    Here is the input problem:
      Axiom 1 (flattening): star2 = star(l).
      Axiom 2 (ax): X + X = X.
      Axiom 3 (ax): X + Y = Y + X.
      Axiom 4 (ax): X + o = X.
      Axiom 5 (ax): X * o = o.
      Axiom 6 (ax): X * l = X.
      Axiom 7 (ax): o * X = o.
      Axiom 8 (ax): l * X = X.
      Axiom 9 (flattening): +2 = l + star(l).
      Axiom 10 (ax): X + (Y + Z) = (X + Y) + Z.
      Axiom 11 (ax): X * (Y * Z) = (X * Y) * Z.
      Axiom 12 (ax): star(X) = l + (X * star(X)).
      Axiom 13 (ax): X * (Y + Z) = (X * Y) + (X * Z).
      Axiom 14 (ax): (X + Y) * Z = (X * Z) + (Y * Z).
      Goal 1 (mygoal): star(l) = l + star(l).
    
    1. star(l) -> star2
    2. X + X -> X
    3. X + Y <-> Y + X
    4. X + o -> X
    5. X * o -> o
    6. X * l -> X
    7. o * X -> o
    8. l * X -> X
    9. star2 + l -> +2
    10. (X + Y) + Z -> X + (Y + Z)
    11. (X * Y) * Z -> X * (Y * Z)
    12. l + (X * star(X)) -> star(X)
    13. (X * Y) + (X * Z) -> X * (Y + Z)
    14. (X * Y) + (Z * Y) -> (X + Z) * Y
    15. star(o) -> l
    16. o + X -> X
    17. star2 -> +2
    
    The conjecture is true! Here is a proof.
    
    Axiom 1 (ax): l * X = X.
    Axiom 2 (ax): star(X) = l + (X * star(X)).
    
    Goal 1 (mygoal): star(l) = l + star(l).
    Proof:
      star(l)
    = { by axiom 2 (ax) }
      l + (l * star(l))
    = { by axiom 1 (ax) }
      l + star(l)
    
    RESULT: Theorem (the conjecture is true).

Matrices with kleene algeba elements are also a kleene algebra.
Star ought to be (1-A)^-1. The schur complement appears in some shaky frrm
A DFA can be reprented by a matrix wth the elements as the thingd between states.
Suggestion:

Open automata ~ recursive sovng of linear algebra
Mnimal automata ~ rank? Some kind of SVD? Projection matrices are the mapping from state to minimal state and the lifting back. 1/0 matrices.representing epsin transtions.

The b are observables? 1/0 diagonal in matrx / automata rep

Quantum anaogy? Kronckecer product (?). Fock space. Symmettry between subspaces?
Path integral? Kleene intergation instead of grassmann integration

Network matrices for composition. ABCD scatterg parameters etc.L

Linear RelationsFu

Fun with semrings
