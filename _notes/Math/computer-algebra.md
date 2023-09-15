---
layout: post
title: Computer Algebra
---
- [Systems](#systems)
- [Sympy](#sympy)
- [Integration](#integration)
- [Maxima](#maxima)
- [Reduce](#reduce)
- [Axiom](#axiom)
- [Macaulay](#macaulay)
- [GAP](#gap)
- [Singular](#singular)
- [Misc](#misc)

See Also:

- Differential Equations
- Term rewriting
- Computer Numbers

<https://en.wikipedia.org/wiki/Computer_algebra_system>

# Systems

FriCAS
Axiom

<https://twitter.com/jjcarett2/status/1598627244292935681?s=20&t=5JLrAKIKjXwiuDermxDT0g>  Schwartz-Zippel and polynomial identity testing
<https://arxiv.org/abs/2211.09691>

# Sympy
<https://news.ycombinator.com/item?id=37430759> [towards a new sympy](https://oscarbenjamin.github.io/blog/czi/post1.html) interesting. Automatic evaluation is a perf problem. Moving towards using poly algebraic structures than generic symbolic featurz

Symengine

<https://www.philipzucker.com/a-smattering-of-physics-in-sympy/>

[sympy makes math fun agan](https://news.ycombinator.com/item?id=34936831)

```python
from sympy import *
init_printing()
t,a,d,vf,vi = symbols("t a d vf vi")
e1 = Eq(d , vi * t + 1/2 * a * t ** 2)
tsub = solve(Eq(vf , vi + a * t),t)[0]
print(tsub) # This is assuming a is nonzero though.
expand(simplify(e1.subs(t,tsub)))
```

<https://leanprover.github.io/theorem_proving_in_lean4/conv.html>

```python

class Proof():
    def __init__(self,expr):
        self.steps = []
        self.ctx = []
        self.expr = expr
    def arg(self,n):

    def cong(self): #pop up 
    def simp(self):
        self.steps.append("simp")
        self.expr = simplify(self.expr)
    def expand(self):
    def factor(self):
    def comm(self):
    def assoc(self):
    def apply(self,eq):

    def subst(self,e):
        assert sympy.Eq(e)
        self.steps.append(("rw", e))
        self.expr = e
    def pprint(self):
        map(latex, self.steps)


```

# Integration
<https://en.wikipedia.org/wiki/Symbolic_integration>

Risch algorithm
<https://en.wikipedia.org/wiki/Risch_algorithm>
"heuristic risch"

<https://docs.sympy.org/latest/modules/integrals/integrals.html>
Meijer G functions.
Closed form for definite integrals even in compound terms
They also have "hand" mode which returns steps

<https://groups.google.com/g/sci.math.symbolic>

[Does there exist a complete implementation of the Risch algorithm?](https://news.ycombinator.com/item?id=37124059)
[Bronstein Book](https://link.springer.com/book/10.1007/b138171)

Schanuel Conjecture

# Maxima

```bash
echo "
print(hello);
 expand ((x + y)^6);
factor (x^6 - 1);
exp(%i*%pi);
linsolve ([3*x + 4*y = 7, 2*x + a*y = 13], [x, y]);
solve (x^3 - 3*x^2 + 5*x = 15, x);
eq_2: 3*x + y = 1$  # $ is silent
plot2d (sin(x)/x, [x, -20, 20])$
?? integ
quit();
" | maxima

`%` is most recent calculated
Also can refer to by assigned number
```

# Reduce

# Axiom
<https://github.com/daly/axiom>
Hmm I can't get it too install. soorrrry axiom

# Macaulay

# GAP

# Singular

# Misc
<http://www.sc-square.org/schools.html>
