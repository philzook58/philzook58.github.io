
<https://en.wikipedia.org/wiki/Hypergeometric_function>

$ F(a;b;c,z) = \sum_{n=0}^\infty \frac{(a)_n (b)_n}{(c)_n} \frac{z^n}{n!} $
Pockhammer / rising factorial.

The ratio of subsequent terms is [rational function](https://en.wikipedia.org/wiki/Rational_function) (numerator and denom are polynomials). This implies that it has a factorial representation?

Solution of second order linear differential equation.

<https://en.wikipedia.org/wiki/Generalized_hypergeometric_function> generalized

A = B

WZ pair. What's up with that

Gosper's algorithm. It's not that complicated?

Many common functions are hypergeometric. What's up with that?

```python
import sympy
```

matrix argument <https://en.wikipedia.org/wiki/Hypergeometric_function_of_a_matrix_argument> huh

Tower of Hanoi

```python
from z3 import *

f = Function("f", IntSort(), IntSort())
ax = ForAll([n], f(n) = If(n <= 0, 1, 2f(n-1) + 1))

```
