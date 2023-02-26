---
layout: post
title: Computer Algebra
---
See Also:
- Differential Equations
- Term rewriting
- Computer Numbers

https://en.wikipedia.org/wiki/Computer_algebra_system


# Systems
FriCAS
Axiom


https://twitter.com/jjcarett2/status/1598627244292935681?s=20&t=5JLrAKIKjXwiuDermxDT0g  Schwartz-Zippel and polynomial identity testing
https://arxiv.org/abs/2211.09691


https://www.philipzucker.com/a-smattering-of-physics-in-sympy/

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

# Integration
https://en.wikipedia.org/wiki/Symbolic_integration

Risch algorithm
https://en.wikipedia.org/wiki/Risch_algorithm


https://groups.google.com/g/sci.math.symbolic