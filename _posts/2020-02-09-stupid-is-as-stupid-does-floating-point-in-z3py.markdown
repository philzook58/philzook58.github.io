---
author: philzook58
comments: true
date: 2020-02-09 05:44:21+00:00
layout: post
link: https://www.philipzucker.com/stupid-is-as-stupid-does-floating-point-in-z3py/
slug: stupid-is-as-stupid-does-floating-point-in-z3py
title: 'Stupid is as Stupid Does: Floating Point in Z3Py'
wordpress_id: 2653
categories:
- Formal Methods
tags:
- python
- smt
- z3py
---




Floating points are nice and all. You can get pretty far pretending they are actually numbers. But they don't obey some mathematical properties that feel pretty obvious. A classic to glance through is "What Every Computer Scientist Should Know About Floating-Point Arithmetic" [https://docs.oracle.com/cd/E19957-01/806-3568/ncg_goldberg.html](https://docs.oracle.com/cd/E19957-01/806-3568/ncg_goldberg.html)







We can check some properties with z3py. Here are a couple simple properties that succeed for mathematical integers and reals, but fail for floating point 






```python
from z3 import *
def numbery_proofs(sort):
    
    x = Const("x", sort)
    y = Const("y", sort)
    z = Const("z", sort)
    print("Commutativity")
    prove(x + y == y + x) #Commutativity
    print("Associativity")
    prove(((x + y) + z) == ((x + (y + z)))) #associativity
    print("Additive Identity")
    prove(x + 0 == x) # 0 additive identity
    print("Multiplicative Identity")
    prove(1 * x == x)
    print("Trichotomy")
    prove(Or(x > 0, x < 0, x == 0)) #trichotomy
    print("Distributivity")
    prove(x * (y + z) == x * y + x * z)
    print("Square positive")
    prove(x * x >= 0)
print("Ints -----------------")
numbery_proofs(IntSort())
print("Reals ---------------")
numbery_proofs(RealSort())
print("Float----------------")
numbery_proofs(Float16())


''' Output
Ints -----------------
Commutativity
proved
Associativity
proved
Additive Identity
proved
Multiplicative Identity
proved
Trichotomy
proved
Distributivity
proved
Square positive
proved
Reals ---------------
Commutativity
proved
Associativity
proved
Additive Identity
proved
Multiplicative Identity
proved
Trichotomy
proved
Distributivity
proved
Square positive
proved
Float----------------
Commutativity
proved
Associativity
counterexample
[z = -1.9375*(2**8),
 y = 1.0009765625*(2**14),
 x = 1.5224609375*(2**4)]
Additive Identity
counterexample
[x = -0.0]
Multiplicative Identity
proved
Trichotomy
counterexample
[x = NaN]
Distributivity
counterexample
[z = -1.0029296875*(2**-2),
 y = 1.01171875*(2**-10),
 x = -1.4833984375*(2**8)]
Square positive
counterexample
[x = NaN]
'''
```






I recently saw on twitter a reference to a Sylvie Boldo paper [https://hal.archives-ouvertes.fr/hal-01148409/](https://hal.archives-ouvertes.fr/hal-01148409/) "Stupid is as Stupid Does: Taking the Square Root of the Square of a Floating-Point Number".








[https://twitter.com/fatlimey/status/1225496023553978369?s=20](https://twitter.com/fatlimey/status/1225496023553978369?s=20)








In it, she uses FlocQ and Coq to prove a somewhat surprising result that the naive formula $ \sqrt{x^2} = \|x\|$ actually is correct for the right rounding mode of floating point, something I wouldn't have guessed.







Z3 confirms for `Float16`. I can't get `Float32` to come back after even a day on a fairly beefy computer. If I use `FPSort(ebits,sbits)` rather than a standard size, it just comes back unknown, so i can't really see where the cutoff size is. This does not bode well for checking properties of floating point in z3 in general. I think a brute force for loop check of 32 bit float properties is feasible. It might even be pretty fast. To some degree, if z3 is taking forever to find a counterexample, I wonder to what to degree the property is probably true.







If anyone has suggestions, I'm all ears.






```python
from z3 import *
x = FP("x", Float16())
rm = RNE() # Rounding Nearest Ties to Even
x2 = fpMul(rm, x, x)
absx1 = fpSqrt(rm, x2)
absx2 = fpAbs(x)

s = Solver()
s.add( 0.01 <= x, x <= 100)
s.add( absx1 != absx2)
res = s.check()
print(res)
if res == sat:
    m = s.model()
    print(m.eval(absx1))
    print(m.eval(absx2))
```


