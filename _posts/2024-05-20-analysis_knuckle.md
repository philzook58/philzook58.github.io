---
title: Proving Sum n = n*(n-1)/2 and that 1/n tends to 0.
date: 2024-05-20
---

Some more interesting semi-automated proofs in python using smt solvers.

Finite sums ought to be a pretty straightforward thing to prove if you have some closed form you're trying to confirm. Basically an induction step can manipulate the sum and show that the closed formula remains true.

A classic example is $\sum_n n = n*(n-1)/2$

We could use sympy to get this result for us. And indeed, stuff like this is one of the compelling reasons to be in python with it's ridiculously wide ecosysytem.

```python
import sympy as sp
import sympy.abc as abc

# sum is inclusive of boundaries.
sp.Sum(abc.n, (abc.n, 0, abc.m-1)).doit()
```

$\displaystyle \frac{m^{2}}{2} - \frac{m}{2}$

But then we may find it pleasant to confirm this result via something more proof flavored. `sympy` isn't often wrong, but it is possible for it to take optimistic assumptions.

I repeat many of the things from previous posts. I make uninterpreted wrappers for `+`, `*` because z3 can't ematch well on interpreted symbols. I suspect what I have to do is something akin to a linartih and ring tactic, where i allow the solver access to these wrapper definitions only when I know the result basically follows by trivial arithmetical reasoning.

```python
from z3 import *

B = BoolSort()
Z = IntSort()
R = RealSort()
x,y,z = Reals('x y z')

def lemma(thm, by=[], admit=False):
    if not admit:
        #print(Implies(And(by), thm).sexpr())
        prove(Implies(And(by), thm))
    else:
        print("Admitted!!", thm)
    return thm
    
plus = Function("plus", R,R,R)
plus_def = ForAll([x, y], plus(x, y) == x + y)

plus_0 = lemma(ForAll([x], plus(x, 0) == x), by=[plus_def])
plus_comm = lemma(ForAll([x, y], plus(x, y) == plus(y, x)), by=[plus_def])
plus_assoc = lemma(ForAll([x, y, z], plus(x, plus(y, z)) == plus(plus(x, y), z)), by=[plus_def])
                   
mul = Function("mul", R,R,R)
mul_def = ForAll([x, y], mul(x, y) == x * y)

mul_zero = lemma(ForAll([x], mul(x, 0) == 0), by=[mul_def])
mul_1 = lemma(ForAll([x], mul(x, 1) == x), by=[mul_def])
mul_comm = lemma(ForAll([x, y], mul(x, y) == mul(y, x)), by=[mul_def])
mul_assoc = lemma(ForAll([x, y, z], mul(x, mul(y, z)) == mul(mul(x, y), z)), by=[mul_def])
mul_distrib = lemma(ForAll([x, y, z], mul(x, plus(y, z)) == plus(mul(x, y), mul(x, z))), by=[mul_def, plus_def])        
```

    proved
    proved
    proved
    proved
    proved
    proved
    proved
    proved

Perhaps a bit more interesting is the notion of relating the naturals and reals. The naturals are nice because they have a clean notion of induction.

There are some possible design choices here.

- Nat as an algebraic data type with explicit mappings.
- Use the Nats as a non negative subset of `IntSort()`. We could write an induction principle
- The nats are a subsets of the reals. Then there is no casting to be done. Directly use real induction perhaps <https://math.stackexchange.com/questions/4202/induction-on-real-numbers>

I think the first is the most straightforward and less error prone. It may also require the most manual casting though.

```python
Nat = Datatype("Nat")
Nat.declare('zero')
Nat.declare('succ', ('pred', Nat))
Nat = Nat.create()
n,m,k = Consts('n m k', Nat)

def induct(P):
    return Implies(And(P(Nat.zero), ForAll([n], Implies(P(n), P(Nat.succ(n))))),
                   #-----------------------------------------------------------
                   ForAll([n], P(n)))

real = Function("real", Nat, R)
real_def = ForAll([n], real(n) == If(Nat.is_zero(n), 0, plus(1, real(Nat.pred(n)))))

```

With this, we can define a sequence as a function `Nat -> R` and a bounded `sum_` function via the recursive definition. This is how one would write the same in a functional program.

It is interesting to note that the natural thing to do is define sum to not be inclusive of it's upper boundary. In other words $\sum_{i=0}^{0} c_i = 0$

```python
Seq = ArraySort(Nat, R)
sum_ = Function("sum", Seq, Nat, R)
s = Const('s', Seq)
sum_def = ForAll([s, n], sum_(s, n) == If(n == Nat.zero, 0, plus(s[Nat.pred(n)], sum_(s, Nat.pred(n)))))
```

As a baby step, we can prove that $\sum_{i=0}^n 0 = 0$. `szero` is the constant $0$ sequence.
I think I initially had difficulty getting this to go through in one show, but then I realized that I wasn't being totally syntactic in the base case of the induction.

```python
szero = K(Nat, RealVal(0))

#sum_const_base = lemma(sum_(szero, Nat.zero) == 0, by=[sum_def, plus_def])
#sum_const_induct = lemma(ForAll([n], Implies(sum_(szero, n) == 0, 
#                                             sum_(szero, Nat.succ(n)) == 0)),
#                         by=[sum_def, plus_def])
sum_szero = lemma(ForAll([n], sum_(szero,n) == 0), by=[sum_def, plus_def, induct(lambda n: sum_(szero, n) == 0)])


```

    proved

Next is summing a constant $\sum^n_{i=0} c = n*c$

```python

# note I original wrote ForAll([x], sum_(K(Nat, x), Nat.zero) == 0) which is not thed correct syntactic hypothesis.
# it wouldn't go through.
sum_const_base = lemma(ForAll([x], sum_(K(Nat, x), Nat.zero) == mul(real(Nat.zero), x)), 
                       by=[sum_def, mul_def, real_def])
sum_const_induct = lemma(ForAll([n], Implies(ForAll([x], sum_(K(Nat, x), n) == mul(real(n), x)), 
                                             ForAll([x], sum_(K(Nat, x), Nat.succ(n)) == mul(real(Nat.succ(n)), x)))),
                         by=[sum_def, plus_def, mul_def, real_def])
sum_const = lemma(ForAll([n, x], sum_(K(Nat, x), n) == mul(real(n), x)), 
                  by=[sum_const_base, sum_const_induct,
                      induct(lambda n: ForAll([x], sum_(K(Nat, x), n) == mul(real(n),x)))])


```

    proved
    proved
    proved

And finally $\sum n = n*(n-1)/2$

```python
#sum_const_induct
#induct(lambda n: ForAll([x], sum_(K(Nat, x), n) == mul(real(n),x)))
#lemma(sum_const, by=[sum_const])

id_ = Lambda([n], real(n))
# helper function. We could perhaps have4 lambdified the sympy result?
nn1 = lambda n: mul(real(n) - 1, real(n)) / 2 

sum_n_base = lemma(ForAll([n], sum_(id_, Nat.zero) == nn1(Nat.zero)), by=[sum_def, plus_def, mul_def, real_def])
sum_n_induct = lemma(ForAll([n], Implies(sum_(id_, n) == nn1(n), 
                                        sum_(id_, Nat.succ(n)) == nn1(Nat.succ(n)))),            
                     by=[sum_def, plus_def, mul_def, real_def])

sum_n = lemma(ForAll([n], sum_(id_, n) == nn1(n)), by=[sum_n_base, sum_n_induct, induct(lambda n: sum_(id_, n) == nn1(n))])
```

    proved
    proved
    proved

## 1/n -> 0

Okay, now let's try something that is headed towards analysis.

The above is highly computable and constructive and finite which is nice. Analysis needs to touch infinity in various ways.

The standard definition of a sequence converging to some value is that there is some big N for any accuracy $\epsilon$ you want such that the sequence past N stays inside $\epsilon$ of the convergent value. <https://en.wikipedia.org/wiki/Limit_of_a_sequence>
$\forall \epsilon,  \exists N, \forall n, n \ge N \rightarrow |x_n - x| < \epsilon$

This definition should probably be skolemized and in general I think working directly with the skolemized for is advisable. Skolemizing in this case mean directly talking about $N(\epsilon)$ as a function of epsilon. This is useful info computationally and practically as this function computes exactly how many terms to evaluate if you want some particular accuracy.

I initially tried to do this and realized I was missing some kind of axiomatic feature of the reals. Something like the Archimedean property <https://en.wikipedia.org/wiki/Archimedean_property> . Indeed, the wikipedia article mentions that the property is related to or the same as proving 1/n converges.

```python
# skolemized looks something like this
eps = Real('eps')
N = Const('N', ArraySort(RealSort(), Nat))
converge_zero = Function("converge_zero", Seq, ArraySort(R, Nat), BoolSort())
converge_zero_def = ForAll([s, N], converge_zero(s, N) == ForAll([eps, n], Implies(real(n) >= real(N[eps]), s[n] < eps)))
```

```python
# gibbering about definitions. I dunno. Skip this.
conv_to = Function("conv_to", Seq, R, B)
eps = Real('eps')
N = Const("N", Nat)

abs = Function("abs", R, R)
abs_def = ForAll([x], abs(x) == If(x >= 0, x, -x))

conv_to_def = ForAll([s, x], conv_to(s, x) == ForAll([eps], Exists([N], ForAll([n], Implies(real(n) >= real(N), abs(s[n] - x) < eps)))))

converges = Function("converges", Seq, B)
converges_def = ForAll([s], converges(s) == Exists([x], conv_to(s, x)))

# limit is partial function. We can only prove it equals something interesting if the sequence converges
# It's kind of the skolemized piece of  converges
lim = Function("lim", Seq, R)
lim_def = ForAll([s], Implies(converges(s), conv_to(s, lim(s))))

# does not go through. Back to the drawing board
recip_converge = lemma(conv_to(Lambda([n], 1/(1 + real(n))), 0), by=[conv_to_def, real_def], admit=True)

# constructing the appropriate N(eps) is annoying
#abs(Lambda([n], 1/(1 + real(n)))   
#round_up = Function("round_up", R, Nat)
#round_up_def = ForAll([x], round_up(x) == If(x <= 0, 1, Nat.pred(round_up(x))), Nat.zero))
```

    Admitted!! conv_to(Lambda(n, 1/(1 + real(n))), 0)

To construct this `N` function, I need a way of taking the $\epsilon \in R$ and turn it into a `Nat`, but I have defined nothing that takes a real into a Nat yet.

The ceiling and floor functions are natural candidates. There are slightly different variations of this to attempt

- `ceil` is nice because the ceil of negative numbers should just be 0
- floor is nice because `x == floor(x) + frac(x)` and I like equations

It also became apparent that I needed more properties and my `real` function and that defining an `le` $\le$ relation on Nat might be useful.

`ceil` here is the first thing that I defined not based on obvious structural recursion. It is a good definition though. I'm not sure how I would dignify it if I were trying to dignify my definitions or automatically discharge their well formedness.

```python

ceil = Function("ceil", R, Nat)
ceil_def = ForAll([x], ceil(x) == If(x <= 0, Nat.zero, Nat.succ(ceil(x-1))))

real_zero = lemma(real(Nat.zero) == 0, by=[real_def])
ceil_real_base = lemma(ceil(real(Nat.zero)) == Nat.zero, by=[ceil_def, real_zero])
ceil_real_induct = lemma(ForAll([n], Implies(ceil(real(n)) == n, ceil(real(Nat.succ(n))) == Nat.succ(n))),
                          by=[real_def, ceil_def, plus_def])
ceil_real = lemma(ForAll([n], ceil(real(n)) == n), by=[real_def, ceil_def, plus_def, induct(lambda n: ceil(real(n)) == n)])


le = Function("le", Nat, Nat, B)
le_def = ForAll([n, m], le(n, m) == If(Nat.is_zero(n), True, If(Nat.is_zero(m), False, le(Nat.pred(n), Nat.pred(m)))))

le_refl_base = lemma(le(Nat.zero, Nat.zero), by=[le_def])
le_refl_induct = lemma(ForAll([n], Implies(le(n, n), le(Nat.succ(n), Nat.succ(n)))), by=[le_def])
le_refl = lemma(ForAll([n], le(n, n)), by=[le_refl_base, le_refl_induct, induct(lambda n: le(n, n))])

le_succ = lemma(ForAll([n,m], le(n, m) == le(Nat.succ(n), Nat.succ(m))), 
                by=[le_def, induct(lambda n: le(n, m) == le(Nat.succ(n), Nat.succ(m)))])


real_non_neg_base = lemma(real(Nat.zero) >= 0, by=[real_zero])
real_non_neg_induct = lemma(ForAll([n], Implies(real(n) >= 0, real(Nat.succ(n)) >= 0)), by=[real_def, plus_def])
real_non_neg = lemma(ForAll([n], 0 <= real(n)), by=[real_non_neg_base, real_non_neg_induct, induct(lambda n: real(n) >= 0)])


_1 = lemma(real(Nat.zero) == 0, by=[real_def])
real_le_base = lemma(ForAll([m], real(Nat.zero) <= real(m)), by=[_1, real_def, real_non_neg])
#real_le_induct = lemma(ForAll([n,m], Implies(Implies(le(n,m), real(n) <= real(m)), 
#                                             Implies(le(Nat.succ(n), m), real(Nat.succ(n)) <= real(m)))),
#                        by=[real_def, le_def, plus_def])
#real_le_base = lemma(ForAll([m], Implies(le(Nat.zero, m), real(Nat.zero) <= real(m))), by=[le_def, real_def, plus_def, real_non_neg])
#real_le_base = lemma(ForAll([n], le(Nat.zero, Nat.succ(n))), by=[le_def])

# uhh, I think I can get this, but I need to do some double induction or something.
real_le = lemma(ForAll([n,m], le(n,m) == (real(n) <= real(m))),
                 by=[real_def, le_def, plus_def, induct(lambda n: Implies(le(n,m), real(n) <= real(m)))], admit=True) 


# hmm. This is probably not true, x = -1, n = 0
#ceil_galois = lemma(le(ceil(x), n) == (x <= real(n))


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
    Admitted!! ForAll([n, m], le(n, m) == (real(n) <= real(m)))

```python
## N = ceil(1/eps) => n > N => 1/real(n) < eps
# x <= real(ceil(x))

#real_ceil = lemma(ForAll([x], x <= real(ceil(x))), by=[real_def, ceil_def, plus_def])
# x <= real(If(x <= 0, 0, Nat.succ(real(x-1))))
real_ceil_neg = lemma(ForAll([x], Implies(x <= 0, x <= real(ceil(x)))), by=[real_def, ceil_def, plus_def])

# x <= real(Nat.succ(ceil(x-1)))) == x <= 1 + real(ceil(x-1)) ==
#real_ceil_pos = lemma(ForAll([x], Implies(x > 0, x <= real(ceil(x))), by=[real_def, ceil_def, plus_def, real_non_neg]))

# I'm pretty puzzled what principle is gonna let me do this. real induction? Some roundabout use of regular induction?
# I really do need something akin to this as an axiom.
# what above making an intermeidate equality anmd inducting over that? "Elimination with A Motive" mentions a similar trick. Interesting
ilemma = induct(lambda n: ForAll([x], Implies(n == ceil(x), x <= real(n))))
real_ceil = lemma(ForAll([x], x <= real(ceil(x))), by=[real_def, ceil_def, plus_def, ilemma])


```

    proved
    proved

Ok, so now we take it step by step. Some little experiements to be sure I can prove stuff about the ceiling of `1/eps`

```python
eps = Real('eps')

eps_ceil_pos = lemma(ForAll([eps], Implies(eps > 0, Not(Nat.is_zero(ceil(eps))))), by=[ceil_def])
nonzero_real_pos = lemma(ForAll([n], Implies(Not(Nat.is_zero(n)), real(n) > 0)),  by=[real_def, plus_def, real_non_neg])

epsrecip = lemma(ForAll([eps], Implies(eps > 0, 1/eps <= real(ceil(1/eps)))), by=[real_ceil])

lemma(ForAll([eps], Implies(eps > 0, 1/real(ceil(1/eps)) <= eps)), by=[epsrecip])
```

It turns out with the lemma real_ceil, it didn't actually need much help, which is a bit surprising.

```python
_1 = lemma(ForAll([eps], Implies(eps > 0, 1/(1 + real(ceil(1/eps))) < eps)), by=[real_ceil]) # so really it didn't need much help
```

So here is the skolemized form of the theorem

```python

recip_n = lemma(ForAll([eps,n], Implies(And(le(ceil(1/eps), n), eps > 0), 1/(1 + real(n)) < eps)), by=[real_ceil, real_le])
recip_n
```

Then with some ministrations, I can massage it to prove the unskolemized form. This needs a lot of hand holding though.

```python
N = Const('N', Nat)

# make a temporary function to abstract the things i don't want z3 to see.
temp = Function("temp", R, Nat, Nat, B)
temp_def = ForAll([eps, N, n], temp(eps, N, n) == Implies(And(le(N, n), eps > 0), 1/(1 + real(n)) < eps))

# We can make a temporary definition to make the pattern more obvious. (It is tough on the eye, but also it's tough on z3's pattern matcher I guess)
# This is also why I suggest working in skolemized form in any case.
_1 = lemma(ForAll([eps, n], temp(eps, ceil(1/eps), n)), by=[temp_def, recip_n])
_2 = lemma(ForAll([eps], Exists([N], ForAll([n], temp(eps, N, n)))), by=[_1])
recip_n2 = lemma(ForAll([eps], Exists([N], ForAll([n], Implies(And(le(N, n), eps > 0), 1/(1 + real(n)) < eps)))), by=[_2, temp_def])

```

    proved
    proved
    proved

# Bits and Bobbles

The "proof" above is obviously meandering. I think it can be cleaned up significantly. I just am trying to avoid building out piles of under theorems.

There is some reason to believe that the Hyperreals make some of this easier.

```python



real_ceil = lemma(ForAll([x], x <= real(ceil(x))), by=[real_def, ceil_def, plus_def, ilemma], admit=False)

```

    proved

Archimedean property
x = real(floor(x)) + frac(x)
Eudoxus reals?

We expect it to often be the case that sympy closed forms will be confirmable via a rote induction procedure.

```python



abs_neg_x = lemma(ForAll([x], abs(-x) == abs(x)), by=[abs_def])
abs_pos = lemma(ForAll([x], abs(x) >= 0), by=[abs_def])

dist = Function("dist", R, R, R)
dist_def = ForAll([x, y], dist(x, y) == abs(x - y))

dist_refl = lemma(ForAll([x], dist(x, x) == 0), by=[dist_def, abs_def])
dist_post = lemma(ForAll([x, y], dist(x, y) >= 0), by=[dist_def, abs_pos])
dist_symm = lemma(ForAll([x, y], dist(x, y) == dist(y, x)), by=[dist_def, abs_def])
dist_tri = lemma(ForAll([x, y, z], dist(x, z) <= plus(dist(x, y), dist(y, z))), by=[dist_def, plus_def, abs_def])

```

    proved
    proved
    proved
    proved
    proved
    proved

We can't talk about converges to if we can't talk about arbitrary reals first, because there's nothing to converge to. So the idea of a cauchy sequence is to say if some sequence seems to be self consistent, it has some number it converges to.
In this way real numbers can be constructed out of the notion of a cauchy sequence without saying exactly what the thing it converges to is.

```python
# https://en.wikipedia.org/wiki/Cauchy_sequence
cauchy = Function("cauchy", Seq, B)
eps = Real('eps')
N = Const("N", Nat)
cauchy_def = ForAll([s], cauchy(s) == 
                    ForAll([eps], Exists([N], ForAll([n, m], Implies(And(n >= N, m >= N), abs(s[n] - s[m]) < eps)))))


```

      Cell In[138], line 5
        ForAll([eps], Exists([N], ForAll([n, m], Implies(And(n >= N, m >= N), abs(sum_(s, n) - sum_(s, m)) < eps))))
                                                                                                                    ^
    SyntaxError: incomplete input

```python
# properties of sequences. Monotonic sequences and bounded sequences.
mono = Function("mono", Seq, B)
mono_def = ForAll([s], mono(s) == ForAll([n], s[n] <= s[Nat.succ(n)]))

bounded = Function("bounded", Seq, B)
bounded_def = ForAll([s], bounded(s) == Exists([y], ForAll([n], s[n] <= y)))
```

Bottling up the pattern of induction that I've been doing manually above into a tactic.

```python
def induct_tac(P, by=[]):
    base = lemma(P(Nat.zero), by=by)
    step = lemma(ForAll([n], Implies(P(n), P(Nat.succ(n)))), by=by
    induct_ax = induct(P)
    x = FreshCons(Nat)
    th = ForAll([x], P(x))
    return lemma(th, by=[base,step,induct_ax])


# alternative style with open x
def induct_tac(x, P, by=[]):
    base = lemma(substitute(P, (x, Nat.zero)), by=[])
    step = lemma(ForAll([x], Implies(P, substitute(P, (x, Nat.succ(x))))),
                 by=by)
    theorem = ForAll([x], P)
    return theorem

```

Cody's is_pos is really interesting
I could model second order concepts via schema. Anything that needs a universal out front of a second order thing, replace with python metatheory lambda for schema.

Transitive clousre
def min(f):
    Implies(f(a,b), trans_close(a,b))

Refinement type eliminators
ex x : A, P x

(forall x : A, P x -> f x (P x)) -> forall y, f y

Woah. Maybe I should be using cvc5
<https://cvc5.github.io/docs/cvc5-1.0.2/theories/transcendentals.html>

could also swap in dreal

```python
# cody's variation
def prove(f):
    s = Solver()
    s.add(Not(f))
    if s.check() == unsat:
        print ("proved")
    else:
        print ("failed to prove")
        print ("countermodel:" + str(s.model()))

# I think this should be called pos_sufficient
def is_pos(f, x):
    return Implies(ForAll(x, Implies(x >= 0, f)), ForAll([x], f))

#def is_pos(f, x):
#    return Implies(f, x >= 0)

def by_induction(f, x):
    pos = is_pos(f, x)
    zero = substitute(f, (x, IntVal(0)))
    succ = Implies(f, substitute(f, (x, x+1)))
    print("is positive:")
    prove(pos)
    print("zero case:")
    prove(zero)
    print("successor case:")
    prove(succ)

f = Function('sum', IntSort(), IntSort())

f_ax0 = ForAll(x, Implies(x <= 0, f(x) == 0))
f_ax1 = ForAll(x, Implies(x > 0, f(x) == f(x - 1) + x))

def f_test(x):
    if x <= 0:
        return 0
    else:
        return f_test(x - 1) + x

x = Int('x')
my_property = Implies(And(f_ax0, f_ax1), Implies(x >= 0, f(x) == x * (x + 1) / 2))
prove(my_property)
by_induction(my_property, x)
```

RNat = Function("Nat", R, Bool) # Nat as a predictae on R
RNat(x) == (real(ceil(x)) == x) # In terms of previous stuff.

RNat is the least set that contains 0 and RNat(x) => RNat(x+1)

Direct rnat induction

----------------------------------
ForAll([x], Implies(RNat(x), P(x))

Real induction. If it is uniform real induction, we can push out a ball for an epsilon that does not depend on the size of the ball.
P(B) /\ exists eps, forall B, P(B) -> P(B+eps)
--------------------------------------

      forall x, P(x) 

This is sort of like the reverse of a monotonic convergence. It's a monotonic divergence.

Logical integration. if prod P(x)dx = e^{int ln(P(x))dx} = 1,

The issue with real induction where you can push the ball out a decreasing amoutn is similar to the concerns that led cantor to invent the orindals in the first place.

It's also like finite escape vs asymptitotic escape/ lyapunov coefficients.

Graham says Freyd reals. <https://math.stackexchange.com/questions/4727657/freyds-algebraic-real-analysis-scale-and-linear-order> <http://www.tac.mta.ca/tac/volumes/20/10/20-10abs.html>
 A double pointed set with gluing? Kind of like an interval definition

Hamkins - The problem is the prefixes aren't determined by prefixes

```python
# modelling a number as a stream 1/2 +- 1/4 +- 1/8 + 1/16
def add(a,b):
    carry = 0
    for da, db in zip(a,b):
        



```

```python
I = Datatype("Interval")
I.
```

```python
RFun = ArraySort(R,R)
cont = Function(RFun, B)

cont_def = ForAll([f], cont(f) == ForAll([eps], Exists([N], ForAll([n], Implies(n >= N, abs(f(n) - f(0)) < eps)))))

```

```python
# RecFunction allows us to use z3 as a simplifier.

#sum__ = RecFunction("sum", Seq, Nat, R)
#RecAddDefinition(sum__, [s, n], If(n == Nat.zero, 0, plus(s[Nat.pred(n)], sum__(s, Nat.pred(n)))))
#simplify(sum__(Lambda([n], If(Nat.is_zero(n), RealVal(0), RealVal(1))), Nat.succ(Nat.zero)))

#sum_id = RecFunction("sum_id", Seq, Nat, R)
#RecAddDefinition(sum_id, [n], If(n == Nat.zero, 0, plus(s[Nat.pred(n)], sum__(s, Nat.pred(n)))))
#simplify(sum__(Lambda([n], If(Nat.is_zero(n), RealVal(0), RealVal(1))), Nat.succ(Nat.zero)))

real_ = RecFunction("real", Nat, R)
RecAddDefinition(real_, [n], If(Nat.is_zero(n), 0, 1 + real_(Nat.pred(n))))
print(simplify(real_(Nat.succ(Nat.succ(Nat.zero)))))
simplify(real_(Nat.succ(Nat.succ(n))))

```

    2

real(succ(succ(n)))

Nets. Sequences are perhaps arbitrary,

Filters. Havibng a domain at all is perhaps arbitrary

Math comp analyses and zach was all about filters.

<https://www.sciencedirect.com/science/article/abs/pii/0004370272900410> computer assisted limit theorems 9172 bledsoe

<https://link.springer.com/article/10.1023/A:1005843328643>  The Heine–Borel Challenge Problem. In Honor of Woody Bledsoe

Bledsoe, W.: Challenge problems in elementary analysis, Journal of Automated Reasoning 6 (1990),

Bledsoe, W. W.: Heine–Borel Theorem Analogy Example, Technical Report Memo ATP 124, University of Texas Computer Science Dept., Austin, TX, 1994.

<https://citeseerx.ist.psu.edu/document?repid=rep1&type=pdf&doi=70050293723ef74d0747323be1cd06eabe5ebbc5> Non resolution theorem proving

Ballantyne, M. and Bennett, W., Graphing methods for topological proofs, The University of
Texas at Austin Math. Dept. Memo ATP-7 (1973).

5. Ballantyne, A. M. and Bledsoe, W. W., Automatic proofs of theorems in analysis using nonstandard techniques, The University of Texas at Austin Math. Dept. Memo ATP-23 (July
1975); J. ACM, to appear, July 1977. -

A. Michael Ballantyne: The Metatheorist: Automatic Proofs of Theorems in Analysis Using Non-Standard Techniques, Part II.

Analogical theorem proving. A predecssor of proof patching

Kolbe, Th. and Walther, Ch.: Patching proofs for reuse, in N. Lavrac and S. Wrobel (eds), Proceedings of the 8th European Conference on Machine Learning 1995, Kreta, 1995.

Analogy for Automated Reasoning  -book 1990

<https://plato.stanford.edu/entries/reasoning-analogy/>

A Bundy - inductive proof plans? Author on the handbook chapter

```python
%%file /tmp/induct.smt2
(declare-sort Nat 0)
(declare-fun sum ((Array Nat Real) Nat) Real)
(declare-fun real (Nat) Real)
(declare-fun plus (Real Real) Real)
(declare-fun mul (Real Real) Real)
(assert (let ((a!1 (forall ((x Real))
             (= (sum ((as const (Array Nat Real)) x) zero) 0.0)))
      (a!2 (forall ((n Nat))
             (let ((a!1 (forall ((x Real))
                          (= (sum ((as const (Array Nat Real)) x) n)
                             (mul (real n) x))))
                   (a!2 (forall ((x Real))
                          (= (sum ((as const (Array Nat Real)) x) (succ n))
                             (mul (real (succ n)) x)))))
               (=> a!1 a!2))))
      (a!3 (forall ((x Real))
             (= (sum ((as const (Array Nat Real)) x) zero) (mul (real zero) x))))
      (a!4 (forall ((n Nat))
             (forall ((x Real))
               (= (sum ((as const (Array Nat Real)) x) n) (mul (real n) x)))))
      (a!5 (forall ((x Real) (n Nat))
             (= (sum ((as const (Array Nat Real)) x) n) (mul (real n) x)))))
  (=> (and a!1 a!2 (=> (and a!3 a!2) a!4)) a!5)))

(check-sat)
```

    Overwriting /tmp/induct.smt2

```python
! vampire /tmp/induct.smt2
```

    % Running in auto input_syntax mode. Trying SMTLIB2
    % Failed with
    % User error: Compound functor expected to be a rankend function (starting with '_'). Instead read: (as const (Array Nat Real))
    % Trying TPTP
    Parsing Error on line 1: cnf(), fof(), vampire() or include() expected at position 0 (text: ()

```python

```
