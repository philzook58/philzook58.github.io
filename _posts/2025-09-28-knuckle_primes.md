---
title: Proving Infinitude of Primes in Knuckledragger
date: 2025-09-28
---

Cody challenged me to prove that there are an infinitely many primes in Knuckledragger, saying it's the minimum thing to do to demonstrate you have a proof assistant. <https://en.wikipedia.org/wiki/Euclid%27s_theorem> It's one of the older proofs out there, appearing famously in Euclid's elements. This is number 11 in the formalizing 100 theorems list <https://www.cs.ru.nl/~freek/100/> . Maybe it'd be fun to start chasing down the other easy ones and copy them out of Isabelle or whatever

By staying very close to the isabelle proof <https://isabelle.in.tum.de/dist/library/HOL/HOL-Computational_Algebra/Primes.html> , it took me about 3-4 hours to do this, some of which was at a groggy 11pm. I went top down through this proof to see the basic definitions and lemmas I needed on demand.

# Prime

First I need to define what it means to be prime.

```python
from kdrag.all import *
import kdrag.theories.int as int_
n,m,p,q,k = kd.FreshVars('n m p q k', smt.IntSort())
x,y,z = smt.Ints('x y z')
prime = kd.define("prime", [n], smt.And(n > 1, smt.Not(smt.Exists([p,q], smt.And(p > 1, q > 1, n == p * q)))))

```

&#x22A8;Not(prime(4))

As a nice sanity check, z3 can infer whether some small numbers are prime. I'm pleasantly surprised by this. The `unfold` keyword argument unfolds the definition of `prime` before handing it off to z3. Without using unfolding, `prime` is just some opaque predicate for which z3 can find arbitrary models of.

```python
kd.prove(prime(2), unfold=1)
kd.prove(prime(3), unfold=1)
kd.prove(smt.Not(prime(4)), unfold=1)
```

```python
l = kd.Lemma(prime(2))
l.unfold(prime)
l.split()
l.auto()
l.intros()
#l.split(at=0)
p,q = l.einstan(0)
l.split(at=0)
l.have(p <= 2)
l.have(q <= 2)
# Prove by computation?
# Proving any particular number is prime can be hard, see RSA.

```

    [p!37, q!38];
    [p!37 > 1, q!38 > 1, 2 == p!37*q!38, p!37 <= 2, q!38 <= 2] ?|= False

Some lemmas basically unpacking the definition. These are very obvious and easy, but only because z3 provides an excellent baseline of automation. If knuckledragger did not have z3 in it's kernel, getting even these simple things would require a lot more work.

```python
prime_nat = kd.prove(smt.Implies(prime(n), n >= 0), by=prime.defn(n)).forall([n])
prime_nat

prime_gt_1 = kd.prove(smt.Implies(prime(n), n > 1), by=prime.defn(n)).forall([n])
prime_gt_1
```

&#x22A8;ForAll(n!24, Implies(prime(n!24), n!24 > 1))

# Divisibility

We also define a divisibility relation.

```python
dvd = kd.define("dvd", [n, m], smt.Exists([p], m == n * p))
```

```python
dvd_imp_le = kd.prove(smt.Implies(smt.And(dvd(k, n), k >= 0, n > 0), k <= n), unfold=1).forall([k,n])
dvd_imp_le
```

&#x22A8;ForAll([k!28, n!24],
       Implies(And(dvd(k!28, n!24), k!28 >= 0, n!24 > 0),
               k!28 <= n!24))

A more complex relationship between `prime` and `dvd`. Ultimately fair simple though. You can see from my commented out stuff that I often do a bunch of work only to realize maybe I was missing some hypothesis or could have called `auto` earlier with the right lemmas.

```python
l = kd.Lemma(smt.Implies(n >= 0, prime(n) == smt.And(1 < n, kd.QForAll([m], m >= 0, dvd(m,n), smt.Or(m == 1, m == n)))))
l.intros()
l.split()

# The order is swapped from what I expected
# <--
l.auto(unfold=1) # This solve is unstable.
# -->
l.unfold(prime, dvd)
l.auto()
prime_nat_iff = l.qed()
prime_nat_iff
#l.intros()
#l.split()
#l.auto(unfold=1)
#l.auto()
#_m = l.fix()
#l.intros()
#l.split(at=1)
#l.split(at=3)
#l.auto()
#l.qed()
#_p = l.einstan(2)
#l.split(at=0)
#l.auto()
```

&#x22A8;Implies(n!24 >= 0,
        prime(n!24) ==
        And(n!24 > 1,
            ForAll(m!25,
                   Implies(And(m!25 >= 0, dvd(m!25, n!24)),
                           Or(m!25 == 1, m!25 == n!24)))))

A useful lemma about the interplay of divisibility and difference. Here we see `einstan` which creates a fresh skolem constant for an `Exists` in the context. This gives us a way to spell out to z3 exactly what term dignifies the `Exists in the goal.

```python
l = kd.Lemma(smt.Implies(smt.And(dvd(k, n), dvd(k, m), n >= 0, k >= 0, m >= 0), dvd(k, m - n))) # TODO: rearrange nat constraints to come first
l.unfold(dvd)
l.intros()
l.split(at=0)
_p1 = l.einstan(0)
_p2 = l.einstan(1)
l.exists(_p2 - _p1)
l.auto()
dvd_diff_nat = l.qed().forall([k,n,m])
dvd_diff_nat
```

&#x22A8;ForAll([k!28, n!24, m!25],
       Implies(And(dvd(k!28, n!24),
                   dvd(k!28, m!25),
                   n!24 >= 0,
                   k!28 >= 0,
                   m!25 >= 0),
               dvd(k!28, m!25 - n!24)))

# Factorial

Defining factorial and proving properties of.

People familiar with theorem proving may raise eyebrows at this definition. I don't currently have good recursive definition schema / termination checking (I do have primitive recursion schema for datatypes, but nothing for Int). `define` is a pretty open blade and requires as much care as `axiom`.

```python
fact = smt.Function("fact", smt.IntSort(), smt.IntSort())
fact = kd.define("fact", [n], smt.If(n <= 0, 1, n * fact(n - 1)))
```

A basic inductive fact. Induction here is double ended induction for the Ints.

```python
l = kd.Lemma(fact(n) >= 1)
l.induct(n)
l.unfold(fact)
l.auto()
l.auto(unfold=1)
_n = l.fix()
l.intros()
l.simp()
l.unfold(fact)
l.simp()
l.auto()
fact_ge_1 = l.qed().forall([n])

fact_ge_1
```

&#x22A8;ForAll(n!24, fact(n!24) >= 1)

I'm a little worried about this one. It went through suspiciously easily. I probably did not need strong induction.

```python
l = kd.Lemma(smt.Implies(n > 1, kd.QExists([p], prime(p), dvd(p, n))))
l.intros()
l.cases(prime(n))
# n is not prime
l.unfold(prime, at=1)
l.have(smt.Exists([p,q], smt.And(p > 1, q > 1, n == p * q)))
l.clear(1)
_p, _q = l.einstan(1)
l.induct(n, int_.induct_nat_strong)
#_n1 = l.fix()
#l.intros()
#print(l)
l.auto()
# n is prime
l.auto(unfold=1)
prime_factor_nat = l.qed().forall([n])
prime_factor_nat
```

&#x22A8;ForAll(n!24,
       Implies(n!24 > 1,
               Exists(p!37,
                      And(prime(p!37), dvd(p!37, n!24)))))

An interesting theorem, that every nat small than n divides `fact(n)`

```python
# dvd_fact
m = kd.FreshVar("m", smt.IntSort())
l = kd.Lemma(smt.Implies(smt.And(1 <= m, m <= n), dvd(m, fact(n))))
#l.intros()
l.induct(n)
#_n = l.fix()
l.auto()
l.auto(by=[fact.defn(smt.IntVal(0))])
l.unfold(dvd)
_n = l.fix()
l.intros()
l.unfold(fact)
l.simp()
l.intros()
l.simp(at=0)
#l.right()
#l.simp(at=0)
#l.have(smt.Exists([p], fact(_n) == m * p))
#l.newgoal(l.top_goal().goal)
#print(_n, p, m)
l.cases(m == 1 + _n)
# case m != 1 + _n
l.have(smt.Exists([p], fact(_n) == m * p))
_p = l.einstan(3)
# l.rewrite(3) # this shouldn't have failed.
l.exists(_p * (1 + _n))
l.auto()
# case m == 1 + _n
l.auto()
dvd_fact = l.qed().forall([m, n])
dvd_fact
```

&#x22A8;ForAll([m!216, n!24],
       Implies(And(m!216 >= 1, m!216 <= n!24),
               dvd(m!216, fact(n!24))))

# Putting it together

Now to actually follow the body of the proof from Isabelle

Not sure why I actually needed this next one.

```python
f1 = kd.prove(fact(n) + 1 != 1, by=fact_ge_1(n))
f1
```

&#x22A8;fact(n!24) + 1 != 1

Ugly ugly ugly.

```python
(pn,), tmp = kd.kernel.skolem(prime_factor_nat(fact(n) + 1)(kd.prove(fact(n) + 1 > 1, by=fact_ge_1(n))))
pn_prime = kd.prove(prime(pn), by=[tmp])
pn_dvd = kd.prove(dvd(pn, fact(n) + 1), by=[tmp])
#kd.prove(pn <= fact(n) + 1, by=[dvd_imp_le(pn, fact(n) + 1)])
#kd.prove(pn > 1, by=[pn_prime], unfold=1)
pn_nat = prime_nat(pn)(pn_prime)
#kd.kernel.unfold(pn_prime, decls=[prime])
```

```python
pn_dvd
```

&#x22A8;dvd(p!227, fact(n!24) + 1)

```python
dvd_imp_le(pn, fact(n) + 1)
```

&#x22A8;Implies(And(dvd(p!227, fact(n!24) + 1),
            p!227 >= 0,
            fact(n!24) + 1 > 0),
        p!227 <= fact(n!24) + 1)

Doing this one manually

```python
l = kd.Lemma(pn <= fact(n) + 1)
l.apply(dvd_imp_le)
l.split()
l.auto(by=[pn_dvd])
l.auto(by=[pn_nat])
l.auto(by=[fact_ge_1(n)])
l.qed()
```

&#x22A8;p!227 <= fact(n!24) + 1

But once I know the lemmas I need, it's fully automatic

```python
pn_lt_fact = kd.prove(pn <= fact(n) + 1, by=[dvd_imp_le(pn, fact(n) + 1), pn_dvd, pn_nat, fact_ge_1(n)])
pn_lt_fact
```

&#x22A8;p!227 <= fact(n!24) + 1

```python
dvd_fact(pn, n)
```

&#x22A8;Implies(And(p!227 >= 1, p!227 <= n!24),
        dvd(p!227, fact(n!24)))

```python
dvd_diff_nat(pn, fact(n), fact(n + 1))
```

&#x22A8;Implies(And(dvd(p!227, fact(n!24)),
            dvd(p!227, fact(n!24 + 1)),
            fact(n!24) >= 0,
            p!227 >= 0,
            fact(n!24 + 1) >= 0),
        dvd(p!227, fact(n!24 + 1) - fact(n!24)))

The subproof. Doing this in a proof by contradiction style seemed useful.

```python
l = kd.Lemma(smt.Implies(n >= 0, smt.Not(pn <= n)))
l.intros()
l.intros()
l.have(pn > 1, by=[pn_prime, prime_gt_1(pn)])
l.have(dvd(pn, fact(n)), by=[dvd_fact(pn, n)])
l.have(dvd(pn, fact(n) + 1), by=[pn_dvd])
l.have(dvd(pn, fact(n) + 1 - fact(n)), by=[dvd_diff_nat(pn, fact(n), fact(n) + 1), fact_ge_1(n)])
l.have(fact(n+1) == (1 + n) * fact(n), by=[fact.defn(n + 1)])
l.have(dvd(pn, 1))
l.have(pn <= 1, by=[dvd.defn(pn, smt.IntVal(1))])
l.auto()
tmp2 = l.qed()


pn_gt_n = kd.prove(smt.Implies(n >= 0, pn > n), by=[tmp2])
pn_gt_n

```

&#x22A8;Implies(n!24 >= 0, p!227 > n!24)

```python
[pn_gt_n, pn_lt_fact, pn_prime]
```

    [|= Implies(n!24 >= 0, p!227 > n!24),
     |= p!227 <= fact(n!24) + 1,
     |= prime(p!227)]

Putting all the pieces together

```python
l = kd.Lemma(smt.Implies(n >= 0, kd.QExists([p], prime(p), n < p, p <= fact(n) + 1)))
l.intros()
l.exists(pn)
l.auto(by=[pn_gt_n, pn_lt_fact, pn_prime])
next_prime_bound = l.qed()
next_prime_bound
```

&#x22A8;Implies(n!24 >= 0,
        Exists(p!37,
               And(prime(p!37),
                   n!24 < p!37,
                   p!37 <= fact(n!24) + 1)))

And then hiding the actual bound.

```python
bigger_prime = kd.prove(smt.Implies(n >= 0, kd.QExists([p], prime(p), n < p)), by=[next_prime_bound]).forall([n])
bigger_prime
```

&#x22A8;ForAll(n!24,
       Implies(n!24 >= 0,
               Exists(p!37, And(prime(p!37), n!24 < p!37))))

```python
dvd(pn, fact(n) + 1)
```

# Bits and Bobbles

<https://proofassistants.stackexchange.com/questions/1403/auto-generating-the-proof-of-infinitude-of-primes/> Some older comments about why AI could or couldn't prove infinitude of primes. Obviously, the theorem is in mathlib or isabelle, and they have tons of automation, so just finding it is cool but cheating. Havintg the isabelle and mathlib proofs in the training dataset is also cheating in some sense (mainly in the sense that it may not generalize to other similar theorem), maybe less so. I'm sure math AI companies today say that prove theorems far beyond infinitude of primes fully automatically, but I have not personally experienced this nirvana yet from an AI. It's been a mixed bag.

I don't get number theory or primes. I've tried a bit on and off through the years. I'm glad people enjoy them, but it seems both confusing and boring to me. I hope one day to find an angle on it I can appreciate. RSA yada yada yada, but also I don't really get crypto. Too far out of my wheelhouse and the advice is to not roll your own.

It is uglier, with more explicit steps. Basically I have almost no mechanisms currently to solve for existentials (many systems have some unification mechanism for this), so they need to be manually put in.

feature improvements that occurred to me

- __enter__ __exit__ on Lemma could make for nice delimiting look. Also useful for proof search though?
- How would I prove specific primes if z3 couldn't handle? euclid's algorithm. Properties of
- assert_goal()  assert_ctx() toi write out what I think the goal looks like.
- refactor commonalities
- forward mode is not bad. More Isar like combinators to increase readability?
- fix should takes names for readability
- Single lambda moves at top level were not easy. simp does too much. intros working on Or(Not(a),b) helps a little
- Lemma is so gnarly. Needs refacotring badly
- cases to open up If?
- I guess I could skolemize by allowing parameters into the fresh constants?

```python
# remove skolem from kernel
def obtain(pf : kd.Proof) -> tuple[list[smt.Expr], kd.Proof]:
    vs, lem = kd.kernel.einstan
    return vs, lem(pf)

```

```python
n = kd.FreshVar("n", smt.IntSort())
smt.Exists([p], smt.And(prime(p), p > n)) # a naive form of prime theorem.
```

```python
with kd.Lemma(smt.Implies(smt.And(dvd(k, n), dvd(k, m), n >= 0, k >= 0, m >= 0), dvd(k, m - n))) as l:
    l.unfold(dvd)
    l.intros()
    l.split(at=0)
    _p1 = l.einstan(0)
    _p2 = l.einstan(1)
    l.exists(_p2 - _p1)
    l.auto()
    dvd_diff_nat = l.qed()
    dvd_diff_nat
```

```python
l = kd.Lemma(smt.Implies(n > 1, kd.QExists([p], prime(p), dvd(p, n))))
l.intros()
l.cases(prime(n))
l.unfold(prime, at=1)
l.have(smt.Exists([p,q], smt.And(p > 1, q > 1, n == p * q)))
l.clear(1)
(_p, _q), lem = kd.kernel.einstan(smt.Exists([p,q], smt.And(p > 1, q > 1, n == p * q)))
l.have(smt.And(_p > 1, _q > 1, n == _p * _q), by=[lem])

```

```python
kd.prove(smt.Implies(smt.And(n > 1, prime(n)), kd.QExists([p], prime(p), dvd(p, n))), unfold=1)
```

```python
a,b,c = smt.Bools("a b c")
smt.Implies(a,b,c) # it just ignores c? That's terrible
def QImplies(*args):
    assert len(args) >= 1
    conc = args[-1]
    hyps = args[:-1]
    return smt.Implies(smt.And(*hyps), conc)

```

a &rArr; b

class Foward():
    def assume(self, ):
        # change the final goal and add into current context?
    def fixes():
    def

Lemma().fixes(x)
       .assumes(p1, p2, p3)
       .assumes()
       .assumes()
       .shows()
Lemma(fixes= ,
      assumes=,
      shows=)

```python
l = kd.Lemma(smt.Implies(n > 1, kd.QExists([p], prime(p), dvd(p, n))))
l.intros()
l.cases(prime(n))
# n is not prime
l.unfold(prime, at=1)
l.have(smt.Exists([p,q], smt.And(p > 1, q > 1, n == p * q)))
l.clear(1)
_p, _q = l.einstan(1)
l.induct(n, int_.induct_nat_strong)
#_n1 = l.fix()
#l.intros()
#print(l)
l.auto()
# n is prime
l.auto(unfold=1)
prime_factor_nat = l.qed().forall([n])
prime_factor_nat
```

```python
l = kd.Lemma(smt.Implies(n > 1, kd.QExists([p], prime(p), dvd(p, n))))
#l.intros()
l.cases(prime(n))
# n is not prime
#l.unfold(prime, at=0)
#l.have(smt.Exists([p,q], smt.And(p > 1, q > 1, n == p * q)))
#l.clear(1)
#_p, _q = l.einstan(1)
#l.induct(n)
#l.simp()
#_n = l.fix()
#l.intros()
#_n1 = l.fix()
#l.intros()
#print(l)
#l.auto()
# n is prime
#l.auto(unfold=1)
#prime_factor_nat = l.qed().forall([n])
#prime_factor_nat
```

    [prime(n!24) == False]
    ?|= Implies(n!24 > 1,
            Exists(p!37, And(prime(p!37), dvd(p!37, n!24))))
