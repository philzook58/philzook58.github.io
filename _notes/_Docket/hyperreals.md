
Goldblatt

Compactness is important here? Huh.

Adding

Trying to make infinitesimals rigorous

Rings can have things like eps^2 = 0 by taking quotient rings.
Something with R as a subfield.

Constructing a model of hyperreals. Infinite sequences of reals. Quotient by equivlanec e relation of agreeing on cofinite set.

A finite list of disagreement points

```
equiv(a,b,l) = forall n, a[n] = b[n] | n in l 
```

More equational than classical presentation?

R is unique complete ordered field. So R*

Transfer principle

Ultrafilter.
Ultrafilter as a notion of truth. Relation to topos? Modal logic? Intuitionstic logic?

Ultrapower.

Internal set theory

Adding a "standard" predicate to set theory. There is a notion of standard elements vs nonstandard elements.
This has a connection to standard models of constructions like the reals or naturals, which by the weakness of power of description of first order logic, the axims often allow other models besides the standard one.

This has some flavor of the method of "junk" elements used to model partial functions using total functions as I've played around with in category theory.

Nonstandard elements are hard to grasp because whenever you get concrete hold f somthing, it tends (is always?) standard.

I think I've seen it mentioned that maybe "standard" is somehow talking about a fluid boundary of described or construct elements. If I keep around an eps smaller than any number I've considered so far, and maybe go back and fix it up as I go should I ever bring in anything smaller? I do kind of feel like an approximate equality of finite difference is sufficient

Nonstandard models of peano <https://en.wikipedia.org/wiki/Non-standard_model_of_arithmetic>
We can keep adding x > n for any n to the axiom set and stay consistent. The forall n is in the metalogic. By compactness, we can add the forall n into the object logic and stay consistet?

Hypernaturals - a construction of the hypernatural is sequences of naturals identified under a ultrafilter (a "large set"). It's weird that allowing just a little disagreement helps

HyperRationals

Naive Infinitesimals
The reals are a subfield of the hyperreals.
There exist infinittesimals which are smaller than

The "standard" function behaves like a kind of rounding.

Distincting between equality and approximation equality.
a ~ b == st(a) = st(b)

st pushes through regular operations (+, -, ...). So it is a homomorphsim of sorts.
st(eps) = 0

lim = x ~ c /\ x != c -> lim(t(x)) = t(c)
continuity is x ~ y -> f(x) ~ f(y)

# Eudoxus Reals

One can imagine nearly linear functions. `f(x) = Ax + r(x)` where the remainder `r(x)` is small in some sense. This is a linear approximation done all the time as an expansion. Asymptotically, if r(x) stays bounded, it matters realtively less and less. If there was some cutoff of size in the universe of numbers, some quantum, it doesn't matter.

In the proof of the irrationality of sqrt 2, one has to somehow refer to "irrationality" and "sqrt 2". To posit sqrt 2 as an enttity means you've already defined the reals. "irrationality" naively means you've already defined the rationals.

To cut the knot, you can define the question as the diophantine equation `2n^2 = m^2` does not have natural solutions. We've mangled the statement of the theorem to smething recognizable. So we've done some metalevel reasoning. This is problematic.

Likewise, there is a way to discuss reals without talking about rationals. IN the Bishop book, a constructive real is a sequence that is converging faster than 1/n more or less. `|f(i) - f(j)| <= 1/i + 1/j`. Multiplying out, `i(f(j)) - f(i)j <= 2(i + j)`

Stern Brocot trees and diophantine approximation?
