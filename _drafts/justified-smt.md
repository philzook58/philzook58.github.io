
Something I like about datalog and ASP is that their every result is justified.
The models output by an smt or sat solver are kind of more random.

This is related to the idea that you can't in general express the transitive closure of a relation in first order logic. "Whhhaaaaa?" you say. I agree. It feels odd.

Doesn't this work?
`forall x y z, R(x,y) & Rstar(y,z) => Rstar(x,z)`
`forall x y, R(x,y) => Rstar(x,y)`

No, because these axioms actually don't precisely constrain `Rstar` to precisely the transitive closure. They constraint `Rstar` to be _at least_ the transitive closure, which is a little different. For example, `[R(x,y) = false, Rstar(x,y) = true]` is a model of these axioms.

Okay, well what about if we try and make the thing bidirectional.

`forall x,y,z Rstar(x,z) <=> R(x,y) & Rstar(y,z) | R(x,z)` This is a little better. However, it doesn't account for self consistent / non well founded loops in the model.
Consider `[R(1,2) = true,  Rstar(1,2) = true, Rstar(2,1) = true]`. This is a tiny 2 vertex loop. It is a model of the above axioms, but still `Rstar` is not the transitive closure of R.

There are some doges for this problem. If R is for serious a particular finite relation, I can precompute the transitive clousure and just write that to constraint Rstar. Or more generally, if R is of bounded size, I could precompute all transitive closures or break all possible loops with axioms.

Answer Set programming could be called ["justified smt"](https://www.weaselhat.com/2022/11/07/asp/).  
However, Z3 does have a notion of well foundedness/least fixed point, that of Algebraic data types.

Another notion of least comes from using the optimization capabilities of z3. If we try to minimize the number of places `Rstar` is true, we'll get the minimal model and only get the pieces that are _forced_ to be true by the axioms. This is the transitive closure.

_Also_, z3 has the notion of transitive closure built in a as special relation.

I realized this trying to use Z3's egraph in a justified way in which it produces the minimal model. The same problem happens. If I say `a = b /\ b = c /\ d = e` what I want `=` to do is be exactly the symmetric transitive clousure of the axioms I said. It is not however, instead collapsing into a single object in the model `[a = V1, b = V1, c = V1, d = V1, e = V1]` is valid.

Another way of viewing `=` is trying to talk about connectivity in an undirected graph. The "proof" of two things being connected is a path between them that starts on one vertex and ends on the other.

Internalizing proofs as objects is quite a fun brain tickling idea. It is an old one too. We are playing godelian games.

Here's another example: parsing. Parsing as deduction. The existence of the parse tree itself is a proof that such and such a string does parse / belongs to the CFG defined set of strings. <https://lexi-lambda.github.io/blog/2019/11/05/parse-don-t-validate/> . Indeed,  parse trees make invalid strings unrepresentable.

Hmm. The well foundedness of strings themselves might save me here.

```python
from z3 import *
sexp = Function("sexp", StringSort(), BoolSort())
s.add(ForAll([s], 
    sexp(s) == Or(s == "()", And(s[0] == "(", sexp(s[1:-1]), s[-1] == ")"))))

```
