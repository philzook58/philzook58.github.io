---
author: philzook58
comments: true
date: 2019-12-23 04:15:35+00:00
layout: post
link: https://www.philipzucker.com/programming-and-interactive-proving-with-z3py/
slug: programming-and-interactive-proving-with-z3py
title: Programming and Interactive Proving With Z3Py
wordpress_id: 2577
categories:
- Formal Methods
tags:
- itp
- python
- z3
---

Edit 2024: See my project knuckledragger for more systematic work in this vein <https://github.com/philzook58/knuckledragger>

I've been fiddling with z3py, figuring out some functionality and realizing some interesting things you could do with it. I think I'm at a point where it is nice to checkpoint myself with a blog post.

I'm a little surprised z3py doesn't overload the & and \| operators and some kind of implies operator for BoolRef. You can insert them later using this.

```python

from z3 import *
# useful non default operator definitions for z3 bools
BoolRef.__and__ = lambda self, rhs: And(self,rhs)
BoolRef.__or__ = lambda self, rhs: Or(self,rhs)
BoolRef.__xor__ = lambda self, rhs: Xor(self,rhs)
BoolRef.__invert__ = lambda self: Not(self)
BoolRef.__rshift__ = lambda self, rhs: Implies(self,rhs)
```

#### Functional Programming

Python is not the best functional programming environment imo. And by functional programming I implicitly mean roughly ML-like FP a la Haskell or OCaml. I don't venture much into lisp land.

The lack of good algebraic datatypes (the class syntax is so ungainly) and a type system hurts. The lack of pattern matching hurts. The `lambda` keyword is so long it makes me sad.

But you have full access to z3 from the python bindings. Z3 does have algebraic data types, and a type system. It has built in substitution mechanisms and evaluation. And it has insane search procedures and the ability to prove things. Pretty damn cool!

Unfortunately the type system is rather simplistic, being basically simply typed rather than polymorphic or something else. But using python a a schema/macro system for z3 seems a plausible way forward.

To build templated types, you can have constructor functions in python for the appropriate types.

```python

def Tuple(a,b):
    Type = Datatype('Tuple(f{(a.name(),b.name())})')
    Type.declare('pair', ('fst', a), ('snd', b))
    Type = Type.create()
    return Type
def Either(a,b):
    Type = Datatype('Either(f{(a.name(),b.name())})')
    Type.declare('left', ('getLeft', a))
    Type.declare('right', ('getRight', b))
    Type = Type.create()
    return Type 
def Maybe(a):
    Type = Datatype('Maybe(f{(a.name())})')
    Type.declare('Just', ('fromJust', a))
    Type.declare("Nothing")
    Type = Type.create()
    return Type
def List(a):
    Type = Datatype('List(f{(a.name())})')
    Type.declare('Cons', ('car', a), ('cdr', Type))
    Type.declare("Nil")
    Type = Type.create()
    return Type
''' 
Note in regards to List. Z3 has a built in type Seq that I think it has built in smarts about. You might be better off using that rather than a custom List. YMMV
'''
```

You can access the constructors from the returned types. Check this out. You get detector functions `is_Nothing` and `is_Just` , the extractor function `fromJust` and constructor functions `Nothing` and `Just`. I do a lot of `dir` exploration with z3py. It's hard to know what's available sometimes

```

# dir(Maybe(IntSort())) returns
[
'Just',
 'Nothing',
... underscore junk ... ,
 'accessor',
 'as_ast',
 'ast',
 'cast',
 'constructor',
 'ctx',
 'ctx_ref',
 'eq',
 'fromJust',
 'get_id',
 'hash',
 'is_Just',
 'is_Nothing',
 'kind',
 'name',
 'num_constructors',
 'recognizer',
 'sexpr',
 'subsort',
 'translate',
 'use_pp']
```

It's possible to build a general purpose match combinator on these types since you can introspect the number of constructors of the ADT using `num_constructors`, `constructor`, `recognizer`, and `accessor`. There might be a match inside z3py somewhere? I think it's part of the SMTLIB standard now.

```python

def match(x, **kwargs):
    t = x.sort()
    nc = t.num_constructors()
    acc = kwargs["_"] # default argument
    for c in range(nc):
        con = t.constructor(c)
        rec = t.recognizer(c)
        nfields = con.arity()
        if nfields == 0:
            res = kwargs[con.name()]
        else:
            res = kwargs[con.name()](  *[t.accessor(c,a)(x) for a in range(nfields)] )
        acc = If(rec(x), res, acc)
    return acc
```

Example usage:

```python

match(Const("x", Maybe(IntSort())), Just=lambda y : y + 1, Nothing = IntVal(3), _=IntVal(10))
# returns If(is(Nothing, x), 3, If(is(Just, x), fromJust(x) + 1, 10))
```

Z3 has a substitution mechanism built in.  This is useful for instantiating `ForAll` and for evaluating `Lambda`. The `substitute_vars` function is what you want like so `substitute_vars(f.body(), x, y, z)`

It is possible to reflect the syntax in a fairly straightforward way back into python via a lambdify function, mimicking the equivalent very useful [function from sympy](https://docs.sympy.org/latest/modules/utilities/lambdify.html). Lambdify is basically an `interp` function. Here is a start for such a function. I by no means have implemented interpretation of the entirety of z3. Also I feel like this implementation is very clunky. Some kind of CPS?

```python

def lift1(f,x):
    return lambda *args: f(x(*args))

def lift2(op,l,r):
    return lambda *args: op(l(*args), r(*args))

# interp is useful for transferring expressions into numpy, sympy
# but also for program extraction

from functools import reduce
import operator as op
def interp(a, *args):
    if is_true(a):
        return lambda *args: True
    elif is_false(a):
        return lambda *args: False
    elif is_int_value(a):
        return lambda *args: a.as_long()
    elif is_rational_value(a):
        n = a.numerator_as_long()
        d = a.denominator_as_long()
        return lambda *args: n / d
    #elif is_algebraic_value(a):
    #    pass
    elif is_const(a): # is free variable
        loc = [ind for ind, b in enumerate(args) if eq(a,b)]
        if len(loc) == 0:
            return a
        else:
            ind = loc[0]
            return lambda *args2: args2[ind]   
    b = [interp(c, *args) for c in a.children()]
    if is_and(a):
        return lambda *args: reduce(op.and_, [f(*args) for f in b])
    elif is_or(a):
        return lambda *args: reduce(op.or_, [f(*args) for f in b])
    elif is_app_of(a, Z3_OP_XOR):
        return lambda *args: reduce(op.xor, [f(*args) for f in b])
    elif is_add(a):
        return lambda *args: reduce(op.add, [f(*args) for f in b])
    elif is_mul(a):
        return lambda *args: reduce(op.mul, [f(*args) for f in b])
    elif len(b) == 1:
        n = b[0]    
        if is_not(a):
            return lift1(op.invert , n)# lambda *args: ~n
    elif len(b) == 2:
        l,r = b
        if is_eq(a):
            return lift2(op.eq, l,r) #lambda *args: l == r
        elif is_distinct(a): # This can be multi_argument
            return lift2(op.ne, l,r) # lambda *args: l != r
        elif is_sub(a):
            return lift2(op.sub, l,r) # lambda *args: l - r
        elif is_app_of(a, Z3_OP_POWER):
            return lift2(op.pow, l,r) #lambda *args: l ** r
        elif is_div(a):
            return  lift2(op.truediv, l,r)# lambda *args: l / r
        elif is_idiv(a):
            return lift2(op.floordiv, l,r) # lambda *args: l // r
        elif is_mod(a):
            return lift2(op.mod, l,r) # lambda *args: l % r
        elif is_le(a):
            return lift2(op.le, l,r) # lambda *args: l <= r
        elif is_lt(a):
            return lift2(op.lt, l,r) # lambda *args: l < r
        elif is_ge(a):
            return lift2(op.ge, l,r) #lambda *args: l > r
        elif is_gt(a):
            return lift2(op.gt, l,r) # lambda *args: l >= r
        elif is_implies(a):
            return lambda *args: (~ l(*args) ) & r(*args) 
    print("unrecognized constructor: ", type(a))
    assert(False)
```

```python

#example usage
a = Bool('a')
interp(Xor(a & a | a, a), a)(True)
x, y = Reals('x y')
interp(x + y + y + y * x, x ,y)(3,2)
```

There is the ability to define recursive functions in z3. It is also plausible to define them via. In this way you can get a reversible functional programming language, maybe some subset of mercury / curry's power.

```python

fac = RecFunction('fac', IntSort(), IntSort())
n = Int('n')
RecAddDefinition(fac, n, If(n == 0, 1, n*fac(n-1)))

s = Solver()
s.add(fac(n) == 6)
s.check()
s.model()
#  returns [n = 3, fac = [0 → 1, else → fac(-1 + ν0)·ν0]]
```

### Interactive Theorem Proving

Z3 is awesome at thoerem proving. But somethings it just doesn't handle right and needs human guidance.

Through searching, there are a couple interesting python interactive theorem prover projects. Cody pointed me to a project he worked on a while back, Boole [https://github.com/avigad/boole](https://github.com/avigad/boole) . It has a dependently typed lambda calculus in it with the purpose of gluing together many systems, I think. He implemented a lot of stuff from scratch. I think I want to try to get less and do less. There is also holpy [https://arxiv.org/abs/1905.05970](https://arxiv.org/abs/1905.05970) which appears to be being actively developed. It's roughly a translation of hol to python I think. It's available from a strange chinese github on the author's website if you go looking for it.

This suggests an interesting approach. Most interactive theorem provers start unautomated and add it later. Instead we can iteratively build an interface to de-automate z3.

Altogether, this approach is more HOL flavored than Coq/Agda flavored. z3 terms are our logic and python is our manipulation metal language. Ideally, one would want to verify that every.

Python is so unprincipled that I can't imagine that you could ever build a system up to the trustworthiness of the other theorem provers. But this is freeing in many ways. Since that is off the table, we can just do the best we can.

Using the z3 syntax tree and the z3 proof automation and z3 substitution mechanisms gives us a HUGE step up from implementing them from scratch. Ideally, we'd want to write as little python as possible, and especially as little python as possible that has to be trusted to be implemented correctly.

One big concern is accidental mutation of the proof under our feet by python. Perhaps using hashes and checking them might be a way to at least detect this. I need to have a good think about how to factor out a trusted core from all possible tactics.

I think it helps a little that z3 often will be able to verify the equivalence of small steps in proofs even if it can't do the entire proof itself.

I think induction principles will need to be injected by hand. Z3 doesn't really have that built in. There are definitely situations that after you introduce the induction, z3 can slam all the cases no problem. For example, check this out.

Another thing that might be nice is integration/translation to sympy. Sympy has a ton of useful functionality, at the very least differentiation.

Translation and integration with cvxpy for sum of squares proofs would also be quite neat. I already did something with this using sympy. I'm not super sure how you extract exact proofs from the floating point solutions SCS returns? I think there is a thing. I've heard the LLL algorithm can be used for this somehow (finding likely algebraic number matches to floating point numbers)?

So here are some sketched out ideas for tactics.

```python

class Proof():
    def __init__(self, goal, name=None): # Taken a name for the theorem?
        self.goals = [([],goal)]
        self.proven = False
        self.name = name
    #def intros(self): #intro_all        
    #    self.goals.append( (ctx, goal.intros())  )
    #    return self
    def equiv(self, goal2):
        ctx, goal1 = self.goals.pop()
        if prove2(Implies(And(*ctx), goal1 == goal2)):
            g = goal2
        else:
            g = goal1
        self.goals.append( (ctx, g))
        return self
    def __eq__(self,rhs):
        return self.equiv(rhs)
    #def assert(): #put new goal in stack with current context. Put into context of 1 below top
    #def assume(): #just put crap in the context.
    def intro_all(self): #name = hint maybe later
        ctx, goal = self.goals.pop()
        assert(goal.is_forall())
        vs = [FreshConst(goal.var_sort(i) , prefix=goal.var_name(i)) for i in range(goal.num_vars())]
        g = instantiate(goal,*vs) 
        self.goals.append( (ctx + vs, g)) # wait. I should keep propositions and variables seperate
        return self
    def intro_imp(self): #intro_impl
        ctx, goal = self.goals.pop()
        if is_implies(goal):
            a, b = goal.children()
            ctx.append(a)
            self.goals.append((ctx,b))
        else:
            self.goals.append((ctx,goal))
        return self
    def split(self): #z3 tactic split-clauses?
        ctx, goal = self.goals.pop()
        if is_and(goal):
            for c in goal.children():
                self.goals.append((ctx,c))
        else:
            self.goals.append((ctx,goal))
        return self
    def z3_tactic(self,t):
        t = Tactic(t)
        ctx, goal = self.goals.pop()
        #g = t(Implies(And(*ctx), goal)).as_expr()
        g = t(goal).as_expr()
        self.goals.append(([],g))
        return self
    def simpl(self):
        return self.z3_tactic("simplify")
    def congruence(self):
        #maybe search for equalities. And put them in the goal
        return self.z3_tactic("solve-eqs")
    def smt(self):
        ctx, goal = self.goals.pop()
        s = Solver()
        #s.set(**keywords)
        claim = Implies(And(*ctx), goal)
        s.add(Not(claim))
        r = s.check()
        if r  == sat:
            print("Countermodel : " + str(s.model()))
        assert(r == unsat)
        return self
    def destruct(self):
        ctx, goal = self.goals.pop()
        if is_bool(goal):
            ctx1 = ctx.copy()
            ctx2 = ctx.copy()
            ctx1.append(goal == True)
            ctx2.append(goal == False)
            self.goals.append((ctx2, BoolVal(False) ))
            self.goals.append((ctx1, BoolVal(True) ))
        else:
            self.goals.append((ctx, goal))    
        return self
    def forget(self,n):
        ctx, goal = self.goals.pop()
        ctx.pop(n)
        self.goals.append((ctx, goal))  
        return self
    def qed(self):
        if len(self.goals) == 0:
            self.proven = True
            # add self to global proof context if self.name is not None
    def get_ctx(self,n):
        return self.goals[-1][0][n]
    def __str__(self):
        if len(self.goals) >= 1:
            ctx, goal = self.goals[-1]
            return "".join([f"[{i}] {str(c)} : {str(c.sort())}\n" for i, c in enumerate(ctx)]) + "----------------\n" + f"{str(goal)} : {str(goal.sort())}"
        else:
            return "No Goals Left"
    def __repr__(self):
        return str(self)
```

```python

x = Real("x")
Proof(x**2 - 1 == 0).equiv((x+1)*(x-1) == 0).equiv((x == 1) | (x == -1))
```

```python

a, b = Bools('a b')
p = Proof((a & b) > b)
p.intro_imp().destruct() 
   .smt() \
   .smt() \
.qed()
```

Another question is how to implement an apply tactic gracefully. Fully deconstructing syntax trees and unifying ourselves is not utilizing z3 well. If you have a good idea how to get unification out of z3, I'd be interested to hear from you here.  [https://stackoverflow.com/questions/59398955/getting-z3-instantiations-of-quantified-variables/59400838#59400838](https://stackoverflow.com/questions/59398955/getting-z3-instantiations-of-quantified-variables/59400838#59400838)

Here's an idea though. In the cold light of day, I am still not sure this reasoning makes much sense. Suppose we're trying to apply forall x. a(x) -> b(x) to a c(y). If forall x. b(x) -> c(y) we're good and by assumption that is obvious for some reason, like the syntactic instantiation of b gives c. We can ask z3 to prove that and it will hopefully easy. If we can prove forall x. a(x) in the current context, that would be sufficient, but not true typically. It is an overly difficult request. We really only need to prove a(x) for values pertinent to the proof of c(y). Here's a suspicious strategem. Any a -> b can be weakened to (q -> a) -> (q -> b). In particular we can choose to weaken forall x. a(x) -> b(x) to forall x. ((c(y) -> b(x)) -> a(x)) -> ((c(y) -> b(x)) -> b(x)). Then we can replace the goal with forall x. ((c(y) -> b(x)) -> a(x)) after we prove that (forall x. (c(y) -> b(x)) -> b(x)) -> c(y).  Maybe c(y) -> b(x) is sufficient to restrict the values of x? Not sure.

Another rough sketch of induction on Nat. Not right yet.

```python

def inductionNat(self):
    assert(self.num_vars() == 1 and self.var_sort(0) == IntSort() and self.is_forall())
    n = FreshInt()
    return instantiate(self, IntVal(0)) & ForAll([n],instantiate(self, n) & (n > 0) > instantiate(self, n+1))
```

We could also make a simple induction for ADTs based on the similar introspection we used for `match` above. It's ugly but I think it works.

```python

def induction(self):
    assert(is_quantifier(self) and self.is_forall() and self.num_vars() == 1) #we can eventually relax vars = 1
    t = self.var_sort(0)
    nc = t.num_constructors()
    th = []
    for i in range(nc):
        con = t.constructor(i)
        nfields = con.arity()
        if nfields == 0:
            th += [substitute_vars(self.body(), con())]
        else:
            hyp = []
            args = []
            for d in range(nfields):
                td = con.domain(d)
                x = FreshConst(td)
                print(x)
                if td == t:
                    hyp += [substitute_vars(self.body(), x)]
                args += [x]
            th += [ForAll(args, Implies(And(*hyp), substitute_vars(self.body(), con(*args))))]
        print(th)
    return And(*th)
```

I haven't really though much about tacticals yet.

```

# describe_tactics() gives a list of all z3 tactics
ackermannize_bv : A tactic for performing full Ackermannization on bv instances.
subpaving : tactic for testing subpaving module.
horn : apply tactic for horn clauses.
horn-simplify : simplify horn clauses.
nlsat : (try to) solve goal using a nonlinear arithmetic solver.
qfnra-nlsat : builtin strategy for solving QF_NRA problems using only nlsat.
nlqsat : apply a NL-QSAT solver.
qe-light : apply light-weight quantifier elimination.
qe-sat : check satisfiability of quantified formulas using quantifier elimination.
qe : apply quantifier elimination.
qsat : apply a QSAT solver.
qe2 : apply a QSAT based quantifier elimination.
qe_rec : apply a QSAT based quantifier elimination recursively.
psat : (try to) solve goal using a parallel SAT solver.
sat : (try to) solve goal using a SAT solver.
sat-preprocess : Apply SAT solver preprocessing procedures (bounded resolution, Boolean constant propagation, 2-SAT, subsumption, subsumption resolution).
ctx-solver-simplify : apply solver-based contextual simplification rules.
smt : apply a SAT based SMT solver.
psmt : builtin strategy for SMT tactic in parallel.
unit-subsume-simplify : unit subsumption simplification.
aig : simplify Boolean structure using AIGs.
add-bounds : add bounds to unbounded variables (under approximation).
card2bv : convert pseudo-boolean constraints to bit-vectors.
degree-shift : try to reduce degree of polynomials (remark: :mul2power simplification is automatically applied).
diff-neq : specialized solver for integer arithmetic problems that contain only atoms of the form (<= k x) (<= x k) and (not (= (- x y) k)), where x and y are constants and k is a numeral, and all constants are bounded.
eq2bv : convert integer variables used as finite domain elements to bit-vectors.
factor : polynomial factorization.
fix-dl-var : if goal is in the difference logic fragment, then fix the variable with the most number of occurrences at 0.
fm : eliminate variables using fourier-motzkin elimination.
lia2card : introduce cardinality constraints from 0-1 integer.
lia2pb : convert bounded integer variables into a sequence of 0-1 variables.
nla2bv : convert a nonlinear arithmetic problem into a bit-vector problem, in most cases the resultant goal is an under approximation and is useul for finding models.
normalize-bounds : replace a variable x with lower bound k <= x with x' = x - k.
pb2bv : convert pseudo-boolean constraints to bit-vectors.
propagate-ineqs : propagate ineqs/bounds, remove subsumed inequalities.
purify-arith : eliminate unnecessary operators: -, /, div, mod, rem, is-int, to-int, ^, root-objects.
recover-01 : recover 0-1 variables hidden as Boolean variables.
bit-blast : reduce bit-vector expressions into SAT.
bv1-blast : reduce bit-vector expressions into bit-vectors of size 1 (notes: only equality, extract and concat are supported).
bv_bound_chk : attempts to detect inconsistencies of bounds on bv expressions.
propagate-bv-bounds : propagate bit-vector bounds by simplifying implied or contradictory bounds.
propagate-bv-bounds-new : propagate bit-vector bounds by simplifying implied or contradictory bounds.
reduce-bv-size : try to reduce bit-vector sizes using inequalities.
bvarray2uf : Rewrite bit-vector arrays into bit-vector (uninterpreted) functions.
dt2bv : eliminate finite domain data-types. Replace by bit-vectors.
elim-small-bv : eliminate small, quantified bit-vectors by expansion.
max-bv-sharing : use heuristics to maximize the sharing of bit-vector expressions such as adders and multipliers.
blast-term-ite : blast term if-then-else by hoisting them.
cofactor-term-ite : eliminate term if-the-else using cofactors.
collect-statistics : Collects various statistics.
ctx-simplify : apply contextual simplification rules.
der : destructive equality resolution.
distribute-forall : distribute forall over conjunctions.
dom-simplify : apply dominator simplification rules.
elim-term-ite : eliminate term if-then-else by adding fresh auxiliary declarations.
elim-uncnstr : eliminate application containing unconstrained variables.
injectivity : Identifies and applies injectivity axioms.
snf : put goal in skolem normal form.
nnf : put goal in negation normal form.
occf : put goal in one constraint per clause normal form (notes: fails if proof generation is enabled; only clauses are considered).
pb-preprocess : pre-process pseudo-Boolean constraints a la Davis Putnam.
propagate-values : propagate constants.
reduce-args : reduce the number of arguments of function applications, when for all occurrences of a function f the i-th is a value.
reduce-invertible : reduce invertible variable occurrences.
simplify : apply simplification rules.
elim-and : convert (and a b) into (not (or (not a) (not b))).
solve-eqs : eliminate variables by solving equations.
special-relations : detect and replace by special relations.
split-clause : split a clause in many subgoals.
symmetry-reduce : apply symmetry reduction.
tseitin-cnf : convert goal into CNF using tseitin-like encoding (note: quantifiers are ignored).
tseitin-cnf-core : convert goal into CNF using tseitin-like encoding (note: quantifiers are ignored). This tactic does not apply required simplifications to the input goal like the tseitin-cnf tactic.
qffd : builtin strategy for solving QF_FD problems.
pqffd : builtin strategy for solving QF_FD problems in parallel.
smtfd : builtin strategy for solving SMT problems by reduction to FD.
fpa2bv : convert floating point numbers to bit-vectors.
qffp : (try to) solve goal using the tactic for QF_FP.
qffpbv : (try to) solve goal using the tactic for QF_FPBV (floats+bit-vectors).
qffplra : (try to) solve goal using the tactic for QF_FPLRA.
default : default strategy used when no logic is specified.
sine-filter : eliminate premises using Sine Qua Non
qfbv-sls : (try to) solve using stochastic local search for QF_BV.
nra : builtin strategy for solving NRA problems.
qfaufbv : builtin strategy for solving QF_AUFBV problems.
qfauflia : builtin strategy for solving QF_AUFLIA problems.
qfbv : builtin strategy for solving QF_BV problems.
qfidl : builtin strategy for solving QF_IDL problems.
qflia : builtin strategy for solving QF_LIA problems.
qflra : builtin strategy for solving QF_LRA problems.
qfnia : builtin strategy for solving QF_NIA problems.
qfnra : builtin strategy for solving QF_NRA problems.
qfuf : builtin strategy for solving QF_UF problems.
qfufbv : builtin strategy for solving QF_UFBV problems.
qfufbv_ackr : A tactic for solving QF_UFBV based on Ackermannization.
ufnia : builtin strategy for solving UFNIA problems.
uflra : builtin strategy for solving UFLRA problems.
auflia : builtin strategy for solving AUFLIA problems.
auflira : builtin strategy for solving AUFLIRA problems.
aufnira : builtin strategy for solving AUFNIRA problems.
lra : builtin strategy for solving LRA problems.
lia : builtin strategy for solving LIA problems.
lira : builtin strategy for solving LIRA problems.
skip : do nothing tactic.
fail : always fail tactic.
fail-if-undecided : fail if goal is undecided.
macro-finder : Identifies and applies macros.
quasi-macros : Identifies and applies quasi-macros.
ufbv-rewriter : Applies UFBV-specific rewriting rules, mainly demodulation.
bv : builtin strategy for solving BV problems (with quantifiers).
ufbv : builtin strategy for solving UFBV problems (with quantifiers).
```
