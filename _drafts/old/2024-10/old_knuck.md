# cody match

```python
from knuckledrag2 import *

global_var_env = {}

class MetaVar(Term):

    def __init__(self, name, env = global_var_env):
        self.name = name
        self.env = env
        if name not in self.env:
            self.level = -1
            self.env[name] = 0
        else:
            self.level = global_var_env[name]
            self.env[name] = self.level + 1

    def __str__(self):
        if self.level == -1:
            return self.name
        else:
            return self.name + str(self.level)

    def __eq__(self, other):
        if not isinstance(other, MetaVar):
            return False
        return (self.name == other.name) and (self.level == other.level)
    def __hash__(self):
        return hash((self.name, self.level))

# A little clunky
def open_vars_aux(term, metas):
    if isinstance(term, Var):
        if term.name in metas:
            return metas[term.name]
        else:
            return term
    if isinstance(term, FunApp):
        #We force the list right away
        args = list(map(lambda t: open_vars_aux(t, metas), term.args))
        return FunApp(term.name, args)
    if isinstance(term, BindApp):
        metas_pruned = metas.copy()
        bound_names = map(lambda v: v.name, term.vars)
        for v in metas_pruned:
            if v in bound_names:
                del(metas_pruned[v])
        return BindApp(term.vars, open_vars_aux(term.body, metas_pruned))
    if isinstance(term, MetaVar):
        return term
    else:
        raise ValueError("open_vars_aux: unkown instance")

#Uses global_var_env for now
def open_bound(term):
    if isinstance(term, BindApp):
        metas = {}
        for v in term.vars:
            mv = MetaVar(v.name)
            metas[v.name] = mv
        return open_vars_aux(term.body, metas)
    raise ValueError('open_bound: value is not a binder!')

#Substitutions are little more than a wrapper around a dictionary,
# and a method that performs the substitution `this.apply(term)`.
class Subst():

    def __init__(self, assgn):
        self.assgn = assgn

    def __getitem__(self, key):
        return self.assgn[key]

    def __setitem__(self, key, newval):
        self.assgn[key] = newval

    def __contains__(self, key):
        return key in self.assgn

    # tedious; python doesn't like dicts with wonky keys
    def __str__(self):
        s = (", ".join("{}: {}".format(k, v) for k, v in self.assgn.items()))
        return "{{ {} }}".format(s)

    def apply(self, term):
        # this would be better/easier with a visitor
        if isinstance(term, MetaVar):
            return self.applyMetaVar(term)
        if isinstance(term, Var):
            return self.applyVar(term)
        if isinstance(term, FunApp):
            return self.applyFunApp(term)
        if isinstance(term, BindApp):
            return self.applyBindApp(term)
        ## We could return term here, but it's a bit "offensive"
        raise ValueError("Subst.apply: Unkown term constructor")

    def applyMetaVar(self, term):
        if term in assgn:
            return self[term]
        else:
            # for now, we allow metavariables to go unresolved
            return term

    def applyVar(self, term):
        return term

    def applyFunApp(self, term):
        return FunApp(term.name, map(lambda t:self.apply(t), term.args))

    def applyBindApp(self, term):
        #things are easy here, because we handled shadowing in `open_bound`
        return BindApp(term.vars, self.apply(term.body))

def EmptySubst():
    return Subst({})

#takes a single pattern (with "fresh" metavars) and a term and returns
#the mgu, or None if none exists.
class Matcher():

    def __init__(self, pattern, term, subst):
        self.pattern = pattern
        self.term = term
        self.subst = subst

    def apply(self):
        if not self.subst:
            return
        if isinstance(self.pattern, MetaVar):
            #the interesting bit
            if self.pattern in self.subst:
                self.pattern = self.subst[self.pattern]
                self.apply()
                return
            else:
                #this is a call to `Subst.__setitem__`
                self.subst[self.pattern] = self.term
                return
        if isinstance(self.pattern, Var) and isinstance(self.term, Var):
            if self.pattern.name != self.term.name:
                self.subst = None
                return
        if isinstance(self.pattern, FunApp) and isinstance(self.term, FunApp):
            if self.pattern.name != self.term.name:
                self.subst = None
                return
            for i in range(len(self.pattern.args)):
                self.pattern = self.pattern.args[i]
                self.term = self.term.args[i]
                self.apply()
                return

        if isinstance(self.pattern, BindApp) and isinstance(self.term, BindApp):
            for v in self.pattern.vars:
                if v not in self.term.vars:
                    self.subst = None
                    return
                self.pattern = self.pattern.body
                self.term = self.term.body
                self.apply()
                return
        else:
            self.subst = None
            return

def match(pattern, term):
    matcher = Matcher(pattern, term, EmptySubst())
    matcher.apply()
    return matcher.subst

if __name__ == "__main__":
    x = Var('x')
    A = lambda t:Atom('A', [t])
    B = lambda t:Atom('A', [t])
    three = Var('3')
    matcher = ForAll([x], A(x))
    matchee = A(three)
    print(match(open_bound(matcher), matchee))

```

# equational

Look at lean for mathemticians.
Look at mathlib theorems.
Do a pile of simple algebraic ones.
(twee should crush it)?
I mean z3 was also fine

define_fun([eq1,eq2,e13])

with solver.ForAllScope(x,y,x) as s:
    s.add(x==y) # auto put ForAll([x,y,z], eq) over everything.
    s.add(y==x)

Pure sympy equational?
sympy "solve" means "find a value for x that makes the equation true".
Eq(a,b) is a statement but I don't know that sympy has a notion of proving it. It's an existential statement kind of.

simplify(lhs) == simplify(rhs)
simplify(lhs - rhs) == 0

```python
db = []
def base(lhs,rhs):
    if sympy.simplify(lhs - rhs).isZero():
        db.append(("eq",lhs,rhs,"sympy.simplify"))
        return len(db)
    else:
        print(lhs,rhs)
        raise ValueError('Could not prove equal')
def trans(eq1,eq2):
    (_, lhs, rhs, _) = db[eq1]
    (_, lhs1, rhs1, _) = db[eq2]
    if sympy.simplify(lhs - lhs1).isZero():
        db.append("trans", lhs, rhs1, ("trans", eq1, eq2))
        return len(db)
    else:
        print(lhs,lhs1)
        raise ValueError('Could not prove equal')
def symm(eq1):
    (_, lhs, rhs, _) = db[eq1]
    db.append("symm", rhs, lhs, ("symm", eq1))
    return len(db)
def subst(t, eq1):
    (lhs, db[eq1]
    sympy.subst()


base(Sum([x], (x, 1, n)), n*(n+1)/2)



```

```python
from knuckledragger.term import Functions, Vars

X,Y,Z = Vars("X Y Z")
f,g,h = Functions("f g h")
a,b,c = Consts("a b c")

```

    ---------------------------------------------------------------------------

    AttributeError                            Traceback (most recent call last)

    Cell In [1], line 3
          1 from knuckledragger.term import Functions, Vars
    ----> 3 X,Y,Z = Vars("X Y Z")
          4 f,g,h = Functions("f g h")


    File ~/Documents/python/knuckledragger/knuckledragger/term.py:88, in Vars(names)
         87 def Vars(names):
    ---> 88     return [Var(name) for name in names.split()]


    File ~/Documents/python/knuckledragger/knuckledragger/term.py:88, in <listcomp>(.0)
         87 def Vars(names):
    ---> 88     return [Var(name) for name in names.split()]


    File ~/Documents/python/knuckledragger/knuckledragger/term.py:71, in Var.__init__(self, name)
         70 def __init__(self, name):
    ---> 71     assert name.isUpper()
         72     self.name = name


    AttributeError: 'str' object has no attribute 'isUpper'

# Algebra of Programming

- Dijkstra
- backhouse
- <http://www.mathmeth.com/read.shtml>
- Bird book
- AoP book
- Gries <https://www.cs.cornell.edu/fbs/publications/EqPropLogic.pdf>

<https://arxiv.org/abs/2312.06103> equatonal reasoning dependent types. references gibbons paper
<https://leahneukirchen.org/caudex/equational-reasoning.html> great links

Triggers and evaluation order. There is a sense that we want rules to be simplifying. In coq etc one cares alot about computational content. Z3 triggers are a way to approach this.

```python
!pip install git+https://github.com/philzook58/knuckledragger.git

```

<a target="_blank" href="https://colab.research.google.com/github/philzook58/knuckledragger.git">
  <img src="https://colab.research.google.com/assets/colab-badge.svg" alt="Open In Colab"/>
</a>

Open in google colab <https://colab.research.google.com/github/philzook58/knuckledragger/blob/main/theories/equational.ipynb>

There are examples of `calc` tactics elsewhere in lean and dafny. Rather than using the raw inference rules, we can write down an equational proof

```python
from knuckledragger.kernel import infer
class Calc():
    def __init__(self, lhs, rhs, ctx = []):
        self.terms = [lhs]
        self.thm = infer(ctx, lhs == lhs)
        self.thms = []
        self.goal = rhs
        self.ctx = ctx
    def then(self, rhs, by=[]): # step? rw?
        thm = infer(by + self.ctx, self.terms[-1] == rhs)
        self.thm = infer([thm, self.thm], self.terms[0] == rhs)
        self.thms.append(thm)
        self.terms.append(rhs)
        return self
    def __eq__(self,rhs): #sadly the way python expands multiple == this does not work that great. needs parens
        return self.then(rhs)
    def simp(): # use z3 simplify. Weak though becaus can't be context aware
        self.
        return self
    def egg_simp(self):
        return self
    def __repr__(self):
        return " == ".join(map(repr, self.terms))
    def __str__(self):
        return repr(self)
    def sympy():
        return self
        pass # use sympy to simplify, use z3 to confirm
    def qed(self, by=[]):
        if self.terms[-1] is not self.goal:
            self.then(self.goal, by=by)
        return self.thm
    
def calc(*steps): # a different syntax for calc
    pf = Calc(steps[0], steps[-1])
    for t in steps[1:-1]:
        pf = pf.then(t)
    return pf
```

```python
from knuckledragger.kernel import trust
from z3 import *
Atom = DeclareSort("Atom")
a,b,c,d = Consts("a b c d", Atom)
ab = trust(a == b)
bc = trust(b == c)
cd = trust(c == d)
pf = Calc(a, d).then(b, by=[ab]).then(c, by=[bc]).then(d, by=[cd])
ad = pf.qed()
ad
#Calc(a,d, ctx=[ab,bc,cd]) == b == c == d 
((Calc(a,d, ctx=[ab,bc,cd]) == b) == c) == d
```

    a == b == c == d

You can also calc chain equalities of boolean expressions that are the same.
Calc also supports an inequality modes

Adding forall.

# Equational Propositional Logic

<https://www.cs.cornell.edu/fbs/publications/EqPropLogic.pdf>
table 2

```python
Prop = DeclareSort("Prop")
eq = Function(Prop, Prop, Prop)
true = Const("true", Prop)
false = Const("false", Prop)
_not = Function(Prop, Prop)
_and = Function(Prop, Prop, Prop)
_or = Function(Prop, Prop, Prop)
_implies = Function(Prop, Prop, Prop)

#eq_reflect =  trust(Implies(eq(a,b), a == b))
eq_reflect = trust(eq(a,b) == (a == b))
eq_assoc = trust(eq(eq(a,b),c) == eq(a,eq(b,c)))
eq_sym = trust(eq(a,b) == eq(b,a))
eq_id = trust(eq(true,eq(a,a)))
false_def = trust(eq(false, _not(true)))
not_eq_distr = trust(_not(eq(a,b)) == eq(_not(a), b))

axioms = [eq_assoc, eq_sym, eq_id, false_def, not_eq_distr]

def not_eq(a,b): # macro definition instead of first class.
    return _not(eq(a,b))

Calc(eq(_and(p, _or(p,q)) p))



```

# Concrete Mathematics

Josephus
Recurrences
Using sympy solutions
hypergeometric

```python

_sum = Function("sum", ArraySort(IntSort(), RealSort()), IntSort(), IntSort(), RealSort())
def Sum(c_i, i, a, b):
    return _sum(Lambda([i], c_i), a, b)
sum_base = trust(ForAll([c_i, a], (c_i, a, a) == 0))
sum_succ = trust(ForAll([c_i, a ,b], _sum(c_i, a, b+1) == _sum(c_i, a, b) + c_i[b]))

#induct = trust()

# sum_all = Function("sumall", ArraySort(IntSort(), RealSort()), RealSort()) infinite sum. Harder to treat. Non computational in some sense.
# sum_set Function("sumset", ArraySort(IntSort(), RealSort()), ListSort(IntSort()), RealSort())) # finite list
# possibly ifninite set?
#sum_set = Function("sumset", ArraySort(IntSort(), RealSort()), ArraySort(IntSort(), BoolSort()), ArraySort(IntSort(), RealSort()))


```

```python
# we need to axiomatize pow because Z3 power cannot handle variables in the exponent
x = Real("x")
n = Int("n")
pow = Function("pow", RealSort(), IntSort(), RealSort())
pow_def = trust(ForAll([x,n], pow(x,n) == If(n == 0, 1, 
                                          If(n < 0 , pow(x,n+1) / x, 
                                                     x*pow(x,n-1)))))
# can't do this because recursive definition. Fine.
#pow, pow_def = define("pow", Lambda([x,n], If(n == 0, 1, 
#                               If(n < 0 , pow(x,n+1) / x, 
#                                          x*pow(x,n-1)))))

pow_zero = infer([pow_def], ForAll([x], pow(x,0) == 1))
pow_one = infer([pow_def, pow_zero], ForAll([x], pow(x,1) == x))
pow_one = infer([pow_def, pow_one], ForAll([x], pow(x,1) == x))

# axiom specialized to particular powers
pown = [pow_zero]
for i in range(1,5):
    pown.append(infer([pow_def, pown[-1]], ForAll([x], pow(x,i) == x**i)))
pown
```

    [(7416851326278927786, ForAll(x, pow(x, 0) == 1)),
     (3910822737024964705, ForAll(x, pow(x, 1) == x**1)),
     (-8021081544531509068, ForAll(x, pow(x, 2) == x**2)),
     (9063170249293680640, ForAll(x, pow(x, 3) == x**3)),
     (8460666806402329999, ForAll(x, pow(x, 4) == x**4))]

```python
fall_pow
```

```python

```

# 2023-z3-itp

Interactive theorem proving is cool.

Automated theorem proving is really cool.

It does happen though that you can get outside the ability of an automated theorem prover in one shot. It may need breadcrumbs or guidance along the way.
But then you need some kind of scaffolding to organize these hints.

I think this is an interesting design I don't see much.

The basic premise is that we allow a single inference rule SUPERMODUS (TM) which uses an automated prover to discharge a big step of the proof. We get to manually select if we like the hypothesies it has access to.

unsat core might be useful to prune the hypotheses for faster future proofs

```python
from typing import Any, Tuple, List
from z3 import *
Form = Any
Thm = Tuple[int, Form]
BoolRef.__and__ = lambda self, other: And(self, other)
BoolRef.__or__ = lambda self, other: Or(self, other)
BoolRef.__invert__ = lambda self: Not(self)
BoolRef.__gt__ = lambda self, other: Implies(self, other) # maybe not worth it. It twists meaning too much
def QForAll(vars, hyp, conc): # useful helper pattern
    return ForAll(vars, Implies(hyp, conc))

def check(thm : Thm):
    hsh, form = thm
    assert hsh == hash(("secret",form))

# recording all known theorems makes certain big hammer autos possible.
# thms = [] # or set()
def formula(thm : Thm) -> Form:
    return thm[1]

def trust(form : Form) -> Thm:
    #thms.append(concthm)
    return hash(("secret",form)), form

def infer(hyps : List[Thm], conc : Form, timeout=1000) -> Thm:
    s = Solver()
    for hyp in hyps:
        check(hyp)
        s.add(hyp[1])
    s.add(Not(conc))
    s.set("timeout", timeout)
    res = s.check()
    if res != z3.unsat:
        print(s.sexpr())
        if res == z3.sat:
            print(s.model())
        assert False,res

    return trust(conc)

def extend(hyps, x,y, P : Form, prefix="c"):
    infer(hyps, ForAll([x],Exists([y], P)))
    f = FreshConst(ArraySort(x.sort(), y.sort()), prefix=prefix)
    return f, trust(ForAll([x], P.substitute(y,f[y])))

# A primitive definition mechanism. Maybe + Lambda this is good enough?
def define(name, x):
    f = FreshConst(x.sort(), prefix=name)
    return f, trust(f == x)



```

```python
proof_db = []
Thm = int

def trust(form : Form, reasons = None) -> Thm:
    proof_db.append((form, reasons))
    return len(proof_db)-1

def check(form):
    pass

def formula(thm:Thm) -> Form: # this replaces "check" I guess if check returns the formula and does the check.
    return proof_db[thm][0]

def infer(hyps : List[Thm], conc : Form, timeout=1000) -> Thm:
    s = Solver()
    for hyp in hyps:
        s.add(formula(hyp))
    s.add(Not(conc))
    s.set("timeout", timeout)
    res = s.check()
    if res != z3.unsat:
        print(s.sexpr())
        if res == z3.sat:
            print(s.model())
        assert False,res

    return trust(conc, reasons=("infer", hyps))


def extend(hyps, x,y, P : Form, prefix="c"):
    infer(hyps, ForAll([x],Exists([y], P)))
    f = FreshConst(ArraySort(x.sort(), y.sort()), prefix=prefix)
    return f, trust(ForAll([x], P.substitute(y,f[y])), reasons=("extend", hyps))

# A primitive definition mechanism. Maybe + Lambda this is good enough?
def define(name, x):
    f = FreshConst(x.sort(), prefix=name)
    return f, trust(f == x, reasons = ("define",))

def metamath():
    # add infer as a metamath rule? and use metamath syntax otherwise.
    # there's a lot of impedance mismatch.
    pass
def json_proof():
    json.dump(proof_db, open("proof_db.json", "w"))
def sql():
    for (thm, reasons) in proof_db:
        conn.exec("INSERT INTO thms (thm, reasons) VALUES (?,?)", thm, reasons)
```

```python


```

    <PyRes.saturation.SearchParams object at 0x7fb829e1a770>
    None
    []
    <PyRes.lexer.Lexer object at 0x7fb829e1a7d0>
    False





    cnf(c0,plain,foo(bar,Biz)).

Evidence.

Z3 handles a quantifier free fragment best. (maybe a single forall isn't)
PRA is quantifier free
So was ACL2
Check out ACL2

Carrying "proof" objects as last argument a la datalog.
antiderivative is proof of integration
Dual vector (although maybe not necessary)
List of zeros or poles

Don't ever pack existentials.
evenness and the div2 number
Does this get out of control?

```python
import subprocess
def infer_vampire(hyps : List[Thm], conc : Form, timeout=1000) -> Thm:
    s = Solver()
    for hyp in hyps:
        check(hyp)
        s.add(hyp[1])
    s.add(Not(conc))
    with open("/tmp/temp.smt2", "w") as f:
        f.write(s.sexpr())
    print(s.sexpr())
    res = subprocess.run(["vampire", "/tmp/temp.smt2", "--output_mode", "smtcomp"], timeout=1.0, capture_output=True)
    print(res)
    if "unsat" not in res.stdout.decode("utf-8"):
        print(res.stdout.decode("utf-8"))
        assert False
    return trust(conc)

infer_vampire([], BoolVal(True))
infer_vampire([], BoolVal(False))


    

```

    (assert (not true))
    
    CompletedProcess(args=['vampire', '/tmp/temp.smt2', '--output_mode', 'smtcomp'], returncode=0, stdout=b'Running in auto input_syntax mode. Trying SMTLIB2\nunsat\n', stderr=b'')
    (assert (not false))
    
    CompletedProcess(args=['vampire', '/tmp/temp.smt2', '--output_mode', 'smtcomp'], returncode=0, stdout=b'Running in auto input_syntax mode. Trying SMTLIB2\nsat\n', stderr=b'')
    Running in auto input_syntax mode. Trying SMTLIB2
    sat
    



    ---------------------------------------------------------------------------

    AssertionError                            Traceback (most recent call last)

    /home/philip/Documents/philzook58.github.io/_drafts/2023-11-09-z3-itp.ipynb Cell 3 line 1
         <a href='vscode-notebook-cell:/home/philip/Documents/philzook58.github.io/_drafts/2023-11-09-z3-itp.ipynb#X54sZmlsZQ%3D%3D?line=15'>16</a>     return trust(conc)
         <a href='vscode-notebook-cell:/home/philip/Documents/philzook58.github.io/_drafts/2023-11-09-z3-itp.ipynb#X54sZmlsZQ%3D%3D?line=17'>18</a> infer_vampire([], BoolVal(True))
    ---> <a href='vscode-notebook-cell:/home/philip/Documents/philzook58.github.io/_drafts/2023-11-09-z3-itp.ipynb#X54sZmlsZQ%3D%3D?line=18'>19</a> infer_vampire([], BoolVal(False))


    /home/philip/Documents/philzook58.github.io/_drafts/2023-11-09-z3-itp.ipynb Cell 3 line 1
         <a href='vscode-notebook-cell:/home/philip/Documents/philzook58.github.io/_drafts/2023-11-09-z3-itp.ipynb#X54sZmlsZQ%3D%3D?line=12'>13</a> if "unsat" not in res.stdout.decode("utf-8"):
         <a href='vscode-notebook-cell:/home/philip/Documents/philzook58.github.io/_drafts/2023-11-09-z3-itp.ipynb#X54sZmlsZQ%3D%3D?line=13'>14</a>     print(res.stdout.decode("utf-8"))
    ---> <a href='vscode-notebook-cell:/home/philip/Documents/philzook58.github.io/_drafts/2023-11-09-z3-itp.ipynb#X54sZmlsZQ%3D%3D?line=14'>15</a>     assert False
         <a href='vscode-notebook-cell:/home/philip/Documents/philzook58.github.io/_drafts/2023-11-09-z3-itp.ipynb#X54sZmlsZQ%3D%3D?line=15'>16</a> return trust(conc)


    AssertionError: 

```python

```

```python
import egglog
egraph = egglog.EGraph()
egglog.bindings.Function("foo").register(egraph)
```

    ---------------------------------------------------------------------------

    TypeError                                 Traceback (most recent call last)

    /home/philip/Documents/philzook58.github.io/_drafts/2023-11-09-z3-itp.ipynb Cell 3 line 3
          <a href='vscode-notebook-cell:/home/philip/Documents/philzook58.github.io/_drafts/2023-11-09-z3-itp.ipynb#X40sZmlsZQ%3D%3D?line=0'>1</a> import egglog
          <a href='vscode-notebook-cell:/home/philip/Documents/philzook58.github.io/_drafts/2023-11-09-z3-itp.ipynb#X40sZmlsZQ%3D%3D?line=1'>2</a> egraph = egglog.EGraph()
    ----> <a href='vscode-notebook-cell:/home/philip/Documents/philzook58.github.io/_drafts/2023-11-09-z3-itp.ipynb#X40sZmlsZQ%3D%3D?line=2'>3</a> egglog.bindings.Function("foo").register(egraph)


    TypeError: argument 'decl': 'str' object cannot be converted to 'FunctionDecl'

```python
from egglog.bindings import *


#egraph.register(Function(FunctionDecl("foo", Schema([], "i64"))))
#egraph.relation("foo", "i64")
help(egraph.function)

```

    Help on method function in module egglog.egraph:
    
    function(*args, **kwargs) -> 'Any' method of egglog.egraph.EGraph instance
        Registers a function.

# Tactics

There are a number of derived rules. We can reuse z3's tactics. This is a bit of slight of hand.

```python
def exI(x, P : Thm) -> Thm:
    return infer([P], Exists([x], P[1]))

A = DeclareSort("A")
a = Const("a", A)
P = Function("P", A, BoolSort())
ax = trust(P(a))
exI(a, ax)


# maybe
def simp(thm : Thm):
    check(thm)
    return infer([thm],z3.simplify(thm[1]))

x = Int("x")
thm = infer([], x + 0 == x)
simp(thm)

# other tactics
def tactic(name, thm):
    g = Goal(thm[1])
    conc = z3.Tactic(name)(g)
    print(conc)
    return infer([thm], conc)

tactic("simplify", thm)
    

```

    [[]]



    ---------------------------------------------------------------------------

    Z3Exception                               Traceback (most recent call last)

    /home/philip/Documents/philzook58.github.io/_drafts/2023-11-09-z3-itp.ipynb Cell 4 line 2
         <a href='vscode-notebook-cell:/home/philip/Documents/philzook58.github.io/_drafts/2023-11-09-z3-itp.ipynb#X15sZmlsZQ%3D%3D?line=23'>24</a>     print(conc)
         <a href='vscode-notebook-cell:/home/philip/Documents/philzook58.github.io/_drafts/2023-11-09-z3-itp.ipynb#X15sZmlsZQ%3D%3D?line=24'>25</a>     return infer([thm], conc)
    ---> <a href='vscode-notebook-cell:/home/philip/Documents/philzook58.github.io/_drafts/2023-11-09-z3-itp.ipynb#X15sZmlsZQ%3D%3D?line=26'>27</a> tactic("simplify", thm)


    /home/philip/Documents/philzook58.github.io/_drafts/2023-11-09-z3-itp.ipynb Cell 4 line 2
         <a href='vscode-notebook-cell:/home/philip/Documents/philzook58.github.io/_drafts/2023-11-09-z3-itp.ipynb#X15sZmlsZQ%3D%3D?line=22'>23</a> conc = z3.Tactic(name)(g)
         <a href='vscode-notebook-cell:/home/philip/Documents/philzook58.github.io/_drafts/2023-11-09-z3-itp.ipynb#X15sZmlsZQ%3D%3D?line=23'>24</a> print(conc)
    ---> <a href='vscode-notebook-cell:/home/philip/Documents/philzook58.github.io/_drafts/2023-11-09-z3-itp.ipynb#X15sZmlsZQ%3D%3D?line=24'>25</a> return infer([thm], conc)


    /home/philip/Documents/philzook58.github.io/_drafts/2023-11-09-z3-itp.ipynb Cell 4 line 2
         <a href='vscode-notebook-cell:/home/philip/Documents/philzook58.github.io/_drafts/2023-11-09-z3-itp.ipynb#X15sZmlsZQ%3D%3D?line=19'>20</a>     check(hyp)
         <a href='vscode-notebook-cell:/home/philip/Documents/philzook58.github.io/_drafts/2023-11-09-z3-itp.ipynb#X15sZmlsZQ%3D%3D?line=20'>21</a>     s.add(hyp[1])
    ---> <a href='vscode-notebook-cell:/home/philip/Documents/philzook58.github.io/_drafts/2023-11-09-z3-itp.ipynb#X15sZmlsZQ%3D%3D?line=21'>22</a> s.add(Not(conc))
         <a href='vscode-notebook-cell:/home/philip/Documents/philzook58.github.io/_drafts/2023-11-09-z3-itp.ipynb#X15sZmlsZQ%3D%3D?line=22'>23</a> s.set("timeout", timeout)
         <a href='vscode-notebook-cell:/home/philip/Documents/philzook58.github.io/_drafts/2023-11-09-z3-itp.ipynb#X15sZmlsZQ%3D%3D?line=23'>24</a> res = s.check()


    File ~/.local/lib/python3.10/site-packages/z3/z3.py:1826, in Not(a, ctx)
       1824 else:
       1825     s = BoolSort(ctx)
    -> 1826     a = s.cast(a)
       1827     return BoolRef(Z3_mk_not(ctx.ref(), a.as_ast()), ctx)


    File ~/.local/lib/python3.10/site-packages/z3/z3.py:1531, in BoolSortRef.cast(self, val)
       1529 if not is_expr(val):
       1530     msg = "True, False or Z3 Boolean expression expected. Received %s of type %s"
    -> 1531     _z3_assert(is_expr(val), msg % (val, type(val)))
       1532 if not self.eq(val.sort()):
       1533     _z3_assert(self.eq(val.sort()), "Value cannot be converted into a Z3 Boolean value")


    File ~/.local/lib/python3.10/site-packages/z3/z3.py:107, in _z3_assert(cond, msg)
        105 def _z3_assert(cond, msg):
        106     if not cond:
    --> 107         raise Z3Exception(msg)


    Z3Exception: True, False or Z3 Boolean expression expected. Received [[]] of type <class 'z3.z3.ApplyResult'>

```python
z3.tactics()
```

    ['ackermannize_bv',
     'subpaving',
     'horn',
     'horn-simplify',
     'nlsat',
     'qfnra-nlsat',
     'qe-light',
     'nlqsat',
     'qe',
     'qsat',
     'qe2',
     'qe_rec',
     'psat',
     'sat',
     'sat-preprocess',
     'ctx-solver-simplify',
     'psmt',
     'unit-subsume-simplify',
     'aig',
     'add-bounds',
     'card2bv',
     'degree-shift',
     'diff-neq',
     'eq2bv',
     'factor',
     'fix-dl-var',
     'fm',
     'lia2card',
     'lia2pb',
     'nla2bv',
     'normalize-bounds',
     'pb2bv',
     'propagate-ineqs',
     'purify-arith',
     'recover-01',
     'bit-blast',
     'bv1-blast',
     'bv_bound_chk',
     'propagate-bv-bounds',
     'propagate-bv-bounds2',
     'reduce-bv-size',
     'bv-slice',
     'bvarray2uf',
     'dt2bv',
     'elim-small-bv',
     'max-bv-sharing',
     'blast-term-ite',
     'cofactor-term-ite',
     'collect-statistics',
     'ctx-simplify',
     'demodulator',
     'der',
     'distribute-forall',
     'dom-simplify',
     'elim-term-ite',
     'elim-uncnstr2',
     'elim-uncnstr',
     'elim-predicates',
     'euf-completion',
     'injectivity',
     'snf',
     'nnf',
     'occf',
     'pb-preprocess',
     'propagate-values2',
     'propagate-values',
     'reduce-args',
     'reduce-args2',
     'simplify',
     'elim-and',
     'solve-eqs',
     'special-relations',
     'split-clause',
     'symmetry-reduce',
     'tseitin-cnf',
     'tseitin-cnf-core',
     'qffd',
     'pqffd',
     'smtfd',
     'fpa2bv',
     'qffp',
     'qffpbv',
     'qffplra',
     'default',
     'solver-subsumption',
     'qfbv-sls',
     'nra',
     'qfaufbv',
     'qfauflia',
     'qfbv',
     'qfidl',
     'qflia',
     'qflra',
     'qfnia',
     'qfnra',
     'qfuf',
     'qfufbv',
     'qfufbv_ackr',
     'ufnia',
     'uflra',
     'auflia',
     'auflira',
     'aufnira',
     'lra',
     'lia',
     'lira',
     'smt',
     'skip',
     'fail',
     'fail-if-undecided',
     'macro-finder',
     'quasi-macros',
     'ufbv-rewriter',
     'bv',
     'ufbv']

```python
x = Bool("x")
print( x & x > ~x | x)
x = Array("x", StringSort(), StringSort())
print(x.sort())
print(x.sort().domain())
print(x.sort().range())
print(dir(x.sort()))
x.sort().name()
```

    Implies(And(x, x), Or(Not(x), x))
    Array(String, String)
    String
    String
    ['__bool__', '__class__', '__copy__', '__deepcopy__', '__del__', '__delattr__', '__dict__', '__dir__', '__doc__', '__eq__', '__format__', '__ge__', '__getattribute__', '__gt__', '__hash__', '__init__', '__init_subclass__', '__le__', '__lt__', '__module__', '__ne__', '__new__', '__nonzero__', '__reduce__', '__reduce_ex__', '__repr__', '__setattr__', '__sizeof__', '__str__', '__subclasshook__', '__weakref__', '_repr_html_', 'as_ast', 'ast', 'cast', 'ctx', 'ctx_ref', 'domain', 'domain_n', 'eq', 'get_id', 'hash', 'kind', 'name', 'range', 'sexpr', 'subsort', 'translate', 'use_pp']





    'Array'

```python
class Backward():
    def __init__(self, goal):
        self.goal = infer([], goal > goal)
    def intros(self):
        pass
class Forward(): #Isar
    def __init__(self, goal):
        self.goal = goal
        self.lemmas = []
        self.vars = []
        self.hyps = []
    def intro(self,vars):
        self.vars.extend(vars)
        return self
    def assume(self, hyps):
        self.hyps.extend(hyps)
        return self
    def wrap(self, form):
        return ForAll(self.vars, Implies(And(self.hyps), form))
    def have(self, conc, by=[]):
        self.lemmas.append(infer(by + self.lemmas, conc))
        return self
    def qed(self):
        return infer(self.lemmas, self.goals)




```

# Reals

The z3 "reals" are more like algebraic numbers.
We can add some kind of induction axiom.
Or define CReal as a sequence $ \bN -> bR $ that converges.

There isn't much to talk about in analysis without discussing functions $\bR -> \bR$ or $\bN -> \bR$

## Cosine Doesn't Exist

The notion of completed infinities is problematic and shows up everywhere. Problems that are ultimately obviously solvable, albeit by massive enumeration are nice.
"defining" cosine to be the 1000th term expansion mod 2 pi is pretty good.
Metatheoretically, we can establish the connection to "actual" cosine if we like.
Comparing float32 to float64 is a reasonable method for establishing accuracy estimates / convergence estimates.
The weakness is that sometimes the 1000th term expansion is not an acceptable approxiamtion and we can only detect this metathoretically.
The statement "forall integers" does seem like it is touching to close to completing the integers. Cody mentioned that there is a "cut elimination" property for induction that once you want to apply said theorem to an actual concrete integer, you can unwind the induction a finite number of steps.
Z3 could solve this is 1 shot in principle. It is interesting to maybe stick to proof methods that are just guiding what should be doable in 1 shot.

Z3 won't like variable pow.

Simplest challenge problem
lim(n->inf, 1/n) = 0

```python
exp = Array("exp", IntSort(), ArraySort(RealSort(), RealSort())) # Array("cos", RealSort(), IntSort(), RealSort()) # returns a CReal
exp0def = ForAll([x],exp[0][x] == 1)
fact = lambda x: Real(x)
expsuccdef = QForAll([n,x], n > 0, exp[n][x] == x**n / fact(n) + exp[n-1][x]) # cosine is different on even odd. Yuck.

# expansion example
infer([exp_def], ForAll([x], exp[2][x] == 1 + x + x**2)) 

# comparative accuracy. Don't even fully expand
diff = infer([exp_def], ForAll([x], exp[2][x] - exp[1][x] == x**2 ))
infer([diff], QForAll([x], 0 <= x & x <= 1,  exp[2][x] - exp[1][x] <= 0.1))

```

    ---------------------------------------------------------------------------

    Z3Exception                               Traceback (most recent call last)

    /home/philip/Documents/philzook58.github.io/_drafts/2023-11-09-z3-itp.ipynb Cell 14 line 2
          <a href='vscode-notebook-cell:/home/philip/Documents/philzook58.github.io/_drafts/2023-11-09-z3-itp.ipynb#X50sZmlsZQ%3D%3D?line=0'>1</a> exp = Array("exp", IntSort(), ArraySort(RealSort(), RealSort())) # Array("cos", RealSort(), IntSort(), RealSort()) # returns a CReal
    ----> <a href='vscode-notebook-cell:/home/philip/Documents/philzook58.github.io/_drafts/2023-11-09-z3-itp.ipynb#X50sZmlsZQ%3D%3D?line=1'>2</a> exp0def = ForAll([x],exp[0][x] == 1)
          <a href='vscode-notebook-cell:/home/philip/Documents/philzook58.github.io/_drafts/2023-11-09-z3-itp.ipynb#X50sZmlsZQ%3D%3D?line=2'>3</a> fact = lambda x: Real(x)
          <a href='vscode-notebook-cell:/home/philip/Documents/philzook58.github.io/_drafts/2023-11-09-z3-itp.ipynb#X50sZmlsZQ%3D%3D?line=3'>4</a> expsuccdef = QForAll([n,x], n > 0, exp[n][x] == x**n / fact(n) + exp[n-1][x])


    File ~/.local/lib/python3.10/site-packages/z3/z3.py:4584, in ArrayRef.__getitem__(self, arg)
       4574 def __getitem__(self, arg):
       4575     """Return the Z3 expression `self[arg]`.
       4576 
       4577     >>> a = Array('a', IntSort(), BoolSort())
       (...)
       4582     '(select a i)'
       4583     """
    -> 4584     return _array_select(self, arg)


    File ~/.local/lib/python3.10/site-packages/z3/z3.py:4595, in _array_select(ar, arg)
       4593     _args, sz = _to_ast_array(args)
       4594     return _to_expr_ref(Z3_mk_select_n(ar.ctx_ref(), ar.as_ast(), sz, _args), ar.ctx)
    -> 4595 arg = ar.sort().domain().cast(arg)
       4596 return _to_expr_ref(Z3_mk_select(ar.ctx_ref(), ar.as_ast(), arg.as_ast()), ar.ctx)


    File ~/.local/lib/python3.10/site-packages/z3/z3.py:2354, in ArithSortRef.cast(self, val)
       2352     return IntVal(val, self.ctx)
       2353 if self.is_real():
    -> 2354     return RealVal(val, self.ctx)
       2355 if z3_debug():
       2356     msg = "int, long, float, string (numeral), or Z3 Integer/Real expression expected. Got %s"


    File ~/.local/lib/python3.10/site-packages/z3/z3.py:3208, in RealVal(val, ctx)
       3193 """Return a Z3 real value.
       3194 
       3195 `val` may be a Python int, long, float or string representing a number in decimal or rational notation.
       (...)
       3205 3/2
       3206 """
       3207 ctx = _get_ctx(ctx)
    -> 3208 return RatNumRef(Z3_mk_numeral(ctx.ref(), str(val), RealSort(ctx).ast), ctx)


    File ~/.local/lib/python3.10/site-packages/z3/z3core.py:2302, in Z3_mk_numeral(a0, a1, a2, _elems)
       2300 def Z3_mk_numeral(a0, a1, a2, _elems=Elementaries(_lib.Z3_mk_numeral)):
       2301   r = _elems.f(a0, _str_to_bytes(a1), a2)
    -> 2302   _elems.Check(a0)
       2303   return r


    File ~/.local/lib/python3.10/site-packages/z3/z3core.py:1505, in Elementaries.Check(self, ctx)
       1503 err = self.get_error_code(ctx)
       1504 if err != self.OK:
    -> 1505     raise self.Exception(self.get_error_message(ctx, err))


    Z3Exception: b'parser error'

```python
RealSeq = ArraySort(IntSort(), RealSort())
a = Const("a", RealSeq)
x,eps = Reals("x eps")
n,m = Ints("n m")
#convergent = define("convergant", Lambda([x], Exists([y], ForAll([n], x[n] == y))))

norm_bound, norm_bound_def = define("norm_bound", Lambda([x,eps], (x <= eps) & (-eps <= x)))
abs, abs_def = define("abs", Lambda([x], If(x >= 0, x, -x)))
lim, lim_def = define("lim", Lambda([a,x], 
               ForAll([eps], Exists([n], QForAll([m], m > n, norm_bound(x - a[m], eps))))))
# skolemize it probably.
n = Array("n", RealSort(), IntSort())
# convergence
lim, lim_def = define("lim", Lambda([a,x,n], 
               ForAll([eps], QForAll([m], m > n[eps], norm_bound[x - a[m], eps]))))

lim[Lambda([m], If(m >=0, 1/m, 0)), RealVal(0), Lambda([eps], 1/eps)]
```

    ---------------------------------------------------------------------------

    TypeError                                 Traceback (most recent call last)

    /home/philip/Documents/philzook58.github.io/_drafts/2023-11-09-z3-itp.ipynb Cell 20 line 9
          <a href='vscode-notebook-cell:/home/philip/Documents/philzook58.github.io/_drafts/2023-11-09-z3-itp.ipynb#X60sZmlsZQ%3D%3D?line=4'>5</a> #convergent = define("convergant", Lambda([x], Exists([y], ForAll([n], x[n] == y))))
          <a href='vscode-notebook-cell:/home/philip/Documents/philzook58.github.io/_drafts/2023-11-09-z3-itp.ipynb#X60sZmlsZQ%3D%3D?line=6'>7</a> norm_bound, norm_bound_def = define("norm_bound", Lambda([x,eps], (x <= eps) & (-eps <= x)))
          <a href='vscode-notebook-cell:/home/philip/Documents/philzook58.github.io/_drafts/2023-11-09-z3-itp.ipynb#X60sZmlsZQ%3D%3D?line=7'>8</a> lim, lim_def = define("lim", Lambda([a,x], 
    ----> <a href='vscode-notebook-cell:/home/philip/Documents/philzook58.github.io/_drafts/2023-11-09-z3-itp.ipynb#X60sZmlsZQ%3D%3D?line=8'>9</a>                ForAll([eps], Exists([n], QForAll([m], m > n, norm_bound(x - a[m], eps))))))
         <a href='vscode-notebook-cell:/home/philip/Documents/philzook58.github.io/_drafts/2023-11-09-z3-itp.ipynb#X60sZmlsZQ%3D%3D?line=9'>10</a> # skolemize it probably.
         <a href='vscode-notebook-cell:/home/philip/Documents/philzook58.github.io/_drafts/2023-11-09-z3-itp.ipynb#X60sZmlsZQ%3D%3D?line=10'>11</a> n = Array("n", RealSort(), IntSort())


    TypeError: 'ArrayRef' object is not callable

```python
# This is kind of bishop's definition of just picking 1/n for the modulus of convergence
harmonic_lin = define("linharm", Lambda([a,x], ForAll([eps], QForAll([m], m > 0, norm_bound(x - a[m], 1/m)))))
cauchy = define("cauchy", Lambda([a,n], ForAll([eps], QForAll([m], m > n[eps], norm_bound(a[m] - a[n], eps)))))

define("cauchy", Lambda([a,n], QForAll([eps, m], m > n[eps], norm_bound(a[m] - a[n], eps))))


R = DeclareSort("R")
eclass = Function("eclass", IntSeq, R) # Quotient by cauchy equivalence
QForAll([a,b], ForAll([n], norm_bound(a[n] - b[n]) <= 1/n),    
               eclass(a) == eclass(b) )



```

```python
#SortRef.__rshift__ = lambda self, other: ArraySort(self, other) # Nah bad idea. wrong associativty
def ArrowSort(*args):
    if len(args) == 1:
        return args[0]
    return ArraySort(args[0], ArrowSort(*args[1:]))
SortRef.__mul__ = lambda self, other: TupleSort(f"Pair_{self}_{other}", [self, other])[0]
IntSort() >> IntSort() >> IntSort()
IntSort() * IntSort()
ArrowSort(IntSort(), IntSort(), IntSort())
```

Array(Int, Array(Int, Int))

```python
# Open-closed induction. We can extend any point some epsilon out, and we can close any open ball back to closed.
def induct_real(P : Form) -> Thm:
    assert P.sort().name() == "Array"
    assert P.sort().domain() == RealSort()
    assert P.sort().range() == BoolSort()
    n = FreshConst(RealSort())
    eps = FreshConst(RealSort())
    hyp = P[0] & \
         ForAll([n], Exists([eps], P[n] & (eps > 0) > P[n + eps])) & \
         ForAll([n], ForAll([eps], P[x - eps] & (eps > 0) > P[x]))
    #------------------------------------------
    conc =  ForAll([n], P[n])
    return trust(hyp > conc)
# generalization to general topology?
```

```python
# https://math.stackexchange.com/questions/4202/induction-on-real-numbers
# https://arxiv.org/abs/1208.0973
induct_real = trust(QForAll([P], 
                QForAll([x],P[x] , Exists([y], y > x & P[y])) &
                QForAll([x,y], QForAll([y], y < x, P[y]), P[x])),  
                QForAll([x],x >= 0, P[x]))
```

```python
";(declare-datatypes ((Nat 0)) (((zero) (succ (pred Nat)))))"
smtlib = """
;(declare-datatypes () ((Nat (zero)))) ; (succ (pred Nat)))))
(declare-datatype Nat ((zero) (succ (pred Nat))))
;(declare-datatypes ((Nat 0)) (((zero) (succ (pred Nat)))))
(declare-fun add (Nat Nat) Nat)
(declare-fun x () Nat)
(assert (forall ((x Nat)) (= (add zero x) x)))
(assert (forall ((x Nat) (y Nat)) (= (add (succ x) y) (succ (add x y)))))
(assert (let ((a!1 (and (forall ((y Nat)) (= (add zero y) (add y zero)))
                (forall ((c!13 Nat))
                  (let ((a!1 (not (forall ((y Nat))
                                    (= (add c!13 y) (add y c!13)))))
                        (a!2 (forall ((y Nat))
                               (= (add (succ x) y) (add y (succ x))))))
                    (or a!1 a!2))))))
  (or (not a!1) (forall ((c!13 Nat) (y Nat)) (= (add c!13 y) (add y c!13))))))
(assert (not (forall ((x Nat) (y Nat)) (= (add x y) (add y x)))))
(check-sat)
"""

open("/tmp/peano.smt2", "w").write(smtlib)

```

    894

```python
!vampire /tmp/peano.smt2
```

    perf_event_open failed (instruction limiting will be disabled): Permission denied
    % Running in auto input_syntax mode. Trying SMTLIB2


    ^C
    28863 Aborted by signal SIGINT on /tmp/peano.smt2
    % ------------------------------
    % Version: Vampire 4.6.1 (commit af1735c99 on 2021-12-01 14:43:47 +0100)
    % Linked with Z3 4.8.13.0 f03d756e086f81f2596157241e0decfb1c982299 z3-4.8.4-5390-gf03d756e0
    % Termination reason: Unknown
    % Termination phase: Saturation
    
    % Memory used [KB]: 29551
    % Time elapsed: 24.705 s
    % ------------------------------
    % ------------------------------

# HOL

So HOL is supposed to be weaker than set theory but still very expressive.
See

- Andrews book
- HOL Light tutorial
- Gordon paper

```python
o = BoolSort()
i = DeclareSort("i")
def EQ(A,B):


TRUE = None
FALSE = None
```

# Set Theory

```python

# Zf
Set = DeclareSort("Set")
elem = Function("elem", Set, Set, BoolSort())
A,B,C,x,y,z = Consts("A B C x y z", Set) 

ax_emp = trust(Exists([A],ForAll([x], ~elem(B,A))))
ax_pair = trust(ForAll([A,B], Exists([C], ForAll([x], elem(x, C) == elem(x,A) | elem(x,B)))))
ax_ext = trust(ForAll([A,B], ForAll([x], elem(x,A) == elem(x,B)) == (A == B)))
ax_union = trust(ForAll([A], Exists([B], ForAll([x], elem(x,B) == Exists([y], elem(x,y) & elem(y,A))))))
def ax_sep(B,P):
    A = FreshConst(Set)
    return trust(Exists([A], ForAll([x], elem(x,A) == elem(x,B) & P(x))))

# ordered pairs

# injectivity theorem

```

```python
def extend(hyps,x,P, prefix):
    infer(hyps, Exists([x], P))
    s = FreshConst(Set, prefix=prefix)
    return s, trust(P.substitute(s, x))
```

# Ordinals

```python
# Constructive Real

# Z3 reals are more like algebraic numbers, not reals.
CReal = ArraySort(Nat, RealSort())
eq = Function("eq", CReal, CReal, BoolSort())
ax_eq = trust(ForAll([x,y], eq(x,y) == (ForAll([n], x[n] - y[n] < 1/n))
```

# Category

Topos Book
Scott Encoding using exists predicate.
Well formed as precondition.

```python
Arr = DeclareSort("Arr")
Ob = DeclareSort("Ob")
ex = Function("Ex", Arr, BoolSort())

f,g,h = Consts("f g h", Arr)
A,B,C = Consts("A B C", Ob)
comp = Function("comp", Arr, Arr, Arr)
id_ = Function("id", Ob, Arr)
dom = Function("dom", Arr, Ob)
cod = Function("cod", Arr, Ob)
z3.ExprRef.__lshift__ = lambda self, other: comp(self, other)
#ax_comp = trust(ForAll([f,g,h], comp(f,comp(g,h)) == comp(comp(f,g),h)))
ax_comp_assoc = trust(ForAll([f,g,h], f << (g << h) == (f << g) << h))
#ax_id_l = trust(ForAll([f,A], (cod(f) == A) > (id_(A) << f == f)))
#ax_id_r = trust(ForAll([f,A], (dom(f) == A) > (f << id_(A) == f)))
ax_id_l = trust(ForAll([f], id_(cod(f)) << f == f)) # inline the dom/cod
ax_id_r = trust(ForAll([f], f << id_(dom(f)) == f)) 
ax_cat = [ax_id_l, ax_id_r, ax_comp_assoc]

ax_dom_id = trust(ForAll([A], dom(id_(A)) == A))
ax_cod_id = trust(ForAll([A], cod(id_(A)) == A))
ax_ex_id = trust(ForAll([A], ex(id_(A))))
ax_ex_comp = trust(ForAll([f,g], ex(f << g) == (dom(f) == cod(g))))
ax_wff = [ax_dom_id, ax_cod_id, ax_ex_id, ax_ex_comp]

junk = Const("junk", Arr)
ax_junk = trust(ForAll([f], Implies(ex(f), f != junk))) # bidirectional?

wff_id_id = infer(ax_wff + ax_cat, ex(id_(A) << id_(A)) & (dom(id_(A) << id_(A)) == A) & (cod(id_(A) << id_(A)) == A))
wff_id_id
#infer(ax_cat + ax_wff + [wff_id_id], id_(A) << id_(A) == id_(A))

# sanity check
#infer(ax_cat + ax_wff, False)

monic, monic_def = define("monic", Lambda([f], ForAll([g,h], Implies(f << g == f << h, h == g))))
epic, epic_def = define("epic", Lambda([f], ForAll([g,h], Implies(g << f == h << f, h == g))))
```

```python

id_monic = infer(ax_cat + ax_wff + [monic_def], ForAll([A], monic[id_(A)]))
id_monic
```

    (-6531872273261288051, ForAll(A, monic!200[id(A)]))

```python
# pullback is universal square 
pullback = define("pullback", Lambda([f,g,h,k, univ], 
f << g == h << k & 
ForAll([x,y], Exists([univ], Implies(x << g == y << k, x == univ << g  & y == univ << k)))))
```

```python
infer(ax_cat + ax_wff + [monic_def], False)
```

    (declare-sort Arr 0)
    (declare-sort Ob 0)
    (declare-fun monic!89 () (Array Arr Bool))
    (declare-fun comp (Arr Arr) Arr)
    (declare-fun id (Ob) Arr)
    (declare-fun cod (Arr) Ob)
    (declare-fun dom (Arr) Ob)
    (declare-fun Ex (Arr) Bool)
    (assert (forall ((f Arr)) (= (comp (id (cod f)) f) f)))
    (assert (forall ((f Arr)) (= (comp f (id (dom f))) f)))
    (assert (forall ((f Arr) (g Arr) (h Arr)) (= (comp f (comp g h)) (comp (comp f g) h))))
    (assert (forall ((A Ob)) (= (dom (id A)) A)))
    (assert (forall ((A Ob)) (= (cod (id A)) A)))
    (assert (forall ((A Ob)) (Ex (id A))))
    (assert (forall ((f Arr) (g Arr)) (= (Ex (comp f g)) (= (dom f) (cod g)))))
    (model-add monic!89
               ()
               (Array Arr Bool)
               (lambda ((f Arr))
                 (forall ((g Arr) (h Arr))
                   (or (not (= (comp f g) (comp f h))) (= h g)))))
    



    ---------------------------------------------------------------------------

    AssertionError                            Traceback (most recent call last)

    /home/philip/Documents/philzook58.github.io/_drafts/2023-11-09-z3-itp.ipynb Cell 30 line 1
    ----> <a href='vscode-notebook-cell:/home/philip/Documents/philzook58.github.io/_drafts/2023-11-09-z3-itp.ipynb#X43sZmlsZQ%3D%3D?line=0'>1</a> infer(ax_cat + ax_wff + [monic_def], False)


    /home/philip/Documents/philzook58.github.io/_drafts/2023-11-09-z3-itp.ipynb Cell 30 line 3
         <a href='vscode-notebook-cell:/home/philip/Documents/philzook58.github.io/_drafts/2023-11-09-z3-itp.ipynb#X43sZmlsZQ%3D%3D?line=30'>31</a>     if res == z3.sat:
         <a href='vscode-notebook-cell:/home/philip/Documents/philzook58.github.io/_drafts/2023-11-09-z3-itp.ipynb#X43sZmlsZQ%3D%3D?line=31'>32</a>         print(s.model())
    ---> <a href='vscode-notebook-cell:/home/philip/Documents/philzook58.github.io/_drafts/2023-11-09-z3-itp.ipynb#X43sZmlsZQ%3D%3D?line=32'>33</a>     assert False,res
         <a href='vscode-notebook-cell:/home/philip/Documents/philzook58.github.io/_drafts/2023-11-09-z3-itp.ipynb#X43sZmlsZQ%3D%3D?line=34'>35</a> return trust(conc)


    AssertionError: unknown

```python

```

# Metatheory

Termination, confluence, progress, type preservation, consistency,

Abstract Binding Trees. Can we force Z3 to be unware of the binders by making it an uninterpreted sort with views?
Reminds me of the quotienting construction (like equivalent sequences of CReal). We make a new sort of the quotiented thing and an injecton function and a lift of some equvlaence relation on the domain to an actual equivalence over the quotient sort.
In this case alpha equivalence.

I had some ideas int smt.md about model checking these kinds of problems.

Z3 hoas? It didn't work right?

```python
# Krishnaswami https://semantic-domain.blogspot.com/2015/03/abstract-binding-trees.html?m=1
# https://www.cs.cmu.edu/~rjsimmon/15312-s14/hws/hw1update2-handout.pdf
Sort("Var")
abt = Sort("abt")
view = Datatype("view", "op", "lam", "var") # no app?
Function("into", )
Function("out",)

Function("subst", "Var", )

```

```python
from z3 import *
Term = DatatypeSort("Term") #, [("nil", Unit), ("cons", (Int, "List"))])
Term.constructor("Var", IntSort())
Term.constructor("App", [Term, Term])
Term.constructor("Const", IntSort())

```

    ---------------------------------------------------------------------------

    TypeError                                 Traceback (most recent call last)

    /home/philip/Documents/philzook58.github.io/_drafts/2023-11-09-z3-itp.ipynb Cell 45 line 3
          <a href='vscode-notebook-cell:/home/philip/Documents/philzook58.github.io/_drafts/2023-11-09-z3-itp.ipynb#X63sZmlsZQ%3D%3D?line=0'>1</a> from z3 import *
          <a href='vscode-notebook-cell:/home/philip/Documents/philzook58.github.io/_drafts/2023-11-09-z3-itp.ipynb#X63sZmlsZQ%3D%3D?line=1'>2</a> Term = DatatypeSort("Term") #, [("nil", Unit), ("cons", (Int, "List"))])
    ----> <a href='vscode-notebook-cell:/home/philip/Documents/philzook58.github.io/_drafts/2023-11-09-z3-itp.ipynb#X63sZmlsZQ%3D%3D?line=2'>3</a> Term.constructor("Var", IntSort())
          <a href='vscode-notebook-cell:/home/philip/Documents/philzook58.github.io/_drafts/2023-11-09-z3-itp.ipynb#X63sZmlsZQ%3D%3D?line=3'>4</a> Term.constructor("App", [Term, Term])
          <a href='vscode-notebook-cell:/home/philip/Documents/philzook58.github.io/_drafts/2023-11-09-z3-itp.ipynb#X63sZmlsZQ%3D%3D?line=4'>5</a> Term.constructor("Const", IntSort())


    TypeError: DatatypeSortRef.constructor() takes 2 positional arguments but 3 were given

### Nominal Sets

```python
Atom = DeclareSort("Atom")
#Perm = ArraySort(Atom, Atom)
swap = Function("swap", Atom, Atom, Perm)
mul(x,x) = id
mul(swap(a,b), swap(c,d)) = swap(b,a) * swap(c,d)
swap(a,b) == swap(b,a)
app(mul(x,y), z) = app(x, app(y, z))
app(swap(a,b), a) = b
app(swap(a,b), c) = c if a != c and b != c

app(swap(a,b),z) = y ==> z = app(swap(a,b), y)
f(p x, y, z) => p f(x,p y,p z) # equivariance.
p f (x, y , z) <=> f (p x, p y, p y)

fvar(t) = 
```

```python

```

# Internal Proofs

```python
Proof = DeclareSort("Proof")
Function("even", IntSort(), Proof, BoolSort()) # last argument style

index = Function("pindex", IntSort(), Proof)
infer = Function(  )

# SHould proofs be trees
Proof = DeclareSort("Proof")
Proof.constructor("axiom")
Proof.constructor("infer", [Proof, Proof])

# the proof that 2 bool expressions always evaluate to true.
Function("and", BoolSort(), BoolSort(), Proof, BoolSort())
Function("pand", Proof, Proof, Proof)

# Justification
Path = DatatypeSort("Path")
Cons()
path(x,y,P)

# dialectica
# lenses as tactics. Hmmm. scope discipline. Up down cntrol flow.
Function("implies", BoolSort(), Proof, )

```

# Notes

Hmm. Z3 ctx object. Should I be using tha somehow?
I can't controlis the user happens to add a recfundefinition to the local context that is bad.

sympy
calcium
z3
CAD
cvxpy maybe

What problems would be nice?
Deriving good expressions, not proving so much
float bounds
solution to diff eq accuracy.
operator algebra
integrals

Equation sets:

- integration rubi
- algebra of programming
- hlint
- textbook covers
  - vector calc
  - recurrences
- axiom macsyma
- catlab
- rewrite engine comp
- tptp ueq

# Notation

Many systems offer notation mechanisms.
Python gives you operator overloading of course, which gets you pretty far.
But sometimes maybe it's nice to parse strings or extend a DSL.
Lark is a parser generator library that is pretty great. In the cases where it's worth it (which are rare imo), can use Lark. Lark is also extensible, you can import grammars into other grammar. Subclassing the transformer then gives you the ability to add new notations.
f strings also can enable interesting quasiquotation strategies

# Nats

```python
from knuckledragger import *
# Peano Arithmetic

# Z3py adt of natural numbers
Nat = Datatype("Nat")
Nat.declare("zero")
Nat.declare("succ", ("pred", Nat))
Nat = Nat.create()
print(Nat.succ(Nat.zero))

# Peano
def induct(P : Form) -> Thm:
    print(P.sort())
    assert P.sort().name() == "Array"
    assert P.sort().domain() == Nat
    assert P.sort().range() == BoolSort()
    n = FreshConst(Nat)
    hyp = P[Nat.zero] & ForAll([n], P[n] > P[Nat.succ(n)])
    #------------------------------------------
    conc =  ForAll([n], P[n])
    return trust(hyp > conc)

x,y = Consts("x y", Nat)
add = Function("add", Nat, Nat, Nat)
zero_add = trust(ForAll([x], add(Nat.zero, x) == x))
succ_add = trust(ForAll([x,y], add(Nat.succ(x), y) == Nat.succ(add(x, y))))

P = Lambda([x], add(x,Nat.zero) == add(Nat.zero,x))

base = modus([], P[Nat.zero])
ind = modus([zero_add, succ_add], ForAll([x], P[x] > P[Nat.succ(x)]))
add_zero = modus([base,ind,induct(P)], ForAll([x], P[x]))
add_zero_prime = modus([zero_add, succ_add, induct(P)], ForAll([x], P[x]))


P = Lambda([x], ForAll([y], add(x,Nat.succ(y)) == Nat.succ(add(x,y))))
add_succ = modus([zero_add,succ_add, induct(P)], ForAll([x],P[x]))
comm_add = modus([zero_add, succ_add, add_zero, add_succ, induct(Lambda([x], ForAll([y], add(x,y) == add(y,x))))] ,
                  ForAll([x,y], add(x, y) == add(y, x)))

comm_add

def induct_int(P : Form) -> Thm:
    assert P.sort().name() == "Array"
    assert P.sort().domain() == IntSort()
    assert P.sort().range() == BoolSort()
    n = FreshConst(IntSort())
    hyp = P[0] & ForAll([n], P[n] > P[n - 1] & P[n + 1])
    #------------------------------------------
    conc =  ForAll([n], P[n])
    return trust(hyp > conc)
# https://math.stackexchange.com/questions/2659184/can-induction-be-done-to-prove-statements-for-integers


def induct_posint(P : Form) -> Thm:
    assert P.sort().name() == "Array"
    assert P.sort().domain() == IntSort()
    assert P.sort().range() == BoolSort()
    n = FreshConst(IntSort())
    hyp = P[0] & ForAll([n], (P[n] & n >= 0) > P[n + 1])
    #------------------------------------------
    conc =  ForAll([n], (n >= 0) > P[n])
    return trust(hyp > conc)
# extending with injection axioms into the Ints

def induct(P):
  # assert P.type == Nat -> Bool ?
  n = FreshConst(Nat)
  return ForAll(n, Implies(P(Nat.zero), Forall(n, Implies(P(n), P(Nat.succ(n))))), Forall(n, P(n)))

inj = Function("inj", Nat, IntSort())
n = FreshConst(Nat)
axioms = [
  inj(Nat.zero) == 0,
  ForAll(n, inj(Nat.succ(n)) == inj(n) + 1) # recursive definition of inj
]

theorem1 = ForAll(n, inj(n) >= 0)
theorem2 = ForAll(i, Implies(i >= 0, Exist(n, inj(n) == i)))
P = lambda x: 
x,y,n = Ints("x y n")
even, even_def = define("even", Lambda([x], Exists([y], x == y + y)))
odd, odd_def = define("odd", Lambda([x], Exists([y], x == y + y + 1)))

even0 = infer([even_def], even[0])
#ind = infer([even_def,odd_def], QForAll([n], even[n], odd[n+1]))
ind1 = infer([even_def,odd_def], ForAll([n], even[n] == odd[n+1]))
ind2 = infer([even_def,odd_def], ForAll([n], odd[n] == even[n+1]))
#ind = infer([even_def,odd_def, ind], QForAll([n], odd[n-1], even[n]))
#ind2 = infer([even_def,odd_def], QForAll([n], odd[n], Exists([y], n + 1 == (y + 1) + (y + 1))))
#ind3 = infer([even_def, odd_def, ind2], QForAll([n], odd[n], Exists([y], n + 1 == y + y)))
#even_or_odd = infer([even_def, odd_def], ForAll([n], even[n] | odd[n]))

# proof relevant predicates. The evidence is unsealed
# Can't really do a depndnt product / sum type easily.
# fst(p)
x,y,n,m = Ints("x y n m")
even_ev, even_ev_def = define("even", Lambda([x,y], x == y + y))
odd_ev, odd_ev_def = define("odd", Lambda([x,y], x == y + y + 1))

even0 = infer([even_ev_def], even_ev[0,0])
ind1 = infer([even_ev_def,odd_ev_def], ForAll([n,m], even_ev[n,m] == odd_ev[n+1,m]))
ind2 = infer([even_ev_def,odd_ev_def], ForAll([n,m], odd_ev[n,m] == even_ev[n+1,m+1]))

#even_ev_remove = infer([even_ev_def], QForAll([n,m], Exists([m], even_ev[n,m])), even[n])
# make definition the existential of even_ev
# even, even_def = define("even", Lambda([x], Exists([y], even_ev[x,y])))

# sklolem version
# Implies(even[n], even_ev[n,half[n]]
# Implies(odd[n], odd_ev[n,half[n] + 1]
half, half_def = define("half", Lambda([x], x / 2))
infer([half_def, even_ev_def, odd_ev_def], ForAll([n], even_ev[n, half[n]] | odd_ev[n, half[n]]))



```

# Tptp

TPTP is a useful source of axioms. I put some of them n the

<https://link.springer.com/article/10.1007/BF00243005> Hmm McCume point set topology

```python
from PyRes.fofspec import FOFSpec
from PyRes.saturation import SearchParams,ProofState
# https://github.com/eprover/PyRes/blob/master/pyres-fof.py
params = SearchParams()
print(params)

suppressEqAxioms = False
silent           = False
indexed          = True
proofObject      = False

params.delete_tautologies = True
params.forward_subsumption = True
params.backward_subsumption = True
#params.heuristics = GivenClauseHeuristics[optarg]
#params.literal_selection = LiteralSelectors[optarg]

problem = FOFSpec()
#problem.parse(file)
if not suppressEqAxioms:
    problem.addEqAxioms()

cnf = problem.clausify()
state = ProofState(params, cnf, silent, indexed)
res = state.saturate()
print(res)
print(problem.formulas)
from PyRes.lexer import Lexer
lexer = Lexer("foo(bar,Biz)")
print(lex)
from PyRes.formulas import parseFormula, parseWFormula
form = parseFormula(Lexer("foo(bar,Biz)"))
print(form.isUnary())
wform = parseWFormula(Lexer("fof(myformula, axiom, foo(bar,Biz))."))
wform
problem.addFormula(wform)
problem
problem.addEqAxioms()
problem
problem.clausify()

def ForAll(x,body):
    return Formula("!", x, body)
def And(*args):
    return Formula("&", )
Formula.__eq__ = lambda self, other: Formula("=", self, other)
Formula.__and__ = lambda self, other: Formula("&", self, other)

from PyRes.fofspec import FOFSpec
problem = FOFSpec()
problem.parse("./tptp/category/CAT001-0.ax")
problem
```

# Reals

Transfer principle schema.

Use Z3 reals.
Transfer anystatement to the hyperreals.

```python
from z3 import *

HR = Sort("HyperReal")
R = RealSort()

std = Function("std", HR, R)
inj = Function("inj", R, HR)

axiom(std(inj(x)) == x)

# eps?
# exists([eps], QForAll([x], x > 0, eps < std(x)))



def transfer(thm):
    #check theorem only talks about R.
    #replace R with HR
    #return as theorem

infer([], ForAll([x,y], x + y == y + x))

```

# CAS

Computer algebra calculations. Can I use sympy, sage etc. What kinds of computations might I want to verify?

Sums
Hypergeometric identities
Gosper's algorithm

The shadow calculus might be an acceptable stand in for calculus.

Concrete Mathematics
Iverson had a concrete mathematics book. That's intriguing

Σ

```
Σ = sum # ill advised but amusing.
Σ(range(10))
```

# Knuckledrag2

```python
import tempfile
import subprocess


class Term():
    def __eq__(self, rhs):
        return Eq(self, rhs)

    def __add__(self, rhs):
        return FunApp("+", [self, rhs])

    def __sub__(self, rhs):
        return FunApp("-", [self, rhs])

    def __and__(self, rhs):
        return And([self, rhs])

    def __le__(self, rhs):
        return Impl(rhs, self)

    def __gt__(self, rhs):
        return Impl(self, rhs)

    def __or__(self, rhs):
        return Or([self, rhs])

    def __invert__(self):
        return Not(self)

class Var(Term):
    def __init__(self, name):
        self.name = name

    def __str__(self):
        return self.name.upper()


def Vars(xs):
    return [Var(x) for x in xs.split()]


# class Sort(Enum):
#    NUMBER = auto()
#    SYMBOL = auto()
#    TERM = auto()

class FunApp(Term):
    def __init__(self, name, args):
        self.name = name
        self.args = args

    def __str__(self):
        args = ",".join(map(str, self.args))
        return "%s(%s)" % (self.name, args)

    def smt2(self):
        args = " ".join([arg.smt2() for arg in self.args])
        return "(%s %s)" % (self.name, args)

def Atom(name, args):
    return FunApp(name, args)

def Const(name):
    return FunApp(name, [])


def Consts(names):
    return [Const(name) for name in names.split()]


class Eq(FunApp):
    def __init__(self, lhs, rhs):
        super().__init__("Eq", [lhs, rhs])

    def __str__(self):
        return "(%s = %s)" % (str(self.args[0]), str(self.args[1]))


class And(FunApp):
    def __init__(self, vals):
        super().__init__("And", vals)

    def __str__(self):
        t = " & ".join([str(val) for val in self.args])
        return "(%s)" % t


class Or(FunApp):
    def __init__(self, vals):
        super().__init__("Or", vals)

    def __str__(self):
        t = " | ".join([str(val) for val in self.args])
        return "(%s)" % t


class Impl(FunApp):
    def __init__(self, hyp, conc):
        super().__init__("Impl", [hyp, conc])

    def __str__(self):
        return "(%s => %s)" % (str(self.args[0]), str(self.args[1]))

class BindApp(Term):
    def __init__(self, name, vars, body):
        self.name = name
        self.vars = vars
        self.body = body
    
class ForAll(BindApp):
    def __init__(self, vars, body):
        super().__init__("ForAll", vars, body)

    def __str__(self):
        vars = ",".join([str(var) for var in self.vars])
        return "(! [%s] : %s)" % (vars, str(self.body))


class Exists(BindApp):
    def __init__(self, vars, body):
        super().__init__("Exists", vars, body)

    def __str__(self):
        vars = ",".join([str(var) for var in self.vars])
        return "(? [%s] : %s)" % (vars, str(self.body))


class Not(FunApp):
    def __init__(self, val):
        super().__init__("Not", [val])

    def __str__(self):
        return "(~ %s)" % str(self.args[0])


class Solver():
    def __init__(self):
        self.facts = {}

    def add(self, x, name=None):
        if name == None:
            name = "myaxiom_%d" % len(self.facts)
        self.facts[name] = x

    def solve(self, execname="vampire"):
        facts = ["fof(%s, axiom, %s)." % (name, str(fact)) for name,
                 fact in self.facts.items()]
        print(facts)
        with tempfile.NamedTemporaryFile(suffix=".tptp") as fp:
            fp.writelines([stmt.encode() + b"\n" for stmt in facts])
            fp.flush()
            res = subprocess.check_output(
                [execname, fp.name])
            print(str(res))
        return res
        # writetotemp file. Call vampire.


class Proof(object):
    def __init__(self, formula, DO_NOT_USE_trusted=False, reason=None):
        if DO_NOT_USE_trusted:
            # I should deep copy formula and or/make formula immutable
            # make getter of formula for iy to be immutable
            # Could also serialize it here maybe? Strings are immutable.
            # Keep all of them. Check formula against immutable string.
            object.__setattr__(self, "formula", formula)
            object.__setattr__(self, "formula_str", str(formula))
            object.__setattr__(self, "reason", reason)
        else:
            raise Exception("Proof should only be produced via modus or axiom")

    def __setattr__(self, name, value):
        raise Exception("Attempted to set to immutable Proof object")

    def __delattr__(self, name):
        raise Exception("Attempted to delete from Proof object")

    def check_consistency(self):
        return str(self.formula) == self.formula_str

    def __repr__(self):
        return "Proof(%s)" % str(self.formula_str)


def axiom(formula):
    return Proof(formula, DO_NOT_USE_trusted=True)


def modus(conc, *hyps, sanity=True):
    # sanity checks: make sure hyps alone isn't inconsistent
    s = Solver()
    s.add(Not(conc))
    for hyp in hyps:
        assert isinstance(hyp, Proof)
        s.add(hyp.formula)
    res = s.solve(execname="vampire")
    if "SZS status Unsatisfiable" in res:
        return Proof(conc, DO_NOT_USE_trusted=True)
    else:
        raise Exception("modus failed")

'''
Schema

def nat_induction(P):
    return axiom(Implies(P(zero)  & ForAll([x], P(x) > P(x + 1)), ForAll([x], P(x))))


'''

'''
Backwards proof:

def Goal():
    def self():
        self.cbs = [] # callbacks
    def back(self,*hyps, sanity=True):
        prove(self.formula, hyps)

    def intros(self):

    def exists(self): ???

    def simp()
    def rewrite()

```
