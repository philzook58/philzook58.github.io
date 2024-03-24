---
date: 2024-03-24
title: "Knuckledragger 2: ATP for Python ITP"
---

Knuckledragger is the moniker I've given to an approach and [library](https://github.com/philzook58/knuckledragger) I'm developing to do interactive theorem proving in python with the heavy lifting done by pre existing automated solvers.

I intend to match the base formalism of my system to what the automated solvers offer. This hopefully avoids some impedance mismatch that occurs in sledgehammer systems.

The reason to use python is because it is available everywhere and has libraries for everything. It already has an excellent interactive ecosystem in the form of jupyter notebooks and you can easily standup web demos in the form of links to google collab

That there isn't a good library already in python for unification, lambda evaluation, term indexing is somewhat mysterious to me.

I've tried to avoid having much code. By [piggybacking on pyz3's ast](https://www.philipzucker.com/python-itp/) you can go pretty far. But there are limitations and at a certain point this is an awkward design. I'm not sure z3's support of quantifier reasoning is complete enough to go the distance.

There are another older class of solver beside SMT. Roughly these are the resolution and superposition provers that compete in the [CASC](https://tptp.org/CASC/) automated reasoning competition. Two prominent systems are [vampire](https://vprover.github.io/) and [eprover](https://github.com/eprover/eprover). These solvers are saturation style, inferring more and more theorems until they find the goal. In this respect they are reminiscent of datalog and egraph saturation. This also more closely matches the definitions of logical reasoning as the minimal set of syntax reachable under inference rules from axioms. Most importantly, even though I usually poo poo this, the solvers chase completeness for their inference.

# Terms

For the purposes of a library, it is worth going verbose to offer more functionality. The lightest weight term type in python is a string tagged tuple. But really, for clarity, frozen dataclasses are quite nice. You get a lot of functionality for free and it is less weird. The weirder the library I build, probably the less people will use it.

Some core datatypes you'll see in theorem proving developments are variables and function symbols. A function symbol with no arguments is called a constant.

Variables represents implicitly universally quantified pieces of statements. Like `f(f(X)) = f(X)` is the statement that `f` is idempotent. If we had quantifiers, this would be expressed as `forall x, f(f(x)) = f(x)`. There is no law that logic must contain quantifiers.

I specialized out `Eq` because I want it to print infix, basically it is still just a 2-arity function symbol. A very special one that the solvers have a lot of support for.

```python
from dataclasses import dataclass
from typing import Tuple

@dataclass(frozen=True)
class Term:
    pass

@dataclass(frozen=True)
class Var(Term):
    name: str
    def __repr__(self):
        return self.name.title()
    def vars(self):
        return {self}

@dataclass(frozen=True)
class Fn(Term):
    name: str
    args: tuple[Term, ...]
    def __eq__(self : Term, other : Term):
        return Eq(self, other)
    def vars(self):
        return {v for a in self.args for v in a.vars()}
    def __repr__(self):
        return f"{self.name}({', '.join(map(str, self.args))})"

@dataclass(frozen=True)
class Eq(Term):
    lhs: Term
    rhs: Term
    def __repr__(self):
        return f"{self.lhs} = {self.rhs}"
    def vars(self):
        return self.lhs.vars() | self.rhs.vars()
```

```python
# helpers
def Vars(names):
    return [Var(name) for name in names.split()]
def Function(name):
    return lambda *args: Fn(name, args)
def Const(name):
    return Fn(name, ())
def Consts(names):
    return [Const(name) for name in names.split()]
```

## Sequents

This setup is sparser than that is typical in first order logic, where I'd also have connectives like `and` and `or`.

This is somewhat inspired by my understanding of the underpinnings of [Isabelle](https://isabelle.in.tum.de/). In isabelle, the base theory (Pure) let's you take sequents and unify them together to get new sequents. What we're doing here is a similar thing, but now we can discharge the unification obligation plus some search to the ATP.

I could equally have called the following a clause. The hypotheses are the negative literals and the conclusions are the positive literals.

I find it a very interesting perspective to not consider these automated theorem provers as classical first order predicate logic reasoning, but instead as operating at various levels of metalogic. The resolution rule is itself constructing partial proof trees. Each clause is a sequent judgement. Perhaps this has something to do with multiple conclusion logic <https://en.wikipedia.org/wiki/Multiple-conclusion_logic>

```python
@dataclass(frozen=True)
class Sequent():
    hyps: tuple[Term,...]
    concs: tuple[Term,...]

    def __repr__(self):
        return f"{list(self.hyps)} |- {list(self.concs)}"
    def fof(self):
        vars = {v for t in self.hyps for v in t.vars()} | {v for t in self.concs for v in t.vars()}
        if len(self.hyps) == 0:
            return f"![{','.join(map(repr,vars))}] : ({' & '.join(map(repr,self.concs))})"
        return f"![{','.join(map(repr,vars))}] : ({' & '.join(map(repr,self.hyps))} => {' & '.join(map(repr,self.concs))})"
    def cnf(self):
        if len(self.hyps) == 0:
            return " | ".join(map(repr,self.concs))
        else:
            forms = [f"~{h}" for h in self.hyps]
            forms.extend(map(repr,self.concs))
            return " | ".join(forms)
            #return f"{' | '.join(self.concs)} | {' | '.join(hyps)}"

```

# Packaging Eprover

I recently tried an experiment in packaging eprover for easy installation and use from. I built a version using [cosmopolitan libc](https://github.com/jart/cosmopolitan) which produces a dat binary that works on linux, windows, mac, x86_64 or aarch64. Then I just included the binary in the repo. I needed to fiddle with a couple eprover makefiles to make the usage of cc, ar, ranlib no longer hardcoded, but otherwise it was fairly painless.

Then I copied the binary, put it in my python package, committed it to the git repo, and added a line to my pyproject.toml stating I have extra data files. The `__init__.py` offers the path of this binary because it already can ask the `__file__` magic variable where itself is.

The repo for this is here. <https://github.com/philzook58/pyeprover>
I did the same thing for vampire, but did not compile using cosmopolitan. <https://github.com/philzook58/pyvampire>

Anyway, long story short is the following line should just work and then `eprover.run(["myfile.p])` can call the solver.

```python
! pip install git+https://github.com/philzook58/pyeprover
```

# Proofs and Theorems

This is a variation of my proof data structure. There are different approaches possible to this. The important thing is you need a strong distinction between formulas and proven theorems. Here they are distinct because the `Theorem` is an index into a hidden `__proof_db` data structure that actually holds the formula/sequent.

The two ways of controlling the db are `assume` and `infer`. Assume let's you just add stuff. The point is not to prevent you from tossing in axioms if you want. The point is to allow you to distinguish between things that follow from deduction vs axioms.

`infer` calls eprover. It takes in _`Theorem`_ hypotheses and a `Sequent` conclusion you want to prove. If it succeeds, it returns a `Theorem` pointing to the `Sequent` proven.

It turns the hypotheses given into `cnf` TPTP formulas. It turns the conclusion info a `fof` formula, because `cnf` does not support the `conjecture` clause type and I don't want to skolemize and stuff if the solver already does this.

Since I hold pointers to the previous theorems in the proof_db, it really is a proof data structure representing some kind of proof dag. Optionally, I can record the output of eprover, which contrains a lower tptp proof info.

```python
import eprover
from typing import Union
from dataclasses import dataclass

class ProofDB():
    def __init__(self):
        self.__proofdb = []
    def last_theorem(self):
        return Theorem(len(self.__proofdb) - 1, self)
    def assume(self, sequent : Union[Sequent, Term]):
        if isinstance(sequent,Term):
            sequent = Sequent((), [sequent])
        assert isinstance(sequent, Sequent)
        self.__proofdb.append((sequent, "assume"))
        return self.last_theorem()
    def infer(self, hyps: list["Theorem"], conc: Union[Sequent, Term], timeout=1.0, save_proof=False) -> Sequent:
        # could be neat to make hyps optional and just toss proof_db to the solver if hyps=None
        assert all(isinstance(hyp, Theorem) for hyp in hyps)
        if isinstance(conc,Term):
            conc = Sequent((), [conc])
        with open("/tmp/myfile.p", "w") as f:
            for hyp in hyps:
                f.write(f"cnf(thm{hyp.index},axiom, {hyp.cnf()}).\n")
            f.write(f"fof(goal, conjecture, {conc.fof()}).\n")
        res = eprover.run( ["/tmp/myfile.p"], timeout=timeout, capture_output=True)
        if "SZS status Theorem" not in res.stdout.decode("utf-8"):
            raise Exception(f"Proof failed \n{hyps}\n----------------(eprover)\n{conc}\n", res.stdout.decode("utf-8")) 
        if save_proof:
            self.__proofdb.append((conc, ("infer", hyps, res.stdout)))
        else:   
            self.__proofdb.append((conc, ("infer", hyps)))
        return self.last_theorem()
    def __getitem__(self, key):
        return self.__proofdb[key]
    def __len__(self):
        return len(self.__proofdb)

# It isn't persay such an issue that theorem's constructor is not protected because the proof db holds the only reference.
@dataclass(frozen=True)
class Theorem():
    index: int
    proofdb: ProofDB
    def formula(self):
        return self.proofdb[self.index][0]
    def cnf(self):
        return self.formula().cnf()
    def __repr__(self):
        return f"Theorem({self.formula()})"
```

Some example usage. A simple involutive problem

```python
X,Y,Z,A,B,C = Vars("X Y Z A B C")
f = Function("f")

db = ProofDB()

print(f"{f(f(X)) == f(X)=}")
print(f"{type(f(f(X)))=}")
involute_f = db.assume(f(f(X)) == f(X))
print(f"{involute_f=}")
print(all(list(isinstance(h, Theorem) for h in [involute_f])))
thm1 = db.infer([involute_f] , f(f(f(f(X)))) == f(X))
#thm2 = db.infer([involute_f],  f(X) == X)


```

    f(f(X)) == f(X)=f(f(X)) = f(X)
    type(f(f(X)))=<class '__main__.Fn'>
    involute_f=Theorem([] |- [f(f(X)) = f(X)])
    True

Two simple theorems of group theory

```python
mul = Function("mul")
inv = Function("inv")
e = Const("e")

db = ProofDB()
right_inv = db.assume(mul(X, inv(X)) == e)
right_id = db.assume(mul(X, e) == X)
assoc = db.assume(mul(mul(X, Y), Z) == mul(X, mul(Y, Z)))

group_ax = [right_inv, right_id, assoc]

left_inv = db.infer(group_ax, mul(inv(X), X) == e)
left_id = db.infer(group_ax, mul(e, X) == X)
#comm = db.infer(group_ax, mul(X, Y) == mul(Y, X))
print(left_inv, left_id)

```

    Theorem([] |- [mul(inv(X), X) = e()]) Theorem([] |- [mul(e(), X) = X])

# Bits and Bobbles

Next I probably want the typed form of tptp supported and it is especially appealing to use `thf` which supports lambdas.

I wonder if I'm inching towards just building python versions of everything. Unification, simple resolution provers. We'll see. It's nice to have that stuff in the library if I do.

I probably also should just make dataclasses for special logical formula constructos like ForAll, Exists, And, Or, Implies, etc.

HOLpy is a tour de force. They should've made it a library though. Making their own fronted seems like a bad battle to pick, but what do I know.

Isabelle is so good.

There is probably a clean prolog version of this. asserta keyed theorems to a proof_db protected by assume/infer predicates. Lambda prolog and Amy Felty's tutorial. I'm not sure why I am unaware of something like this in the modern prolog community. The new python interop

```python
# peano
db = ProofDB()
N, M = Vars("N M")

# definition of nats
zero = Const("zero")
succ = Function("succ")
succ_inject =   db.assume(Sequent([succ(N) == succ(M)], [N == M]))
succ_distinct = db.assume(Sequent([succ(N) == zero], []))
# induction without quantifiers PRA style
def induction(n, formula):
    base = db.infer([], subst(formula, n, zero))
    step = db.infer([], Sequent([formula], [subst(formula, n, succ(n))]))
    return db.assume(formula)
# definition of plus
plus = Function("plus")
db.assume(plus(zero, N) == N)
plus = Function("plus")
db.assume(plus(succ(N), M) == succ(plus(N, M)))
#induction(N, plus(zero, N) == N)

```

```python
# set theory
empty = Const("empty")
def comprehension(n, formula):
    pass
```

```python
# adts. Painful in untyped. tptp doesn't have support?
List = Function("list")

list_constuct = db.assume([List(L)], [L == cons(hd(L),tl(L)), L == nil])

hd_cons = db.assume([List(Y)], [ hd(cons(X,Y)) == X]) # injectivity
tl_cons = db.assume([List(Y)], [ tl(cons(X,Y)) == Y])

#db.assume([List(X), List(Y), X == Y], [hd(X)])

```

    ---------------------------------------------------------------------------

    NameError                                 Traceback (most recent call last)

    Cell In[24], line 3
          1 List = Function("list")
    ----> 3 list_constuct = db.assume([List(L)], [L == cons(hd(L),tl(L)), L == nil])
          5 hd_cons = db.assume([List(Y)], [ hd(cons(X,Y)) == X]) # injectivity
          6 tl_cons = db.assume([List(Y)], [ tl(cons(X,Y)) == Y])


    NameError: name 'L' is not defined

Typed terms.
It is nice / good sanity checking to give terms types.
It also gives us access to intrinsic reasoning about ints etc.

```python
from dataclasses import dataclass
class Type:
    pass

@dataclass(frozen=True)
class STVar(Type):
    name: str

@dataclass(frozen=True)
class SVar(Type):
    name: str

@dataclass(frozen=True)
class TConst(Type):
    name: str
    args: tuple[Type] = ()

def TFun(*args):
    if len(args) == 1:
        return args[0]
    else:
        return TConst('->', (args[0], TFun(*args[1:])))


BoolType = TConst("bool")
NatType = TConst('nat')
IntType = TConst('int')
RealType = TConst('real')
```
