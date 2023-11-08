---
layout: post
title: Metamath
---

Parsing is a proof obligation which is kind of cool / insane.
since fol is _embedded_, the distinction between sets and predicates is interestingly flimsy? Tarski S2
Disjointness and nominal logic?
A directed prolog of sorts. Proof checking as computation. You write which rules to resolve on, it adds the requirements to the goal stack

```prolog
d(X,Y) :- dif(X,Y).
a(axname, [path, X, Y]) :- d(), f(), f(), e(), e().
f(name, TypeCode, Var) --> []

a(nam, )
```

The RPN nature means we describe proof trees in a depth first manner. This is similar to bussproofs.

```metamath
l1 $e stuff1
l2 $e stuff2
myax $a$ mydude
```

is like asserting an inference rule

```metamath
l1 stuff      l2 stuff
----------------------- myax
      mydude
```

hoare in metamath

path proofs in metamath

```metamath
$c vert path edge a b c d e f $.
$v x y z $.
$f vert x $.
$f vert y $.
$f vert z $.

min $e edge x y $.
base-path $a path x y $.

maj $e path y z $.
trans-path $a path x z $.

verta $a vert a $.
vertb $a vert b $.
vertc $a vert c $.
$a vert d $.
$a vert e $.

edgeab $a edge a b $.
edgebc $a edge b c $.

pathac $p path a c $.

```

```bash
echo '
$c path edge vert 1 2 3 4 $.
$v x y z $.
vert1 $a vert 1 $.
vert2 $a vert 2 $.
vert3 $a vert 3 $.
edge12 $a edge 1 2 $.
edge23 $a edge 2 3 $.
vertx $f vert x $.
verty $f vert y $.
vertz $f vert z $.
edgexy $e edge x y $.
basepath $a path x y $.
path12 $p path 1 2 $=
  vert1 vert2 edge12 basepath $.
path23 $p path 2 3 $=
  vert2 vert3 edge23 basepath $.
pathyz $e path y z $.
transpath $a path x z $.
path13 $p path 1 3 $=
  edge12 vert1 vert2 vert3 path23 transpath $.

' > /tmp/path.mm
metamath 'read "/tmp/path.mm"' "verify proof *" "exit"
```

<https://drops.dagstuhl.de/opus/volltexte/2023/18384/pdf/LIPIcs-ITP-2023-9.pdf> automated theorem proving for metamath

metamath 0

<https://github.com/digama0/mm0>

metamath-lamp <https://github.com/digama0/mm0>

metamath book

metamath pcc
drat
datalog
prolog
congruence closure

[metamath python checker](https://github.com/david-a-wheeler/mmverify.py/blob/master/mmverify.py)

```python
# some excerpts from the above checker

# Tell me the types and I don't need the code
Label = str
Var = str
Const = str
Stmttype = typing.Literal["$c", "$v", "$f", "$e", "$a", "$p", "$d", "$="]
StringOption = typing.Optional[str]
Symbol = typing.Union[Var, Const]
Stmt = list[Symbol]
Ehyp = Stmt
Fhyp = tuple[Var, Const]
Dv = tuple[Var, Var]
Assertion = tuple[set[Dv], list[Fhyp], list[Ehyp], Stmt]
FullStmt = tuple[Stmttype, typing.Union[Stmt, Assertion]]


class Frame:
    """Class of frames, keeping track of the environment."""

    def __init__(self) -> None:
        """Construct an empty frame."""
        self.v: set[Var] = set()
        self.d: set[Dv] = set()
        self.f: list[Fhyp] = []
        self.f_labels: dict[Var, Label] = {}
        self.e: list[Ehyp] = []
        self.e_labels: dict[tuple[Symbol, ...], Label] = {}
        # Note: both self.e and self.e_labels are needed since the keys of
        # self.e_labels form a set, but the order and repetitions of self.e
        # are needed.

class FrameStack(list[Frame]):
    """Class of frame stacks, which extends lists (considered and used as
    stacks).
    """
    # ... .stuff ...
    pass

def apply_subst(stmt: Stmt, subst: dict[Var, Stmt]) -> Stmt:
    """Return the token list resulting from the given substitution
    (dictionary) applied to the given statement (token list).
    """
    result = []
    for tok in stmt:
        if tok in subst:
            result += subst[tok]
        else:
            result.append(tok)
    vprint(20, 'Applying subst', subst, 'to stmt', stmt, ':', result)
    return result

class MM:
    """Class of ("abstract syntax trees" describing) Metamath databases."""

    def __init__(self, begin_label: Label, stop_label: Label) -> None:
        """Construct an empty Metamath database."""
        self.constants: set[Const] = set()
        self.fs = FrameStack()
        self.labels: dict[Label, FullStmt] = {}
        self.begin_label = begin_label
        self.stop_label = stop_label
        self.verify_proofs = not self.begin_label

    # ... stuff ....

    def treat_step(self,
                   step: FullStmt,
                   stack: list[Stmt]) -> None:
        """Carry out the given proof step (given the label to treat and the
        current proof stack).  This modifies the given stack in place.
        """
        vprint(10, 'Proof step:', step)
        if is_hypothesis(step):
            _steptype, stmt = step
            stack.append(stmt)
        elif is_assertion(step):
            _steptype, assertion = step
            dvs0, f_hyps0, e_hyps0, conclusion0 = assertion
            npop = len(f_hyps0) + len(e_hyps0)
            sp = len(stack) - npop
            if sp < 0:
                raise MMError(
                    ("Stack underflow: proof step {} requires too many " +
                     "({}) hypotheses.").format(
                        step,
                        npop))
            subst: dict[Var, Stmt] = {}
            for typecode, var in f_hyps0:
                entry = stack[sp]
                if entry[0] != typecode:
                    raise MMError(
                        ("Proof stack entry {} does not match floating " +
                         "hypothesis ({}, {}).").format(entry, typecode, var))
                subst[var] = entry[1:]
                sp += 1
            vprint(15, 'Substitution to apply:', subst)
            for h in e_hyps0:
                entry = stack[sp]
                subst_h = apply_subst(h, subst)
                if entry != subst_h:
                    raise MMError(("Proof stack entry {} does not match " +
                                   "essential hypothesis {}.")
                                  .format(entry, subst_h))
                sp += 1
            for x, y in dvs0:
                vprint(16, 'dist', x, y, subst[x], subst[y])
                x_vars = self.fs.find_vars(subst[x])
                y_vars = self.fs.find_vars(subst[y])
                vprint(16, 'V(x) =', x_vars)
                vprint(16, 'V(y) =', y_vars)
                for x0, y0 in itertools.product(x_vars, y_vars):
                    if x0 == y0 or not self.fs.lookup_d(x0, y0):
                        raise MMError("Disjoint variable violation: " +
                                      "{} , {}".format(x0, y0))
            del stack[len(stack) - npop:]
            stack.append(apply_subst(conclusion0, subst))
        vprint(12, 'Proof stack:', stack)
```
