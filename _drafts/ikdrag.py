from dataclasses import dataclass, replace, field
from typing import Optional, Callable
import pprint
import subprocess
import threading


from functools import singledispatch


@dataclass(frozen=True, slots=True)
class Decl:
    name: str
    arity: int
    bound: Optional[Callable[["Term"], "Term"]] = (
        None  # Revert to Callable? Sometimes should be Term
    )
    # binds: int
    is_var: bool = False
    # is_prop ?  kind of special. Forall p, p should not be allowed
    # call_prop whether call should return a prop?

    def __post_init__(self):
        if self.is_var and not self.name[0].isupper():  # or self.name[0] == "_"):
            raise ValueError("Variable not capitalized", self)
        elif not self.is_var and self.name[0].isupper():
            raise ValueError("Constant cannot be capitalized")

    def __call__(self, *args: "Term") -> "Term":
        assert (
            len(args) == self.arity
        ), f"Expected {self.arity} arguments, got {len(args)}"
        return Term(self, args)

    @property
    def defn(self) -> "Proof":
        return defns[self]

    @property
    def contract(self) -> "Proof":
        return contracts[self]

    @property
    def is_quantifier(self) -> bool:
        return self is ForAll0 or self is Exists0


class PDecl(Decl):
    def __call__(self, *args: "Term") -> "PTerm":
        assert (
            len(args) == self.arity
        ), f"Expected {self.arity} arguments, got {len(args)}"
        return PTerm(self, args)


# Registries
defns: dict[Decl, "Proof"] = {}
contracts: dict[Decl, "Proof"] = {}


And0 = PDecl("&", 2)
Or = PDecl("|", 2)
Implies = PDecl("=>", 2)
Not = PDecl("~", 1)
Iff = PDecl("<=>", 2)
Eq = PDecl("=", 2)
NEq = PDecl("!=", 2)
Add = Decl("add", 2)
Sub = Decl("sub", 2)
Mul = Decl("mul", 2)
Neg = Decl("neg", 1)
Div = Decl("div", 2)
Pow = Decl("pow", 2)
LT = PDecl("lt", 2)
LE = PDecl("le", 2)
ForAll0 = PDecl("forall", 2)
Exists0 = PDecl("exists", 2)
Call = Decl("call", 2)  # app. Sometimes PDecl?


@dataclass(frozen=True, slots=True)
class Term:
    decl: Decl
    args: tuple["Term", ...]

    def __post_init__(self):
        assert self.decl.is_quantifier or all(
            isinstance(a, Term) for a in self.args
        ), self

    def eq(self, other: "Term") -> bool:
        assert self.decl.name not in ["exists", "forall"]  # Todo
        return self.decl == other.decl and all(
            s.eq(o) for s, o in zip(self.args, other.args)
        )

    @property
    def defn(self) -> "Proof":
        return self.decl.defn

    @property
    def contract(self) -> "Proof":
        return self.decl.contract

    def __add__(self, other: "Term") -> "Term":
        # add is AC on the nose
        return Add(self, other)

    def __sub__(self, other: "Term") -> "Term":
        return Sub(self, other)

    def __mul__(self, other: "Term") -> "Term":
        # mul is AC on the nose. Don't use it if you don't want that.
        return Mul(self, other)

    def __truediv__(self, other: "Term") -> "Term":
        return Div(self, other)

    def __pow__(self, other: "Term") -> "Term":
        return Pow(self, other)

    def __eq__(self, other: "Term") -> "Term":
        return Eq(self, other)

    def __ne__(self, other: "Term") -> "Term":
        return NEq(self, other)

    def __lt__(self, other: "Term") -> "Term":
        return LT(self, other)

    def __neg__(self) -> "Term":
        return Neg(self)

    def __call__(self, *args):
        assert len(args) > 0
        if len(args) == 1:
            return Call(self, args[0])
        else:
            return Call(self, args[0])(*args[1:])

    def __str__(self) -> str:
        return self.tptp()

    def tptp(self) -> str:
        if self.decl.name in ["&", "|", "=>", "<=>", "=", "!="]:
            assert len(self.args) == 2
            return f"({self.args[0]} {self.decl.name} {self.args[1]})"
        match self.decl.name:
            case "forall":
                return f"![{', '.join(arg.tptp() for arg in self.args[0])}]: {self.args[1]}"
            case "exists":
                return f"?[{', '.join(arg.tptp() for arg in self.args[0])}]: {self.args[1]}"
        if self.decl.arity == 0:
            return self.decl.name
        else:  # "~" is probably ok?
            return f"{self.decl.name}({', '.join(arg.tptp() for arg in self.args)})"

    def fvs(self) -> set["Term"]:
        # free variables in the expression
        if self.decl.is_quantifier:
            return self.args[1].fvs() - set(self.args[0])
        elif self.decl.is_var:
            return {self}
        else:
            return set().union(*(arg.fvs() for arg in self.args))

    def decls(self) -> set[Decl]:
        decls = set()
        todo = [self]
        while todo:
            t = todo.pop()
            decl = t.decl
            if decl.is_quantifier:
                todo.append(t.args[1])
            else:
                decls.add(decl)
                todo.extend(t.args)
        return decls


class PTerm(Term):
    def __eq__(self, other: "PTerm") -> bool:
        return Iff(self, other)


def And(*args: PTerm) -> "PTerm":
    if len(args) == 0:
        return true
    elif len(args) == 1:
        return args[0]
    else:
        return Term(And0, (args[0], And(*args[1:])))


def ForAll(vars: list["Term"], *hyp_conc: PTerm) -> PTerm:
    assert len(hyp_conc) >= 1
    hyp_conc = list(hyp_conc)
    for v in vars:
        assert v.decl.is_var
        if v.decl.bound is not None:
            hyp_conc = [v.decl.bound(v)] + hyp_conc
    if len(hyp_conc) == 1:
        return Term(ForAll0, (tuple(vars), hyp_conc[0]))
    elif len(hyp_conc) == 2:
        return Term(ForAll0, (tuple(vars), Implies(hyp_conc[0], hyp_conc[1])))
    else:
        return Term(ForAll0, (tuple(vars), Implies(And(*hyp_conc[:-1]), hyp_conc[-1])))


def Exists(vars: list["Term"], *hyp_conc) -> PTerm:
    assert len(hyp_conc) >= 1
    hyp_conc = list(hyp_conc)
    for v in vars:
        assert v.decl.is_var
        if v.decl.bound is not None:
            hyp_conc = [v.decl.bound(v)] + hyp_conc
    return Term(Exists0, (tuple(vars), And(*hyp_conc)))


def Const(name: str, sort: Decl = None) -> Term:
    decl = Decl(name, 0)
    t = decl()
    if sort is not None:
        contracts[decl] = axiom(sort(t))
    return t


def Consts(names: str, sort: Decl = None) -> list[Term]:
    return [Const(name, sort) for name in names.split()]


def Predicate(name: str, arity: int) -> PDecl:
    return PDecl(name, arity)


def Function(name: str, *sorts) -> Decl:
    assert len(sorts) >= 2
    global contracts
    f = Decl(name, len(sorts) - 1)
    args = [Var("X" + str(i), bound=bound) for i, bound in enumerate(sorts[:-1])]
    contracts[f] = axiom(ForAll(args, sorts[-1](f(*args))))
    return f


true = PDecl("$true", 0)()
false = PDecl("$false", 0)()


def Var(name: str, bound=None) -> Term:
    return Term(Decl(name, 0, is_var=True, bound=bound), ())


def Vars(names: str, bound=None) -> list[Term]:
    return [Var(name, bound) for name in names.split()]


@dataclass(frozen=True, slots=True)
class Proof:
    thm: PTerm
    reasons: list[object]

    def __repr__(self) -> str:
        return "|- " + str(self.thm)

    def __call__(self, *args: "Term") -> "Proof":
        # instantiate a universally quantified theorem with specific terms
        assert (
            self.thm.decl.name == "forall"
        ), f"Expected forall, got {self.thm.decl.name}"
        assert len(args) == len(
            self.thm.args[0]
        ), f"Expected {len(self.thm.args[0])} arguments, got {len(args)}"
        subst = dict(zip(self.thm.args[0], args))
        new_thm = substitute(self.thm.args[1], subst)
        return Proof(new_thm, self.reasons + [args])


def axiom(p: PTerm) -> Proof:
    # Ya need axioms. What can I say
    assert (
        len(p.fvs()) == 0
    ), f"Expected closed term, got {p}, free variables: {p.fvs()}"
    return Proof(p, reasons=["axiom"])


def is_positive(t: PTerm) -> bool:
    if t.decl.is_quantifier:
        if t.decl.name == "forall":
            return False
        elif t.decl.name == "exists":
            return is_positive(t.args[1])
    name = t.decl.name
    match name:
        case "and":
            return is_positive(t.args[0]) and is_positive(t.args[1])
        case "or":
            return is_positive(t.args[0]) and is_positive(t.args[1])
        case "imp" | "not" | "iff" | "neq":
            return False
        case "eq":
            return True
        case _:
            return True


def is_coherent(t: PTerm) -> bool:
    # Allow some nesting of implies, since should be curryable.
    if t.decl.is_quantifier:
        if t.decl.name == "forall":
            return is_coherent(t.args[1])
        elif t.decl.name == "exists":
            return is_positive(t.args[1])
        else:
            raise ValueError("Unknown quantifier", t.decl.name)
    name = t.decl.name
    match name:
        case "imp":
            return is_positive(t.args[0]) and is_coherent(t.args[1])
        case "neq":
            return True
        case "eq":
            return True
        case "and" | "or" | "iff":
            return is_positive(t.args[0]) and is_positive(t.args[1])
        case "not":
            return is_positive(t.args[0])
        case _:
            return True


# assert is_coherent(ForAll([a, b], b > zero, b + (-a) + (-b) == -a))
# assert not is_coherent(ForAll([a, b], Not(b > zero), b + (-a) + (-b) == -a))


class VampirePool:
    def _make_proc(self):
        return subprocess.Popen(
            [
                "vampire",
                "--input_syntax",
                "tptp",
                # "--time_limit",
                # "1",
            ],
            stdout=subprocess.PIPE,
            stdin=subprocess.PIPE,
        )

    def __init__(self, N=5):
        self.index = 0
        self.procs = [self._make_proc() for _ in range(N)]
        self.lock = threading.Lock()

    def get_proc(self):
        with self.lock:
            proc = self.procs[self.index]
            self.procs[self.index] = self._make_proc()
            self.index = (self.index + 1) % len(self.procs)
        return proc


_vpool = VampirePool()

vampire_binary = "/home/philip/Documents/solvers/vampire/build/vampire"
# (is_intuitionistic, command, success_string)
# replace the path with wherever you put nanocopi
# If you aren't doing intuitionistic logic, use vampire / eprover.
solvers = {
    "nanocopi": (
        True,
        [
            "swipl",
            "-O",
            "-g",
            "assert(prolog(swi)),assert(proof(none)), asserta(logic(intu)), ['/home/philip/Downloads/nanoCoP-i-HT/nanocopi_main.pl'], call_with_time_limit(1,nanocopi_main('/tmp/prob.p',[cut,comp(6)],_)), halt",
        ],
        "is a intu Theorem",
    ),
    "eprover": (
        False,
        [
            "eprover-ho",
            "--auto",
            "--tstp-in",
            "--tstp-out",
            "--output-level=0",
            "/tmp/prob.p",
        ],
        "SZS status Theorem",
    ),
    "vampire": (
        False,
        [
            vampire_binary,
            "--input_syntax",
            "tptp",
            "--time_limit",
            "1",
            "--proof",
            "off",
            "/tmp/prob.p",
        ],
        "% SZS status Theorem",
    ),
    "z3": (
        False,
        [
            "z3",
            "-tptp",
            "/tmp/prob.p",
        ],
        "SZS status Theorem",
    ),
}


def prove0(p: Term, by=[], solver="eprover") -> Proof:
    assert isinstance(p, Term), f"Expected Term, got {p}"
    assert (
        len(p.fvs()) == 0
    ), f"Expected closed term, got {p}, free variables: {[str(v) for v in p.fvs()]}"
    for i, b in enumerate(by):
        assert isinstance(b, Proof), f"Expected Proof, got {b}"
    with open("/tmp/prob.p", "w") as f:
        for i, b in enumerate(by):
            f.write(f"fof(ax{i}, axiom, {b.thm.tptp()}).\n")
        f.write(f"fof(goal, conjecture, {p.tptp()}).\n")
        f.flush()
    (is_intu, cmd, succcess_string) = solvers.get(solver)
    if not (
        all(is_coherent(b.thm) for b in by) and is_coherent(p)
    ):  # check if classical prover is ok on fragment
        raise ValueError(
            f"Cannot use {solver} on non-coherent terms. {[t for t in by if not is_coherent(t.thm)]} and {p if not is_coherent(p) else None}"
        )
    res = subprocess.run(
        cmd,
        capture_output=True,
        text=True,
        timeout=2,
    )
    if succcess_string in res.stdout:
        return Proof(p, by)
    else:
        raise ValueError(
            f"Failed to prove {p} with by\n{pprint.pformat(by)}, result: {res.stdout}"
        )


def define(name: str, args: list[Term], body, sort=None, ho=False):
    global defns
    f = Decl(name, len(args))
    if ho:
        f = f()  # make a const so that f(*args) uses explicit call
    if len(args) == 0:
        defn = Proof(f() == body, reasons=["define"])
    else:
        defn = Proof(ForAll(args, f(*args) == body), reasons=["define"])
    if ho:
        defns[f.decl] = defn
    else:
        defns[f] = defn
    return f


@singledispatch
def lit(x) -> Term:
    raise ValueError("Cannot support x", x)


@lit.register
def _(x: bool) -> Term:
    return true if x else false


# Would it be nice to use binary / decimal lists?
@lit.register
def _(x: int):
    return Const("d" + str(x))


# set?
@lit.register
def _(x: list) -> Term:
    if len(x) == 0:
        return Const("nil")
    else:
        Function("cons", 2)(lit(x[0]), lit(x[1:]))


def prove(thm, by=[], by_contracts=False, **kwargs):
    assert all(
        isinstance(b, Proof) for b in by
    ), f"Expected Proof, got {[type(b) for b in by]}"
    decls = thm.decls()
    if by_contracts:  # hmm. doubled the time.
        decls = decls.union(*[b.thm.decls() for b in by])
    cs = [contracts[decl] for decl in decls if decl in contracts]
    return prove0(thm, by=by + cs, **kwargs)


from dataclasses import field


def search(env: dict[str, object], *decls: Decl) -> dict[str, Proof]:
    # search(locals(), Add, Mul)  # returns all proofs in env that use Add and Mul
    return {
        k: v
        for k, v in env.items()
        if isinstance(v, Proof) and all(decl in v.thm.decls() for decl in decls)
    }


@dataclass
class Theorem:
    topgoal: Term
    vs: list[Term] = field(default_factory=list)
    hyps: list[Term] = field(default_factory=list)
    lemmas: list[Term] = field(default_factory=list)
    calc_term: Optional[Term] = None
    cur_case: Optional[Term] = None

    def qed(self, by=[], **kwargs):
        self.lemmas.extend(by)
        return prove(self.topgoal, by=self.lemmas, **kwargs)

    def fixes(self, *vs) -> "Theorem":
        self.vs.extend(vs)
        return self

    def assumes(self, *hyps) -> "Theorem":
        self.hyps.extend(hyps)
        return self

    def clear(self, n):
        self.hyps.pop(n)

    def wrap(self, thm):
        # wrap the theorem with the assumptions and variables
        if self.hyps:
            thm = Implies(And(*self.hyps), thm)
        if self.vs:
            thm = ForAll(self.vs, thm)
        return thm

    def sub(self, thm) -> "Theorem":
        # maintain hyps, but remove the lemmas
        return Theorem(topgoal=self.topgoal, vs=self.vs.copy(), hyps=self.hyps.copy())

    def case(self, case) -> "Theorem":
        # maintain hyps, but remove the lemmas. Keep them? Similar to assumes kind of
        return Theorem(
            topgoal=replace(self, vs=self.vs.copy(), hyps=self.hyps.copy() + [case])
        )  # Hmm. If we mutate lemmas. That's nice?

    def __repr__(self) -> str:
        return pprint.pformat(
            {
                "vs": [str(v) for v in self.vs],
                "hyps": [str(hyp) for hyp in self.hyps],
                "topgoal": str(self.topgoal),
            }
        )

    def case(self, case) -> "Theorem":
        self.cur_case = case
        return self

    def esac(self) -> "Theorem":
        self.cur_case = None
        return self

    def search(self, env, *decls: Decl) -> dict[str, Proof]:
        return search(env, *decls)

    def have(self, thm, by=[], **kwargs):
        self.lemmas.append(prove(self.wrap(thm), by=by, **kwargs))
        self.hyps.append(thm)
        return self

    def calc(self, term: Term) -> "Theorem":
        self.calc_term = term
        return self

    def eq(self, term: Term, by=[], **kwargs) -> "Theorem":
        assert self.calc_term is not None, "Must call calc before eq"
        self.lemmas.append(prove(self.wrap(self.calc_term == term), by=by, **kwargs))
        self.calc_term = term
        return self

    def show(
        self, thm, by=[], **kwargs
    ):  # show is the same as have? without adding to hyps
        self.lemmas.append(prove(self.wrap(thm), by=by, **kwargs))
        # self.hyps.append(thm)
        return self


Lemma = Theorem
Case = Theorem


def vprove0(p: Term, by=[]) -> Proof:
    assert isinstance(p, Term), f"Expected Term, got {p}"
    assert (
        len(p.fvs()) == 0
    ), f"Expected closed term, got {p}, free variables: {[str(v) for v in p.fvs()]}"
    with open("/tmp/prob.p", "w") as f:
        for i, b in enumerate(by):
            assert isinstance(b, Proof), f"Expected Proof, got {b}"
            f.write(f"fof(ax{i}, axiom, {b.thm}).\n")
        f.write(f"fof(goal, conjecture, {p}).\n")
    # replace the path with wherever you put nanocopi
    # If you aren't doing intuitionistic logic, use vampire.
    res = subprocess.run(
        ["vampire", "/tmp/prob.p"],
        capture_output=True,
        text=True,
        timeout=2,
    )
    if "% SZS status Theorem" in res.stdout:
        return True
    else:
        return False


class Poly: ...
