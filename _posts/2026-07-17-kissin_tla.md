---
title: Making TLA+ and x86 Kiss Via Z3Py
date: 2026-07-17
---

I've been trying my hand at translating a reasonable subset of TLA+ into z3py for the purposes of connecting specs to [Verus](https://github.com/verus-lang/verus), [CBMC](https://www.cprover.org/cbmc/), and my assembly checker and also for maybe a little interactive theorem proving as a treat.

I do have a sense that TLA+ has made good inroads into acceptance by a more general software engineering. It is relatively low barrier while delivering useful value.

- <https://learntla.com/>
- <https://lamport.azurewebsites.net/tla/tla.html>
- <https://docs.tlapl.us/>

I think a deficiency of the TLA+ ecosystem where maybe I could deliver some value is to offer some tooling to help validate correspondences of specs and implementations. The flexibility of a library approach vs a tool approach seems useful here.

This is all a work in progress, but I'll show what I've got. The TLA+ ingester is here <https://github.com/philzook58/knuckledragger/blob/main/src/kdrag/solvers/tla.py> .  It'd be nice to hear if this is something people want.

## Hour Clock

A basic example from Specifying Systems is the hour clock example. A clock should keep it's hours between 1 and 12 inclusive.

```python
%%file /tmp/HourClock.tla
---- MODULE HourClock ----
EXTENDS Naturals

VARIABLE hr

HCini == hr \in (1 .. 12)

HCnxt == hr' = IF hr = 12 THEN 1 ELSE hr + 1
          (* Alternately expressed as: hr' = (hr % 12) + 1 *)

HC == HCini /\ [][HCnxt]_hr
==========================
```

    Overwriting /tmp/HourClock.tla

We can load this module and infer the sorts

```python
import kdrag.solvers.tla as tla
import kdrag as kd
import kdrag.smt as smt

mod = tla.Module.of_file("/tmp/HourClock.tla")
mod.infer_sorts()
mod
```

    Module(name='HourClock', variables=['hr'], definitions={'HCini': \in(hr, ..(1, 12)), 'HCnxt': =('(hr), $IfThenElse(=(hr, 12), 1, +(hr, 1))), 'HC': \land(HCini, []($SquareAct(HCnxt, hr)))}, def_params={'HCini': [], 'HCnxt': [], 'HC': []}, theorems=[], decls={'HCini': HCini, 'HCnxt': HCnxt, 'HC': HC, 'hr': hr})

Alternatively or in combination with `infer_sorts`, we can manually declare the sorts of our variables. Unfortunately (?), these sort annotations really are a part of the spec. Sometimes `infer_sorts` is not powerful enough to actually infer all the sorts without help. Or perhaps you want to narrow their meaning or pick a non default representation like  BitVectors. Making a choice like that may completely change the interpretation of the spec (`+` becomes wraparound addition for example). I'd like to have a better story here, but for now, the power user capability is nice.

```python
mod = tla.Module.of_file("/tmp/HourClock.tla")
hr = mod.Var("hr", smt.IntSort())
```

Now that we have sorts, we can get the transition relation as an expression over `hr'` and `hr` as a z3py `BoolRef`

```python
HCnxt = mod.action("HCnxt")
print(type(HCnxt))
HCnxt
```

    <class 'z3.z3.BoolRef'>

hr' = If(hr = 12, 1, hr + 1)

This is a little ugly looking because of how it uses a z3 lambda to talk about sets of ints $hr \in 1..12$

```python
mod.action("HCini")
```

&lambda;x!46 : 1 &le; x!46 &and; 12 &ge; x!46[hr]

The simplified form is less ugly

```python
smt.simplify(mod.action("HCini"))
```

1 &le; hr &and; 12 &ge; hr

We can do whatever wacky stuff we want to do with these expressions. Programmatically rip them apart, build a custom model checker, etc, but here is a routine that builds an assertion that checks an invariant. Basically `mod.invariant` constructs the z3py formula $ (init(hr) \implies inv(hr)) \land  (inv(hr) \land step(hr,hr')\implies inv(hr'))$. Knuckledragger is a proof asssitant and in principle we can semi-autoamtically discharge more difficult goals that might include quantifiers etc by using knuckledragger tactics.

```python
kd.prove(kd.smt.simplify(mod.invariant(inv="HCini", init="HCini", step="HCnxt")))
```

&#x22A8;Or(Not(And(hr' == If(hr == 12, 1, 1 + hr),
           1 <= hr,
           12 >= hr)),
   And(1 <= hr', 12 >= hr'))

One thing I'm still thinking about is outputting the TLA as a spec to Verus, a rust verification tool. Verus is designed to hew pretty close to z3 and offers datatypes that correpond to z3 datatypes. That ought to make it a bit easier. Here for example, Verus has an unbounded `int` type that maps to z3's.

I also have C printers, but they don't support `Int`, so more chewing has to be done to convert to the `uint_t` that it does support (C uint should map reasonably well to z3 bitvectors I think. C's `int` is a nastier beast.).

```python
import kdrag.printers.rust as rust
print(rust.of_expr(smt.simplify(mod.action("HCini"))))
```

    ((1 <= hr) && (12 >= hr))

## Assembly

I've been tinkering on an assembly verifier for a while <https://www.philipzucker.com/refine_assembly/> . I think it makes sense to use that to plug into a TLA spec

Here's an x86_64 program that ticks a clock in `%rdi`

```python
%%file /tmp/clock.s
    .global tick
    .global reset

reset:
    mov $1, %rdi
    jmp tick
tick:
    cmp $12, %rdi
    je reset
    add $1, %rdi
    jmp tick
```

    Overwriting /tmp/clock.s

Assemble it

```python
! gcc -c /tmp/clock.s -o /tmp/clock.o
```

Already I had stuff to check a high level python model (I have a symbolic executor from a subset of python to z3py) against the assembly.
We want to show that each step of the model corresponds to a step of the assembly. This sort of question can be automatically discharged, since it doesn't need inductive reasoning really. We take each corresponding finite chunk of a possible trace / action in the two systems and ask z3 to find if they diverge. The argument that this is sufficient to check all behaviors is the induction argument, but it is not internalized into the system here.

```python
from kdrag.all import *
import kdrag.contrib.pcode as pcode
ctx = pcode.BinaryContext("/tmp/clock.o")

def high_low(addr, memstate):
    i = memstate.get_reg(ctx, "RDI")
    return i

BV64 = smt.BitVecSort(64)
@symdef
def step(i : BV64) -> BV64:
    if i == 12:
        return BitVecVal(1,64)
    else:
        return i + 1

ctx.bisim(high_low, step, cuts=["tick"])
```

    Unexpected SP conflict


    Bisimulation proof succeeded  over all paths [('tick', 'tick')]

There are two pathways from  label `tick --> tick` and it checks both.

We can do basically the same thing, swapping out the python spec for one derived from the TLA file.

```python
from kdrag.all import *
import kdrag.contrib.pcode as pcode
import kdrag.solvers.tla as tla
ctx = pcode.BinaryContext("/tmp/clock.o")
mem = ctx.init_mem()
trace_frags = ctx.execute_trace_frags(mem, cuts=["tick"])
mem1 = trace_frags[("tick","tick")] # 2 traces from tick to tick

def high_low(memstate):
    return smt.BV2Int(memstate.get_reg(ctx, "RDI")) # need to read RDI and convert from BitVec to Int

mod = tla.Module.of_file("/tmp/HourClock.tla")
mod.infer_sorts
hr = mod.Var("hr", smt.IntSort())
hr1 = tla.prime(hr)
mod.action("HCnxt")

kd.prove(
    smt.Implies(
    smt.And(
        hr <= 1000, # We need to know hr is less than INTMAX or else it isn't true
        hr == high_low(mem), # start synchronized
        mod.action("HCnxt")),
    smt.Or(hr1 == high_low(mem1[1].memstate),  # either pathway 1 or 2 happens. We should strengthen this to use path condition
           hr1 == high_low(mem1[0].memstate))), unfold=ctx.select64) # Need to unfold the nasty define select64 opaque function
```

    Unexpected SP conflict

&#x22A8;Implies(And(hr <= 1000,
            hr == BV2Int(select64le(register(state0), &RDI)),
            hr' == If(hr == 12, 1, hr + 1)),
        Or(hr' ==
           BV2Int(1 + select64le(register(state0), &RDI)),
           hr' == BV2Int(1)))

# Bits and Bobbles

What kicked this off was finding out that tlatools exports an XML parse tree. Parsing TLA is not impossible, but it's a huge barrier lifted to be able to just use that

Apalache <https://apalache-mc.org/> is a project to build an SMT based model checker for TLA+ and they have basically an identical problem of inferring TLA sorts. It would be nice to reuse their solutions and they do have a `typecheck` subcommand. I should read their papers.

Some previous efforts of mine to model tla in z3py
<https://www.philipzucker.com/Modelling_TLA_in_z3py/>
<https://www.philipzucker.com/shallow_logic_knuckle/>

I have not dealt with Modules in any sort of generalizable way

I could do casting abd subsorting which might ease some typing burden. BitVec should be able to upcast to Int, but I dunno about vice versa.

One sticky point is TLA sequences `<<>>`. Sometimes they map well on z3 sequences. Sometimes they map onto Z3 tuples. It depends if you are Head and Tailing or if you need heterogenous sorts inside them. There are usages that won't be simply typed.

Generally speaking a sticky point is TLA's concept of function. Record and sequences I believe are sugar basically on this ocnstruct, but it is too tempting and really again kind of important to refine these particular usages

I added an anonymous struct `AStruct` helper to knuckledragger. It's kind of nice.

It is confusing to estimate the popularity of things or how that should affect one's decisions. I have a sense that TLA+ has made more inroads into the general software engineering populace than other formal tooling. At the same time, sometimes I think Lean is eating everyone's lunch and there is no point in doing anything else. These estimates are based basically on comment section buzz. I _know_ the internet is full of bullshitters who don't even realize they're bullshitting. I'm one of them. And even as I discount each individual comment, there is some kind of low pass filter on them that becomes a feeling of popularity. I do not think I would be engaging unless I thought it had a foothold. There is a massive marketplace of ideas out there.

I have at different points been interested in TLA+, poo pooed it as being dusty and not as powerful as dependent type whatevers, and now I think I am coming back around. It is pretty focussed on reasonably describing systems that change with time without crazy concept side tracks. The syntax is well considered.

One deficiency of TLA+ is that there is not a great story so far as I am aware to connect specs to an implementation in a way that is machine checked. One way of doing so would be to run a TLA interpreter in lockstep with the system and fuzz it for divergence.

Something that I've become more aware of is that there is no magic or TRUE sense that one system relates to another. Even if I took a first order logic formalized Peano arithmetic and a formalized ZFC, there is no automatic relationship between the two discussions of the naturals. You need to define it and then you can prove something about it. The situation is even more hopeless for a when the two systems in question like in very different frameworks (C and Rust, ZFC and Type theory, etc). The "naturalness" that talking about uint32 in system A and u32 in system B should be "obviously" the same thing is more illusionary than you might expect. You have to say how you want to consider them to be related.

The TLA+ community and Lamport are notable as being at least type questioning. To connect TLA+ to C, Rust, or assembly in any reasonable way I need the types. (Well, maybe rust could support a generic Value type, but the other two it would be awful) The machine oriented perspective of types like in C-ish language is that the type is needed because you need to know what the data is going to look like in the output of the compiler. The dyanmic typed position is that this is drudgery that should be the machines job and that in an ideal world should not have to be specified. The type theory response to that is that no no no, the types are a dimension of expression on intent and have nothing to do with the machine persay.

Turning TLA+ into typed z3py is basically an elaboration problem. I want to recursive translates a untyped AST to a typed one. When you do such things, one realizes that sometimes it is useful to pass down information about expected types. This can be an optional parameter.
I have a function `elab : Untyped_ast -> ?sort -> typed_ast`.  I can often infer required types from binary operators like `=` and `+` where I know the left and right arguments need to be of the same type. Once I determine the type of the left, I should pass this information down to the right. This is in essence the signature of bidirectional typing and at this level, there isn't much spooky about it. It is a natural strategy you will invent on your own if you ever face an untyped to typed problem.

Apalache <https://apalache-mc.org/> is a project to build an SMT based model checker for TLA+ and they have basically an identical problem. It would be nice to reuse their solutions and they do have a `typecheck` subcommand. I think I just want (need?) more control over the choice of types than they offer.

I have attempted TLA to knucledragger multiple times in the past, making a custom Lark parser and trying to shallowly embed the trace semantics of TLA in z3py. Ultimately the first was just sort of too painful. I hate parsing. The latter was also too painful as it required a lot of `Lambda` and extenstionlaity reasoning. z3 would basically choke with not complex problems. Maybe this is getting better. I see that z3 4.17 has some enhanced higher order stuff.

I think the lesson I have received over and over again is to avoid higher order and inductive reasoning if you can.

In it's main usage TLA+ definitions break down into basically 3 categories

1. State predicates
2. Transition relations (expressions only involving the `'` temporal next operator)
3. True temporal properties, but mainly of a particular form

Some of the evolutionary force on TLA specs is that people want to use the checker TLC and it can only support specs that can be reasonably executed. I think this breakdown is also a pretty natural way of thinking about systems. Transition relations are OP and your fancy whatever shellac on them is probably not that much functionality gain.

|    |     |
|----|-----|
| 3   | Int |
| x \in 1...2   |  Int   |
| [foo |-> 3]   |  AStruct(foo=Int) |
|

## The TLA ingester as it stands today

```python
"""
Automatically downloads tla2tools.jar
"""

import kdrag.solvers
import subprocess
import xml.etree.ElementTree as ET
from dataclasses import dataclass, field
import kdrag.smt as smt
import operator
import kdrag as kd
from typing import Callable, Mapping

kdrag.solvers.download(
    "https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar",
    "tla2tools.jar",
    "150b0294c3d407c15f0c971351ccd4ae8c6d885397546dff87871a14be2b4ee4",
)

"""
Plans and TODOs:
- replace usages of domains with domain
- Factor basically everything to be a member of Module
- ZFC style vs Tagged value style vs what we did
- Should functions be uniformly represented as Arrays?
- casting of tuple <-> sequence (when uniformly typed)?
- col/line numbers. Bad error messages when z3 gets a sort error
- What is it for?
- Inlining evaluation. BMC
- Constants and Assumes. Actually check what library modules are imported
- Connect a chunk of assembly.
- Design high specs
- Operator arguments
- Let, Exists, Lambda, CHOOSE
- More EXCEPT notation. Pattern matching
- Temporal operators
"""


def run_tools(args: list[str]):
    """
    Run tla2tools.jar with the given arguments. Returns the stdout of the process.
    """
    # Weirdo flags to try an reduce JVM startup time a little
    res = subprocess.run(
        [
            "java",
            "-XX:TieredStopAtLevel=1",
            "-XX:+UseSerialGC",
            "-cp",
            kdrag.solvers.binpath("tla2tools.jar"),
        ]
        + args,
        capture_output=True,
    )
    if res.returncode != 0:
        raise RuntimeError(
            f"tla2tools.jar failed with return code {res.returncode}:\n{res.stdout.decode()}\n{res.stderr.decode()}"
        )
    else:
        return res.stdout


def check(filename: str):
    """
    Run the model checker on a tla file. Returns the stdout of the model checker.
    """
    return run_tools(["tlc2.TLC", filename])


def pluscal_translate(filename: str) -> bytes:
    """
    Run the pluscal translator on a tla file. Returns the stdout of the translator.
    """
    return run_tools(["pcal.trans", filename])


def tla_to_xml(filename):
    """
    Convert tla file to xml output
    """
    # https://github.com/tlaplus/tlaplus/blob/master/tlatools/org.lamport.tlatools/src/tla2sany/xml/sany.xsd
    return run_tools(["tla2sany.xml.XMLExporter", "-o", filename])


# TODO: Consider maintaining col/line numbers for better errors
@dataclass(frozen=True)
class App:
    "Untyped Ast for expressions"

    f: object
    args: list["App"]

    def __repr__(self):
        if not self.args:
            return f"{self.f}"
        else:
            return f"{self.f}({', '.join(map(str, self.args))})"

    def all_decls(self) -> set[str]:
        decls = set()
        todo: list[App] = [self]
        while todo:
            e = todo.pop()
            if isinstance(e.f, str):
                decls.add(e.f)
            todo.extend(e.args)
        return decls

    def is_const(self):
        return not self.args and isinstance(self.f, str)

    def is_value(self):
        return not self.args and isinstance(self.f, (int, StringLit))

    def is_binder(self):
        return self.f in {"$BoundedForall", "$BoundedExists"}

    def infer_lite(self) -> smt.SortRef | None:
        if isinstance(self.f, int):
            return smt.IntSort()
        if isinstance(self.f, StringLit):
            return smt.StringSort()
        if self.f in consts:
            return consts[self.f].sort()
        if self.f in comp or self.f in {
            r"\land",
            r"\lor",
            r"\lnot",
            "=",
            r"\in",
            r"\notin",
            "$BoundedForall",
            "$BoundedExists",
            "$ConjList",
        }:
            return smt.BoolSort()


def domain(e: smt.ExprRef) -> smt.SortRef:
    assert smt.is_func(e)
    dom = smt.domains(e)
    assert len(dom) == 1, f"Expected one domain for {e}, got {dom}"
    return dom[0]


@dataclass(frozen=True)
class StringLit:
    value: str

    def __repr__(self):
        return repr(self.value)


@dataclass
class Module:
    name: str
    variables: list[str]
    definitions: dict[str, App]
    def_params: dict[str, list[str]]
    theorems: list[App]
    decls: dict[str, smt.FuncDeclRef] = field(default_factory=dict)

    # assumes, constants, extends

    def operator(
        self, name: str, decls: dict[str, smt.FuncDeclRef | smt.ExprRef] = {}, sort=None
    ) -> smt.ExprRef:
        return to_smt(self.definitions[name], {**self.decls, **decls}, sort)

    def action(
        self, actname: str, decls: dict[str, smt.FuncDeclRef | smt.ExprRef] = {}
    ) -> smt.ExprRef:
        """
        Return the action of the module as an smt expression. These are expressions that may involve primed variables,
        but do not involve other temporal operators.
        """
        return self.operator(actname, decls, sort=smt.BoolSort())

    def behavior(
        self, name: str, decls: dict[str, smt.FuncDeclRef | smt.ExprRef]
    ) -> smt.ExprRef:
        """
        Return a useful smt form of statements that involve non trivial temporal operators
        """
        raise NotImplementedError("behavior", name, decls)

    def Var(self, name: str, sort: smt.SortRef) -> smt.ExprRef:
        v = smt.Const(name, sort)
        self.declare_var(v)
        return v

    def declare_var(self, v: smt.ExprRef):
        assert smt.is_const(v)
        name = v.decl().name()
        assert name in self.variables, (
            f"Variable {name} not in module variables {self.variables}"
        )
        if name in self.decls:
            assert self.decls[name].eq(v.decl()), (
                f"Variable {name} already declared with different sort {self.decls[name].range()} vs {v.sort()}"
            )
        else:
            self.decls[name] = smt.Function(name, v.sort())

    def declare_operator(self, name: str, *sorts: smt.SortRef):
        # or should operators be considered meta substitutable? Op(_,_) higher order operators. Yuck
        # and really, every operator implicitly has all v v' of variables as parameters too.
        assert name in self.definitions
        self.decls[name] = smt.Function(name, *sorts)

    def declare_vars(self, vs: list[smt.ExprRef]):
        for v in vs:
            self.declare_var(v)

    def infer_sorts(self):
        eqs = []
        ins = []
        for k, v in self.definitions.items():
            if True:  # self.def_params[k] != []: # TODO: Handle operator arguments. This isn't treating scope correctly
                sort = v.infer_lite()
                if sort is not None:
                    self.decls[k] = smt.Function(k, sort)
                else:
                    eqs.append((k, v))
                todo = [v]
                while todo:
                    e = todo.pop()
                    if e.f == "=" and e.args[0].is_const():
                        assert isinstance(e.args[0].f, str)
                        eqs.append(
                            (e.args[0].f, e.args[1])
                        )  # But should also be checking for ' variables
                    # Check symmetrically e = v?
                    elif e.f == "\\in" and e.args[0].is_const():
                        assert isinstance(e.args[0].f, str)
                        ins.append((e.args[0].f, e.args[1]))
                    if not e.is_binder():
                        todo.extend(reversed(e.args))
        # TODO: could loop to fixed point
        # TODO: operator arguments?
        while True:
            l = len(self.decls)
            for k, v in ins:
                try:
                    e = to_smt(v, self.decls)
                    if k in self.decls:
                        assert self.decls[k] == smt.Function(k, domain(e)), (
                            f"sort mismatch for {k}: {self.decls[k]} vs {domain(e)}"
                        )
                    else:
                        self.decls[k] = smt.Function(k, domain(e))
                except SortInference as _:
                    pass
            for k, v in eqs:
                try:
                    e = to_smt(v, self.decls)
                    if k in self.decls:
                        assert self.decls[k] == smt.Function(k, e.sort()), (
                            f"sort mismatch for {k}: {self.decls[k]} vs {e.sort()}"
                        )
                    else:
                        self.decls[k] = smt.Function(k, e.sort())
                except SortInference as _:
                    pass
            if len(self.decls) == l:
                break
        for v in self.variables:
            if v not in self.decls:
                raise SortInference(f"Could not infer sort for variable {v}")

    def vars(self) -> list[smt.ExprRef]:
        return [self.decls[v]() for v in self.variables]

    def vars1(self) -> list[smt.ExprRef]:
        return [prime(v) for v in self.vars()]

    def invariant(self, inv=None, init=None, step=None):
        assert inv is not None and init is not None and step is not None
        step = self.action(step)
        init = self.action(init)
        vs = self.vars()
        vs1 = self.vars1()
        if isinstance(inv, str):
            inv = self.action(inv)
        elif isinstance(inv, smt.BoolRef):
            pass
        else:
            raise ValueError("Unexpected inv type", inv, type(inv))
        inv1 = smt.substitute(inv, *zip(vs, vs1))
        return smt.And(smt.Implies(init, inv), smt.Implies(smt.And(step, inv), inv1))

    @staticmethod
    def of_file(filename, pcal=False) -> "Module":
        if pcal:
            pluscal_translate(filename)
        mods = ET.fromstring(tla_to_xml(filename))
        name = mods.findtext("RootModule")
        assert name is not None

        by_uid = {}
        for entry in mods.findall("context/entry"):
            uid = entry.findtext("UID")
            node = next((c for c in entry if c.tag != "UID"), None)
            if uid is not None and node is not None:
                by_uid[uid] = node

        def ref_name(ref):
            uid = ref.findtext("UID")
            node = by_uid.get(uid)
            if node is None:
                return f"UID:{uid}"
            return node.findtext("uniquename") or node.tag

        def expr(node):
            if node.tag == "OpApplNode":
                ref = next(iter(node.find("operator")), None)
                f = ref_name(ref) if ref is not None else node.tag
                operands = node.find("operands")
                args = [] if operands is None else [expr(arg) for arg in operands]
                bounds = node.findall("./boundSymbols/bound")
                if bounds:
                    assert len(args) == 1, (
                        f"Expected one body for binding operator {f}, got {args}"
                    )
                    bound_args = []
                    for bound in bounds:
                        args1 = [expr(arg) for arg in bound]
                        assert len(args1) >= 2
                        domain = args1[-1]
                        for var in args1[:-1]:
                            assert isinstance(var, App) and not var.args
                            assert isinstance(var.f, str)
                            bound_args.extend([var, domain])
                    return App(f, bound_args + args)
                return App(f, args)
            if node.tag.endswith("Ref"):
                return App(ref_name(node), [])
            if node.tag == "NumeralNode":
                return App(int(node.findtext("IntValue")), [])
            if node.tag == "StringNode":
                return App(StringLit(node.findtext("StringValue") or ""), [])
            return App(node.findtext("uniquename") or node.tag, [])

        root = next(
            node
            for node in by_uid.values()
            if node.tag == "ModuleNode" and node.findtext("uniquename") == name
        )
        variables = []
        for ref in root.findall("OpDeclNodeRef"):
            uid = ref.findtext("UID")
            node = by_uid.get(uid) if uid is not None else None
            if node is not None and node.findtext("./location/filename") == name:
                var_name = node.findtext("uniquename")
                if var_name is not None:
                    variables.append(var_name)

        definitions: dict[str, App] = {}
        def_params: dict[str, list[str]] = {}
        theorems: list[App] = []
        for node in by_uid.values():
            if node.findtext("./location/filename") != name:
                continue
            body = node.find("./body/*")
            if node.tag == "UserDefinedOpKind" and body is not None:
                def_name = node.findtext("uniquename")
                assert def_name is not None
                definitions[def_name] = expr(body)
                def_params[def_name] = [
                    ref_name(ref)
                    for ref in node.findall("./params/leibnizparam/FormalParamNodeRef")
                ]
            elif node.tag == "TheoremNode" and body is not None:
                theorems.append(expr(body))

        return Module(name, variables, definitions, def_params, theorems)


binops: dict[object, Callable[[smt.ExprRef, smt.ExprRef], smt.ExprRef]] = {
    "+": operator.add,
    "-": operator.sub,
    "*": operator.mul,
    "%": operator.mod,
    "\\union": smt.SetUnion,
    "\\intersect": smt.SetIntersect,
    "\\": smt.SetDifference,
    "\\o": smt.Concat,
}


def _head(x: smt.ExprRef) -> smt.ExprRef:
    assert isinstance(x, smt.SeqRef)
    return x[0]


unops: dict[object, Callable[[smt.ExprRef], smt.ExprRef]] = {
    "-.": operator.neg,
    "Head": _head,
    "Len": smt.Length,
}

comp: dict[object, Callable[[smt.ExprRef, smt.ExprRef], smt.ExprRef]] = {
    "<": operator.lt,
    "\\leq": operator.le,
    ">": operator.gt,
    "\\geq": operator.ge,
}
consts: dict[object, smt.ExprRef] = {
    "BOOLEAN": smt.FullSet(smt.BoolSort()),
    "TRUE": smt.BoolVal(True),
    "FALSE": smt.BoolVal(False),
}

"""
But really this should be module
defined = (
    {
        "$IfThenElse",
        "$BoundedForall",
        "$BoundedExists",
        "$SetOfRcds",
        "$FcnConstructor",
        "$FcnApply",
        "$SetEnumerate",
        "$RcdConstructor",
    }.union(consts.keys())
    .union(binops.keys())
    .union(unops.keys())
    .union(comp.keys())
)
def is_defined(f: App) -> bool:
    if 
"""


def prime(e: smt.ExprRef) -> smt.ExprRef:
    assert smt.is_const(e)
    # TODO: prime should actually be a recursive function that takes in the current variables in scope and traverses a term.
    name = e.decl().name()
    assert name[-1] != "'", f"Cannot prime {e} because it is already primed"
    return smt.Const(name + "'", e.sort())


class SortInference(Exception):
    pass


# Should to_smt be a method of Module? decls is var types usually. We may want to recursively call other definitions
def to_smt(
    e: App, decls: Mapping[str, smt.FuncDeclRef | smt.ExprRef], sort=None
) -> smt.ExprRef:
    if isinstance(e.f, StringLit) and not e.args:
        assert sort is None or sort == smt.StringSort()
        return smt.StringVal(e.f.value)
    if e.f in decls:
        assert isinstance(e.f, str)
        f = decls[e.f]
        if isinstance(f, smt.FuncDeclRef):
            assert len(e.args) == f.arity()
            assert sort is None or sort == f.range()
            args = [
                to_smt(arg, decls, sort=f.domain(i)) for i, arg in enumerate(e.args)
            ]
            return f(*args)
        elif isinstance(f, smt.ExprRef):
            assert not e.args
            assert sort is None or sort == f.sort()
            return f
        else:
            raise ValueError(f"decls[{e.f}] is not a FuncDeclRef or ExprRef")
    elif e.f == "$BoundedForall":
        assert len(e.args) >= 3 and len(e.args) % 2 == 1
        bound_decls = dict(decls)
        smt_vars = []
        domains = []
        for var, domain in zip(e.args[:-1:2], e.args[1:-1:2]):
            assert not var.args and isinstance(var.f, str)
            domain_smt = to_smt(domain, bound_decls)
            assert smt.is_func(domain_smt)
            assert smt.codomain(domain_smt) == smt.BoolSort()

            x = smt.Const(var.f, smt.domains(domain_smt)[0])
            bound_decls[var.f] = x
            smt_vars.append(x)
            domains.append(smt.IsMember(x, domain_smt))
        body = to_smt(e.args[-1], bound_decls, sort=smt.BoolSort())
        return smt.ForAll(
            smt_vars, *domains, body
        )  # TODO: does tla support telescoping?
    elif isinstance(e.f, int):
        assert not e.args
        assert sort is None or sort == smt.IntSort()
        return smt.IntVal(e.f)
    elif e.f == "\\land" or e.f == "$ConjList":
        args = [to_smt(arg, decls, sort=smt.BoolSort()) for arg in e.args]
        if len(args) == 0:
            return smt.BoolVal(True)
        elif len(args) == 1:
            return args[0]
        else:
            return smt.And(*args)
    elif e.f == "\\lor":
        assert len(e.args) >= 2
        args = [to_smt(arg, decls, sort=smt.BoolSort()) for arg in e.args]
        return smt.Or(*args)
    elif e.f == "\\lnot":
        assert len(e.args) == 1
        arg = to_smt(e.args[0], decls, sort=smt.BoolSort())
        return smt.Not(arg)
    elif e.f == "=":
        assert len(e.args) == 2
        # maybe vice versa for sort propagation?
        rhs = to_smt(e.args[1], decls)
        lhs = to_smt(e.args[0], decls, sort=rhs.sort())
        return smt.Eq(lhs, rhs)
    elif e.f == "..":
        # 1..10 range syntax
        assert len(e.args) == 2
        args = [to_smt(arg, decls, sort=smt.IntSort()) for arg in e.args]
        x = smt.FreshConst(smt.IntSort(), prefix="x")
        return smt.Lambda(x, smt.And(args[0] <= x, x <= args[1]))
    elif e.f == "\\in" or e.f == "\\notin":
        x = to_smt(e.args[0], decls)
        s = to_smt(e.args[1], decls, sort=smt.SetSort(x.sort()))
        res = smt.IsMember(x, s)
        if e.f == "\\notin":
            res = smt.Not(res)
        return res
    elif e.f == "'":  # Prime operator
        assert len(e.args) == 1 and len(e.args[0].args) == 0
        # TODO: prime can actually be applied to compound expressions?
        x = to_smt(e.args[0], decls, sort=sort)
        return prime(x)
    elif e.f == "UNCHANGED":
        assert len(e.args) == 1
        if len(e.args[0].args) == 0:
            x = to_smt(e.args[0], decls)
            return smt.Eq(prime(x), x)
        elif e.args[0].f == "$Tuple":
            assert len(e.args[0].args) >= 1
            return smt.And(
                *[
                    smt.Eq(prime(to_smt(arg, decls)), to_smt(arg, decls))
                    for arg in e.args[0].args
                ]
            )
        else:
            raise ValueError(f"Cannot handle UNCHANGED {e.args[0]}")
    elif e.f == "$IfThenElse":
        assert len(e.args) == 3
        cond = to_smt(e.args[0], decls, sort=smt.BoolSort())
        then = to_smt(e.args[1], decls, sort=sort)
        else_ = to_smt(e.args[2], decls, sort=sort)
        return smt.If(cond, then, else_)
    elif e.f == "$Tuple":  # TODO actual tuples?
        args = [to_smt(arg, decls) for arg in e.args]
        if all(arg.sort() == args[0].sort() for arg in args):
            return smt.Concat(*[smt.Unit(arg) for arg in args])
        else:
            return kd.tuple_(*args)
    elif e.f == "$FcnApply":
        assert len(e.args) == 2
        f = to_smt(e.args[0], decls)
        if isinstance(f, smt.SeqRef):
            arg = to_smt(e.args[1], decls, sort=smt.IntSort())
            return f[arg - smt.IntVal(1)]
        elif smt.is_func(f):
            arg = to_smt(e.args[1], decls, sort=smt.domains(f)[0])
            return f(arg)
        else:
            raise ValueError(f"Cannot apply {f} of type {type(f)}")
    elif e.f == "Append":
        elmt = to_smt(e.args[1], decls)
        seq = to_smt(e.args[0], decls, sort=smt.SeqSort(elmt.sort()))
        return smt.Concat(seq, smt.Unit(elmt))
    elif e.f == "Tail":
        assert len(e.args) == 1
        e1 = to_smt(e.args[0], decls, sort=sort)
        assert isinstance(e1, smt.SeqRef), (
            f"Expected sequence, got {e1} of type {type(e1)}"
        )
        return kd.Tail(e1)
    elif e.f == "$SetEnumerate":
        # concrete set enumeration {1,2,3,4}
        assert sort is None or isinstance(sort, smt.ArraySortRef)
        argsort = sort.domain() if sort is not None else None
        args = [to_smt(arg, decls, sort=argsort) for arg in e.args]
        if len(args) == 0:
            if argsort is None:
                raise SortInference(f"Cannot infer sort of empty set {e}")
            return smt.EmptySet(argsort)
        else:
            S = smt.EmptySet(args[0].sort())
            for arg in args:
                S = smt.SetAdd(S, arg)
            return S
    elif e.f in binops:
        assert len(e.args) == 2
        args = [to_smt(arg, decls, sort=sort) for arg in e.args]
        return binops[e.f](args[0], args[1])
    elif e.f in comp:
        assert len(e.args) == 2
        assert sort is None or sort == smt.BoolSort()
        args = [to_smt(arg, decls) for arg in e.args]
        return comp[e.f](args[0], args[1])
    elif e.f in unops:
        assert len(e.args) == 1
        args = [to_smt(arg, decls, sort=sort) for arg in e.args]
        return unops[e.f](args[0])
    elif e.f in consts:
        assert len(e.args) == 0
        assert sort is None or sort == consts[e.f].sort()
        return consts[e.f]
    elif e.f == "$RcdConstructor":
        # Record Construction
        sorts = {}
        if sort is not None:
            assert isinstance(sort, smt.DatatypeSortRef), (
                f"Expected sort to be a DatatypeSortRef, got {sort}"
            )
            assert sort.num_constructors() == 1, (
                f"Expected sort to have one constructor, got {sort}"
            )
            constructor = sort.constructor(0)
            for i in range(constructor.arity()):
                acc = sort.accessor(0, i)
                sorts[acc.name()] = acc.range()
        fields = {}
        fields0 = assoc_list(e.args)
        assert sort is None or set(fields0.keys()) == set(sorts.keys()), (
            f"fields mismatch: {fields0.keys()} vs {sorts.keys()}"
        )
        fields = {k: to_smt(v, decls, sort=sorts.get(k)) for k, v in fields0.items()}
        return kd.astruct(**fields)
    elif e.f == "$SetOfRcds":
        # [acct : 1..3] syntax. Returns the set of records in that cartesian product
        assert sort is None  # TODO
        fields0 = assoc_list(e.args)
        fields = {k: to_smt(v, decls) for k, v in fields0.items()}
        sort = kd.AStruct(**{k: v.sort().domain() for k, v in fields.items()})
        x = smt.FreshConst(sort, prefix="x")
        return smt.Lambda([x], smt.And(*[v(getattr(x, k)) for k, v in fields.items()]))
    elif e.f == "$FcnConstructor":  # [v \in S |-> e] syntax.
        assert len(e.args) == 3
        v, dom, body = e.args
        dom_smt = to_smt(dom, decls)
        assert len(v.args) == 0 and isinstance(v.f, str), v
        assert smt.is_func(dom_smt), f"Expected function for domain, got {dom_smt}"
        vsmt = smt.Const(v.f, smt.domains(dom_smt)[0])
        decls = {**decls, v.f: vsmt}
        body_smt = to_smt(body, decls)
        return smt.Lambda([vsmt], body_smt)  # We've thrown away domain which is goofy.
    elif e.f == "$Except":
        assert len(e.args) >= 2
        base = to_smt(e.args[0], decls, sort=sort)  # base function
        if isinstance(base, smt.DatatypeRef):
            raise NotImplementedError("Except on records not implemented yet")
        elif smt.is_func(base):
            res = base
            cod = smt.codomain(base)
            dom = smt.domains(base)[0]
            for kv in e.args[1:]:
                assert kv.f == "$Pair" and len(kv.args) == 2
                k, v = kv.args
                if k.f == "$Seq" and len(k.args) == 1:
                    k = to_smt(k.args[0], decls, sort=dom)
                    v = to_smt(v, decls, sort=cod)
                    res = smt.Store(res, k, v)
                else:
                    raise NotImplementedError(f"EXCEPT on {k} not implemented yet")
            return res
        else:
            raise NotImplementedError(f"EXCEPT on {base} not implemented yet")

    # These appear in spec statements
    # elif e.f == "$SquareAct":
    #    return smt.Const("$SQUAREACT TODO", smt.BoolSort())
    # elif e.f == "[]":
    #    return smt.Const("[] TODO", smt.BoolSort())
    # elif sort is not None:
    #    # fallback to uninterprted function
    #    args = [to_smt(arg, decls) for arg in e.args]
    #    f = smt.Function(e.f, *[arg.sort() for arg in args], sort)
    #    return f(*args)
    else:
        raise SortInference(
            f"Could not convert {e} to smt. Maybe you need to supply a toplevel sort or decl?"
        )


def assoc_list(pairs: list[App]) -> dict[str, App]:
    """
    Convert a list of pairs to a dictionary. Each pair is an App with two arguments.
    """
    d = {}
    for pair in pairs:
        assert pair.f == "$Pair" and len(pair.args) == 2
        key, value = pair.args
        assert len(key.args) == 0, "Only string keys are supported in assoc_list"
        key = key.f
        assert isinstance(key, StringLit), (
            "Only string keys are supported in assoc_list"
        )
        key = key.value
        assert key not in d, f"Duplicate key {key} in assoc_list"
        d[key] = value
    return d


"""

    def infer_sorts2(self):
        # just do it inline?
        for k, v in self.definitions.items():
            if self.def_params[k] == []:
                sort = v.infer_lite()
                if sort is not None:
                    self.sorts[k] = sort
                else:
                    eqs.append((k, v))
                todo = [v]
                while todo:
                    e = todo.pop()
                    if e.f == "=" and e.args[0].is_const():
                        eqs.append(
                            (e.args[0].f, e.args[1])
                        )  # But should also be checking for ' variables
                    # Check symmetrically e = v?
                    elif e.f == "\\in" and e.args[0].is_const():
                        ins.append((e.args[0].f, e.args[1]))
                    if not e.is_binder():
                        todo.extend(reversed(e.args))
    


def infer(e : App, decls: dict[str, smt.FuncDeclRef | smt.ExprRef]) -> smt.SortRef | None:
    pass
def check(e : App, decls: dict[str, smt.FuncDeclRef | smt.ExprRef], sort : ) -> bool:
    pass
But yeah, also


prims = {
    smt.IntSort(): TLAPrim.Int(),
    smt.BoolSort(): TLAPrim.Bool(),
    smt.StringSort(): TLAPrim.String(),
}

def sort_to_Sort(sort: smt.SortRef) -> smt.DataypeRef:
    if sort in prims:
        return prims[sort]
    elif isinstance(sort, smt.SeqSortRef):
        return TLASort.Seq(sort_to_Sort(sort.domain()))
    elif isinstance(sort, smt.DatatypeSortRef):
    if isinstance(sort, smt.ArraySortRef):

def type_constrs(e : App, decls: dict[str, smt.FuncDeclRef | smt.ExprRef], constrs, sorts : dict[App, smt.ExprRef]) -> smt.ExprRef:
    todo = [([], e)] # context
    constrs = []
    #sorts = {}
    while todo:
        e = todo.pop()
        try:
            e = to_smt(e, decls)
            constrs.append(smt.Eq(smt.Const(id(e), Sort), sort_to_Sort(e.sort())))
        except SortInference as _:
            if 


Yea. Let's just bail on strong inference.


def cast(x: smt.ExprRef, sort: smt.SortRef) -> smt.ExprRef:
    if x.sort() == sort:
        return x
    if isinstance(sort, smt.SeqSortRef) and kd.is_tuple(x):
        dom = sort.domain()
    else:
        raise ValueError(f"Cannot cast {x} of sort {x.sort()} to {sort}")

def sort_constraints(e: App, decls: dict[str, smt.SortRef], sort=None) -> list[smt.ExprRef]:

def infer_sort(e: App, ctx: dict[str, smt.SortRef], constrs : dict[str, ]) -> smt.SortRef | None:
    if isinstance(e.f, StringLit):
        return smt.StringSort()
    if isinstance(e.f, int):
        return smt.IntSort()
    if e.f in ctx:
        return ctx[e.f]
    if e.f in comp:
        return smt.BoolSort()

Maybe to_smt could mutate the decls?
A data driven spec of what sorts things have?

sorts = {
"BOOLEAN" : {[], smt.SetSort(smt.BoolSort())},
"TRUE" : {[], smt.BoolSort()},
"FALSE" : {[], smt.BoolSort()},
"\\land" : {[], smt.BoolSort()},
"\\lor" : {[], smt.BoolSort()},
}}

Use smt solve for type checking?

TLASort = kd.Inductive("TLASort")
TLASort.declare("Bool")
TLASort.declare("Int")
TLASort.declare("Array", ("domain", TLASort), ("range", TLASort))
TLASort.declare("Seq", ("domain", TLASort))
TLASort.declare("Record", ("fields", kd.MapSort(kd.StringSort(), TLASort)))

TLAPrim = kd.Inductive("TLAPrim")
TLAPrim.declare("Bool", ("bool", smt.BoolSort()))
TLAPrim.declare("Int", ("int", smt.IntSort()))
TLAPrim.declare("String", ("string", smt.StringSort()))

TLAValue = kd.Inductive("TLAValue")
TLAValue.declare("Prime", ("value", TLAPrim))
TLAValue.declare("Array", smt.ArraySort(TLAPrim, TLAValue))


    
    def infer_sorts(self, typeok="TypeOk") -> dict[str, smt.ExprRef]:
        todo = [self.definitions[typeok]]
        decls = {}
        while todo:
            e = todo.pop()
            match e:
                case App("\\land", args) | App("$ConjList", args):
                    todo.extend(args)
                # case App("=", [App(lhs, []), rhs]):
                #    assert lhs not in decls, f"lhs {lhs} already in decls"
                #    decls[lhs] = smt.Const(lhs, to_smt(rhs, decls).sort())
                case App("\\in", [App(lhs, []), rhs]):
                    assert lhs not in decls, f"lhs {lhs} already in decls"
                    decls[lhs] = smt.Const(lhs, domain(to_smt(rhs, decls)))
                case _:
                    raise ValueError("unexpected expression in infer_sorts", e)
        return decls
    
"""

```
