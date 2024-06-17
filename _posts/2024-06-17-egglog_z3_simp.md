---
title: Conditional Simplification of Z3py Expressions with Egglog
date: 2024-06-17
---

Z3 offers `simplify`, which is really really useful. But it only works with the built in z3 rewrite rules, which are not contextual. It would be awesome to be able to add user defined rewrite rules or rewrite under solver contexts. There may be some kind of way to use a solver to get contextual rewriting but I'm not sure. There are some tactics discussed here
<https://microsoft.github.io/z3guide/programming/Example%20Programs/Formula%20Simplification/> but also caleb did some clever hacky workarounds (he put a dummy variable in and then rooted around for it. "all it's doing really is making a fresh variable v, setting v == expr_to_simplify, run the simplification then search through the constraints for v" ) <https://github.com/draperlaboratory/cozy/blob/c955d6add00bc712775516f02ee6fdd6c10d3f7a/cozy/claripy_ext.py#L10>

The obvious thing that shows up is simplification of array expressions, which are the compounding of many stores and loads. This sort of thing shows up in symbolic execution all the time. If the addresses of the stores and loads are symbolic, you need contextual aliasing info to know which ones commutes and cancel with each other. Otherwise you're just stuck a a big long mess of an expression. This was one of my egglog0 examples <https://www.philipzucker.com/egglog0/> and also an example I wrote in egglog <https://egraphs-good.github.io/egglog/?example=array> I think it was Evy that brought this idea up to me in between my meltdowns at chris leaving. It's a good one.

I was getting into a quagmire of building my own AST for knuckledragger <https://github.com/philzook58/knuckledragger> which was roughly similar to Z3's python AST but under my control.  But now I am back to thinking  a cleverer design is to just heavily piggy back on z3 even if I'm not always calling z3 itself.

The z3py api is a de facto standard and I think it ultimately has fewer warts than merits. CVC5 has built a pythonic api to mimic it <https://cvc5.github.io/docs/cvc5-1.0.2/api/python/pythonic/pythonic.html> which I can hopefully just swap in. I consider pysmt to be basically unusable (sorry) because they diverged from this api.

Saul has been making the egglog python bindings <https://egglog-python.readthedocs.io/latest/> taking a very meta highly integrated approach. I kind of just want it to look like z3 though. It's very interesting and I'm haunted by the idea that I am a stodgy old man and they're right. I think it's biggest demerit is that it is very novel. I've never seen an interface like it. From a research perspective this is a plus. It is very cool that they are getting the python typechecker and the embedded dsl to play ball. I dunno <https://egraphs.zulipchat.com/#narrow/stream/375765-egg.2Fegglog/topic/egglog.20python.20midlevel.20api/near/421919681>

It turns out, it is simple enough to have my cake too. The pyegglog supports the raw bindings and I've been spending a decent amount of time serializing Z3 ASTs to other smt or tptp solvers. Translating to egglog programs is easy.

This might be a nice approach for tools already integrated with z3 such as angr.

I had hoped it would be as easy as `t.sexpr()` but egglog's sexpr and smtlibs are not compatible. Still, not so bad. There is a lot of elbow grease left to proabbly clean this up to actually working but it gets the idea out there.

```python
! pip install egglog z3-solver
```

```python
import egglog.bindings as eggbnd
from z3 import *

Math = DeclareSort("Math")
add = Function("add", Math, Math, Math)
zero = Const("zero", Math)
one =  Const("one", Math)

sig = [Math, add, zero, one]

x,y = Consts("x y", Math)
add(zero,one) == one
rules =[
ForAll([x], add(x,zero) == x),
ForAll([x,y], add(x,y) == add(y,x)),
]

def z3_to_egglog(e, vars=[]):
    """ a simple sexpr traversal, but we wrap 0-arity constants in parens and vars in no parens to match egglog's syntax"""
    if e in vars:
        return e.sexpr()
    else:
        head, args = e.decl(), e.children()
        return f"({head.name()} {' '.join(z3_to_egglog(a, vars) for a in args)})"

from knuckledragger.utils import open_binder
def simp(e, rules, sig, n=10):
    """ generate an egglog program to simplify e using rules with a signature sig. We could collect sig by traversing stuff, but it's easier to just be handed it."""
    output = []
    for f in sig:
        if isinstance(f, z3.FuncDeclRef):
            dom = " ".join([f.domain(i).name() for i in range(f.arity())])
            output.append(f"(function {f.name()}  ({dom}) {f.range().name()})")
        elif isinstance(f, z3.SortRef):
            output.append(f"(datatype {f.name()})")
        elif isinstance(f, z3.ExprRef):
            output.append(f"(function {f.sexpr()} () {f.sort().name()})")
    for r in rules:
        assert r.is_forall()
        vs, r = open_binder(r)
        assert r.decl().name() == "="
        lhs, rhs = r.children()
        output.append(f"(rewrite {z3_to_egglog(lhs,vars=vs)} {z3_to_egglog(rhs, vars=vs)})")
    output.append(f"(let knuck_e {z3_to_egglog(e)})")
    output.append(f"(run {n})")
    output.append("(extract knuck_e)")
    return output


egraph = eggbnd.EGraph()
for c in simp(add(zero,one), rules, sig):
    print(c)
    commands = egraph.parse_program(c)
    res = egraph.run_program(*commands)
print(res)
```

    (datatype Math)
    (function add  (Math Math) Math)
    (function zero () Math)
    (function one () Math)
    (rewrite (add X (zero )) X)
    (rewrite (add X Y) (add Y X))
    (let knuck_e (add (zero ) (one )))
    (run 10)
    (extract knuck_e)
    ['(one)']

# Bits and Bobbles

I might need to parse back the egglog. There's a chance the sexpr reader can do it. Some kind of preludes might be necessary to deal with egglog primitives.
Some kind of smtlib prelude rules would be nice for egglog.
Bitvectors in particular. Arbitrary sized bitvectors in particular particular.

One of the ideas behind knuckledragger is bolt whatever solver I think I can trust into the kernel with as little overhead as possible. I just sort of want a system to track my calls to solvers that I feel chain together.

I've been backpedaling a little on this and focussing on Z3.

One thing that is very nice in a theorem proving setting is a simp tactic. What makes this tactic special is it's moding. It can do a little bit and produce a simplified goal. So it is something like a `theorem -> theorem` function instead of a `theorem -> Bool` function.

In the equational context, it is nice to not have to give both sides of the equation.

Similarly, I'm also quite intrigued at using maude <https://maude.cs.illinois.edu/wiki/The_Maude_System> , which is a remarkably advanced system that is undersung and misunderstood. It has AC rewriting. It has python bindings these days. <https://github.com/fadoss/maude-bindings> What more can one ask?

I also wrote a tptp printer and smtlib printer from z3's ast. I want to call vampire, eprover, twee and iether accept them as proofs (akin to why3 spread specturm) or try to extract clues from their proof output to help z3 along.
Also intuitionistic knuckledragger using leanCop is interesting.<https://jens-otten.de/provers.html> [https://leancop.de/nanocop/](https://www.leancop.de/nanocop-i/)  <https://leancop.de/ileancop/index.html> <https://jens-otten.de/provers.html#nanocop-i> <https://www.iltp.de/>

 <https://github.com/philzook58/knuckledragger/blob/a3334f6fc09209ee511268415f3ec0e01ca8bdd4/knuckledragger/utils.py#L34>

```python
def lemma_smt(thm: z3.BoolRef, by=[], sig=[]) -> list[str]:
    """
    Replacement for lemma that returns smtlib string for experimentation with other solvers
    """
    output = []
    output.append(";;declarations")
    for f in sig:
        if isinstance(f, z3.FuncDeclRef):
            output.append(f.sexpr())
        elif isinstance(f, z3.SortRef):
            output.append("(declare-sort " + f.sexpr() + " 0)")
        elif isinstance(f, z3.ExprRef):
            output.append(f.decl().sexpr())
    output.append(";;axioms")
    for e in by:
        if is_proof(e):
            output.append("(assert " + e.thm.sexpr() + ")")
    output.append(";;goal")
    output.append("(assert " + z3.Not(thm).sexpr() + ")")
    output.append("(check-sat)")
    return output


def open_binder(l: z3.QuantifierRef):
    vars = [
        z3.Const(l.var_name(i).upper(), l.var_sort(i))
        for i in reversed(range(l.num_vars()))
    ]
    return vars, z3.substitute_vars(l.body(), *vars)


def expr_to_tptp(expr: z3.ExprRef):
    if isinstance(expr, z3.IntNumRef):
        return str(expr.as_string())
    elif isinstance(expr, z3.QuantifierRef):
        vars, body = open_binder(expr)
        body = expr_to_tptp(body)
        vs = ", ".join([v.sexpr() + ":" + z3_sort_tptp(v.sort()) for v in vars])
        if expr.is_forall():
            return f"(![{vs}] : {body})"
        elif expr.is_exists():
            return f"(?[{vs}] : {body})"
        elif expr.is_lambda():
            return f"(^[{vs}] : {body})"
    children = list(map(expr_to_tptp, expr.children()))
    head = expr.decl().name()
    if head == "true":
        return "$true"
    elif head == "false":
        return "$false"
    elif head == "and":
        return "({})".format(" & ".join(children))
    elif head == "or":
        return "({})".format(" | ".join(children))
    elif head == "=":
        return "({} = {})".format(children[0], children[1])
    elif head == "=>":
        return "({} => {})".format(children[0], children[1])
    elif head == "not":
        return "~({})".format(children[0])
    elif head == "ite":
        return "$ite({}, {}, {})".format(*children)
    elif head == "<":
        return "$less({},{})".format(*children)
    elif head == "<=":
        return "$lesseq({},{})".format(*children)
    elif head == ">":
        return "$greater({},{})".format(*children)
    elif head == ">=":
        return "$greatereq({},{})".format(*children)
    elif head == "+":
        return "$sum({},{})".format(*children)
    elif head == "-":
        return "$difference({},{})".format(*children)
    elif head == "*":
        return "$product({},{})".format(*children)
    elif head == "/":
        return "$quotient({},{})".format(*children)
    else:
        if len(children) == 0:
            return head
        return f"{head}({', '.join(children)})"


z3.ExprRef.tptp = expr_to_tptp


def z3_sort_tptp(sort: z3.SortRef):
    match sort.name():
        case "Int":
            return "$int"
        case "Bool":
            return "$o"
        case "Real":
            return "$real"
        case "Array":
            return "({} > {})".format(
                z3_sort_tptp(sort.domain()), z3_sort_tptp(sort.range())
            )
        case x:
            return x.lower()


z3.SortRef.tptp = z3_sort_tptp


def lemma_tptp(thm: z3.BoolRef, by=[], sig=[], timeout=None, command=None):
    """
    Returns tptp strings
    """
    output = []
    for f in sig:
        if isinstance(f, z3.FuncDeclRef):
            dom = " * ".join([f.domain(i).tptp() for i in range(f.arity())])
            output.append(f"tff(sig, type, {f.name()} : ({dom}) > {f.range().tptp()}).")
        elif isinstance(f, z3.SortRef):
            output.append(f"tff(sig, type, {f.tptp()} : $tType).")
        elif isinstance(f, z3.ExprRef):
            output.append(f"tff(sig, type, {f.sexpr()} : {f.sort().tptp()}).")
    for e in by:
        if is_proof(e):
            output.append(f"tff(hyp, axiom, {e.thm.tptp()} ).")
    output.append(f"tff(goal,conjecture,{thm.tptp()} ).")
    if command == None:
        return output
    else:
        with open("/tmp/temp.p", "w") as f:
            f.writelines(output)
        command.append("/tmp/temp.p")
        res = subprocess.run(
            command,
            timeout=timeout,
            capture_output=True,
        )
        return res
```
