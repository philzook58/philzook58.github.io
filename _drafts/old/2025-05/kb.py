import z3 as smt
from typing import Optional, NamedTuple
from collections import defaultdict
from enum import Enum


###### AST HELPERS


def occurs(x: smt.ExprRef, t: smt.ExprRef) -> bool:
    """Does x occur in t?

    >>> x,y,z = smt.Ints("x y z")
    >>> assert occurs(x + y, x + y + z)
    >>> assert not occurs(x + y, x + z)
    >>> assert occurs(x, x + y + z)
    >>> v0 = smt.Var(0, smt.IntSort())
    >>> assert occurs(v0, v0 + x + y)
    """
    # TODO: Not alpha invariant, doesn't handle binders
    if x.eq(t):
        return True
    elif smt.is_app(t):
        return any(occurs(x, t.arg(i)) for i in range(t.num_args()))
    elif smt.is_quantifier(t):
        raise Exception("occurs check quantifier unimplemented", t)
    elif smt.is_var(t):
        return False
    else:
        raise Exception("Unexpected term in occurs check", t)


def unify(
    vs: list[smt.ExprRef], p1: smt.ExprRef, p2: smt.ExprRef
) -> Optional[dict[smt.ExprRef, smt.ExprRef]]:
    """Unification"""
    subst = {}
    todo = [(p1, p2)]

    def is_var(x):
        return any(x.eq(v) for v in vs)

    while todo:
        p1, p2 = todo.pop()  # we could pop _any_ of the todos, not just the top.
        if p1.eq(p2):  # delete
            continue
        elif is_var(p1):  # elim
            if occurs(p1, p2):
                return None
            todo = [
                (smt.substitute(t1, (p1, p2)), smt.substitute(t2, (p1, p2)))
                for (t1, t2) in todo
            ]
            subst = {k: smt.substitute(v, (p1, p2)) for k, v in subst.items()}
            subst[p1] = p2
        elif is_var(p2):  # orient
            todo.append((p2, p1))
        elif smt.is_app(p1):  # decompose
            if not smt.is_app(p2) or p1.decl() != p2.decl():
                return None
            todo.extend(zip(p1.children(), p2.children()))
        else:
            raise Exception("unexpected case", p1, p2)
    return subst


def open_binder(lam: smt.QuantifierRef) -> tuple[list[smt.ExprRef], smt.ExprRef]:
    """
    Open a quantifier with fresh variables. This achieves the locally nameless representation
    https://chargueraud.org/research/2009/ln/main.pdf
    where it is harder to go wrong.

    >>> x = smt.Int("x")
    >>> open_binder(smt.ForAll([x], x > 0))
    ([X!...], X!... > 0)
    """
    # Open with capitalized names to match tptp conventions
    vs = [
        smt.FreshConst(lam.var_sort(i), prefix=lam.var_name(i).upper().split("!")[0])
        for i in range(lam.num_vars())
    ]
    return vs, smt.substitute_vars(lam.body(), *reversed(vs))


def quant_kind_eq(t1: smt.QuantifierRef, t2: smt.QuantifierRef) -> bool:
    """Check both quantifiers are of the same kind

    >>> x = smt.Int("x")
    >>> forall = smt.ForAll([x], x > 0)
    >>> exists = smt.Exists([x], x > 0)
    >>> lamb = smt.Lambda([x], x > 0)
    >>> assert quant_kind_eq(forall, forall)
    >>> assert quant_kind_eq(exists, exists)
    >>> assert quant_kind_eq(lamb, lamb)
    >>> assert not quant_kind_eq(forall, exists)
    """
    # TODO: could make a faster version using Z3 kind tags
    return (
        t1.is_forall() == t2.is_forall()
        and t1.is_exists() == t2.is_exists()
        and t1.is_lambda() == t2.is_lambda()
    )


def alpha_eq(t1, t2):
    """
    Alpha equivalent equality.
    Z3's fast built-in t.eq is not alpha invariant.

    >>> x,y = smt.Ints("x y")
    >>> t1,t2 = smt.Lambda([x], x), smt.Lambda([y], y)
    >>> t1.eq(t2) # syntactic equality
    False
    >>> alpha_eq(t1, t2)
    True
    >>> alpha_eq(smt.Lambda([x], x)[3], smt.IntVal(3)) # No beta equivalence
    False
    """
    if t1.eq(t2):  # fast path
        return True
    # elif (smt.is_ground(t1) or smt.is_ground(t2)) and not t1.eq(t2): TODO: Needs is_ground threaded up from C API to python API.
    #    return False
    elif smt.is_quantifier(t1):
        if (
            smt.is_quantifier(t2)
            and quant_kind_eq(t1, t2)
            and t1.num_vars() == t2.num_vars()
            and [t1.var_sort(i) == t2.var_sort(i) for i in range(t1.num_vars())]
        ):
            # It is ok to keep de bruijn indices here and not use open_binder?
            # vs, body1 = open_binder(t1)
            # body2 = smt.substitute_vars(t2.body(), *reversed(vs))
            # return alpha_eq(body1, body2)
            return alpha_eq(t1.body(), t2.body())
        else:
            return False
    elif smt.is_app(t1):
        if smt.is_app(t2) and t1.decl() == t2.decl():
            return all(alpha_eq(t1.arg(i), t2.arg(i)) for i in range(t1.num_args()))
        else:
            return False
    elif smt.is_var(t1):
        return (
            smt.is_var(t2)
            and smt.get_var_index(t1) == smt.get_var_index(t2)
            and t1.sort() == t2.sort()
        )  # sort check is probably redundant if quantifier bound?
    else:
        raise Exception("Unexpected terms in alpha_eq", t1, t2)
    # could instead maybe use a solver check or simplify tactic on Goal(t1 == t2)


def pmatch(
    vs: list[smt.ExprRef], pat: smt.ExprRef, t: smt.ExprRef, subst=None
) -> Optional[dict[smt.ExprRef, smt.ExprRef]]:
    """
    Pattern match t against pat considering vs as variables. Returns substitution dictionary if succeeds
    https://www.philipzucker.com/ho_unify/
    """
    if pat.sort() != t.sort():
        return None
    if subst is None:
        subst = {}
    todo = [(pat, t)]
    no_escape = []

    def is_var(x):
        return any(x.eq(v) for v in vs)

    def check_escape(x):
        if any(x.eq(v) for v in no_escape):
            return False
        else:
            return all(check_escape(c) for c in x.children())

    while todo:
        pat, t = todo.pop()
        if is_var(pat):  # regular pattern
            if pat in subst:
                if not alpha_eq(subst[pat], t):
                    return None
            else:
                if check_escape(t):  # check_escape is relative of occurs_check
                    subst[pat] = t
                else:
                    return None
        elif smt.is_select(pat) and is_var(pat.arg(0)):
            #  higher order pattern. "select" is smt speak for apply.
            # F[x,y,z] = t ---> F = Lambda([x,y,z], t)
            F = pat.arg(0)
            allowedvars = pat.children()[1:]
            """
            if any(
                v not in no_escape for v in allowedvars
            ):  # TODO: this is probably wrong
                raise Exception(
                    "Improper higher order pattern", pat
                )  # we could relax this to do syntactic unification here.
            """
            # By commenting this out, I've enabled non obviously bound constants
            # other option: Just lift them all out.
            # smt.subsitute(t, *[zip(a,a.FreshConst("")) for a for allowed_vars])
            t1 = smt.Lambda(allowedvars, t)
            todo.append((F, t1))
        elif smt.is_app(pat):
            nargs = pat.num_args()
            if not smt.is_app(t) or pat.decl() != t.decl():  # or nargs != t.num_args():
                return None
            for i in range(nargs):
                todo.append((pat.arg(i), t.arg(i)))
        elif isinstance(pat, smt.QuantifierRef):
            if (
                not isinstance(t, smt.QuantifierRef)
                or not quant_kind_eq(t, pat)
                or t.num_vars() != pat.num_vars()
                or any(t.var_sort(i) != pat.var_sort(i) for i in range(t.num_vars()))
            ):
                return None
            vs1, patbody = open_binder(pat)
            no_escape.extend(vs1)
            tbody = smt.substitute_vars(t.body(), *reversed(vs1))
            todo.append((patbody, tbody))
        else:
            raise Exception("Unexpected pattern", t, pat)
    return subst


def rewrite1(
    t: smt.ExprRef, vs: list[smt.ExprRef], lhs: smt.ExprRef, rhs: smt.ExprRef
) -> Optional[smt.ExprRef]:
    """
    Rewrite at root a single time.
    """
    subst = pmatch(vs, lhs, t)
    if subst is not None:
        return smt.substitute(rhs, *subst.items())
    return None


class RewriteRuleException(Exception): ...


class RewriteRule(NamedTuple):
    """A rewrite rule tuple"""

    vs: list[smt.ExprRef]
    lhs: smt.ExprRef
    rhs: smt.ExprRef

    def freshen(self) -> "RewriteRule":
        """Freshen the rule by renaming variables.

        >>> x,y= smt.Reals("x y")
        >>> rule = RewriteRule([x,y], x*y, y*x)
        >>> rule.freshen()
        RewriteRule(vs=[x..., y...], lhs=x...*y..., rhs=y...*x..., pf=None)
        """
        vs1 = [smt.FreshConst(v.sort(), prefix=v.decl().name()) for v in self.vs]
        return RewriteRule(
            vs1,
            lhs=smt.substitute(self.lhs, *zip(self.vs, vs1)),
            rhs=smt.substitute(self.rhs, *zip(self.vs, vs1)),
        )

    def to_expr(self):
        """Convert the rule to a theorem of form `forall vs, lhs = rhs`.

        >>> x,y = smt.Reals("x y")
        >>> RewriteRule([x,y], x*y, y*x).to_expr()
        ForAll([x, y], x*y == y*x)
        """
        if len(self.vs) == 0:
            return self.lhs == self.rhs
        else:
            return smt.ForAll(self.vs, self.lhs == self.rhs)

    @classmethod
    def from_expr(cls, expr: smt.BoolRef | smt.QuantifierRef) -> "RewriteRule":
        """Convert a theorem of form `forall vs, lhs = rhs` to a rule."""
        return rewrite_of_expr(expr)


def rewrite1_rule(
    t: smt.ExprRef,
    rule: RewriteRule,
    trace: Optional[list[tuple[RewriteRule, dict[smt.ExprRef, smt.ExprRef]]]] = None,
) -> Optional[smt.ExprRef]:
    """
    Rewrite at root a single time.
    """
    subst = pmatch(rule.vs, rule.lhs, t)
    if subst is not None:
        if trace is not None:
            trace.append((rule, subst))
        return smt.substitute(rule.rhs, *subst.items())
    return None


def rewrite_of_expr(thm: smt.BoolRef | smt.QuantifierRef) -> RewriteRule:
    """
    Unpack theorem of form `forall vs, lhs = rhs` into a Rule tuple

    >>> x = smt.Real("x")
    >>> rewrite_of_expr(smt.ForAll([x], x**2 == x*x))
    RewriteRule(vs=[X...], lhs=X...**2, rhs=X...*X...)
    """
    vs = []
    thm1 = thm  # to help out pyright
    while isinstance(thm1, smt.QuantifierRef):
        if thm1.is_forall():
            vs1, thm1 = open_binder(thm1)
            vs.extend(vs1)
        else:
            raise RewriteRuleException("Not a universal quantifier", thm1)
    if not smt.is_eq(thm1):
        raise RewriteRuleException("Not an equation", thm)
    assert isinstance(thm1, smt.ExprRef)  # pyright
    lhs, rhs = thm1.children()
    return RewriteRule(vs, lhs, rhs)


def rewrite(
    t: smt.ExprRef,
    rules: list[smt.BoolRef | smt.QuantifierRef],
    trace=None,
) -> smt.ExprRef:
    """
    Repeat rewrite until no more rewrites are possible.

    >>> x,y,z = smt.Reals("x y z")
    >>> unit = kd.prove(smt.ForAll([x], x + 0 == x))
    >>> x + 0 + 0 + 0 + 0
    x + 0 + 0 + 0 + 0
    >>> rewrite(x + 0 + 0 + 0 + 0, [unit])
    x
    """
    rules1 = [
        rule if isinstance(rule, RewriteRule) else rewrite_of_expr(rule)
        for rule in rules
    ]
    db = defaultdict(list)
    for rule in rules1:
        db[rule.lhs.decl()].append(rule)

    # @functools.cache
    def worker(e):
        while True:
            if smt.is_app(e):
                decl = e.decl()
                children = [worker(c) for c in e.children()]
                e = decl(*children)
                rules = db.get(decl, ())
                done = True
                for rule in rules:
                    res = rewrite1_rule(e, rule, trace=trace)
                    if res is not None:
                        e = res
                        done = False
                        break
                if done:
                    return e
            else:
                return e

    return worker(t)


#### KNUTH BENDIX STUFF


class Order(Enum):
    EQ = 0  # Equal
    GR = 1  # Greater
    NGE = 2  # Not Greater or Equal


def lpo(vs: list[smt.ExprRef], t1: smt.ExprRef, t2: smt.ExprRef) -> Order:
    """
    Lexicographic path ordering.
    Based on https://www21.in.tum.de/~nipkow/TRaAT/programs/termorders.ML
    TODO add ordering parameter.
    """

    def is_var(x):
        return any(x.eq(v) for v in vs)

    if is_var(t2):
        if t1.eq(t2):
            return Order.EQ
        elif occurs(t2, t1):
            return Order.GR
        else:
            return Order.NGE
    elif is_var(t1):
        return Order.NGE
    elif smt.is_app(t1) and smt.is_app(t2):
        decl1, decl2 = t1.decl(), t2.decl()
        args1, args2 = t1.children(), t2.children()
        if all(lpo(vs, a, t2) == Order.NGE for a in args1):
            if decl1 == decl2:
                if all(lpo(vs, t1, a) == Order.GR for a in args2):
                    for a1, a2 in zip(args1, args2):
                        ord = lpo(vs, a1, a2)
                        if ord == Order.GR:
                            return Order.GR
                        elif ord == Order.NGE:
                            return Order.NGE
                    return Order.EQ
                else:
                    return Order.NGE
            elif (decl1.name(), decl1.get_id()) > (decl2.name(), decl2.get_id()):
                if all(lpo(vs, t1, a) == Order.GR for a in args2):
                    return Order.GR
                else:
                    return Order.NGE

            else:
                return Order.NGE
        else:
            return Order.GR
    else:
        raise Exception("Unexpected terms in lpo", t1, t2)


def kbo(vs: list[smt.ExprRef], t1: smt.ExprRef, t2: smt.ExprRef) -> Order:
    """
    Knuth Bendix Ordering, naive implementation.
    All weights are 1.
    Source: Term Rewriting and All That section 5.4.4
    """
    if t1.eq(t2):
        return Order.EQ

    def is_var(x):
        return any(x.eq(v) for v in vs)

    def vcount(t):
        todo = [t]
        vcount1 = {v: 0 for v in vs}
        while todo:
            t = todo.pop()
            if is_var(t):
                vcount1[t] += 1
            elif smt.is_app(t):
                todo.extend(t.children())
        return vcount1

    vcount1, vcount2 = vcount(t1), vcount(t2)
    if not all(vcount1[v] >= vcount2[v] for v in vs):
        return Order.NGE

    def weight(t):
        todo = [t]
        w = 0
        while todo:
            t = todo.pop()
            w += 1
            if smt.is_app(t):
                todo.extend(t.children())
        return w

    w1, w2 = weight(t1), weight(t2)
    if w1 > w2:
        return Order.GR
    elif w1 < w2:
        return Order.NGE
    else:
        if is_var(t2):  # KBO2a
            decl = t1.decl()
            if decl.arity() != 1:
                return Order.NGE
            while not t1.eq(t2):
                if t1.decl() != decl:
                    return Order.NGE
                else:
                    t1 = t1.arg(0)
            return Order.GR
        elif is_var(t1):
            return Order.NGE
        elif smt.is_app(t1) and smt.is_app(t2):
            decl1, decl2 = t1.decl(), t2.decl()
            if decl1 == decl2:  # KBO2c
                args1, args2 = t1.children(), t2.children()
                for a1, a2 in zip(args1, args2):
                    ord = kbo(vs, a1, a2)
                    if ord == Order.GR:
                        return Order.GR
                    elif ord == Order.NGE:
                        return Order.NGE
                raise Exception("Unexpected equality reached in kbo")
            elif (decl1.name(), decl1.get_id()) > (
                decl2.name(),
                decl2.get_id(),
            ):  # KBO2b
                return Order.GR
            else:
                return Order.NGE
        else:
            raise Exception("Unexpected terms in kbo", t1, t2)


def critical_pair_helper(
    vs: list[smt.ExprRef], t: smt.ExprRef, lhs: smt.ExprRef, rhs: smt.ExprRef
) -> list[tuple[smt.ExprRef, dict[smt.ExprRef, smt.ExprRef]]]:
    """
    Look for pattern lhs to unify with a subterm of t.
    returns a list of all of those lhs -> rhs applied + the substitution resulting from the unification.
    The substitution is so that we can apply the other `t -> s` rule once we return.


    This helper is asymmettric between t and lhs. You need to call it twice to get all critical pairs.
    """
    res = []
    if any(
        t.eq(v) for v in vs
    ):  # Non trivial overlap only `X ~ lhs` is not interesting.
        return res
    subst = unify(vs, t, lhs)
    if subst is not None:
        res.append((rhs, subst))
    f, children = t.decl(), t.children()
    for n, arg in enumerate(children):
        # recurse into subterms and lift result under f if found something
        for s, subst in critical_pair_helper(vs, arg, lhs, rhs):
            args = children[:n] + [s] + children[n + 1 :]
            res.append((f(*args), subst))
    return res


def all_pairs(rules):
    """
    Find all the ways the left hand side of two rules can overlap.
    Return a derived equation

    """
    # TODO. I'm not treating encompassment correctly
    res = []
    for rule1 in rules:
        for rule2 in rules:
            # we're double counting when rule1 = rule2 but whatever
            if any(v1.eq(v2) for v1 in rule1.vs for v2 in rule2.vs):
                rule2 = rule2.freshen()
            vs = rule1.vs + rule2.vs
            for t, subst in critical_pair_helper(vs, rule1.lhs, rule2.lhs, rule2.rhs):
                # print(rule1, rule2, t, subst)
                apply_rule1 = smt.substitute(rule1.rhs, *subst.items())
                apply_rule2 = smt.substitute(t, *subst.items())
                vs1 = list(set(vs) - set(subst.keys()))
                if len(vs1) == 0:
                    res.append(apply_rule1 == apply_rule2)
                else:
                    res.append(
                        smt.ForAll(vs1, apply_rule1 == apply_rule2)
                    )  # new derived equation
    return res


def orient(eq: smt.BoolRef | smt.QuantifierRef, order=kbo) -> RewriteRule:
    r = rewrite_of_expr(eq)
    if order(r.vs, r.lhs, r.rhs) == Order.GR:
        return r
    elif order(r.vs, r.rhs, r.lhs) == Order.GR:
        return r._replace(lhs=r.rhs, rhs=r.lhs)
    else:
        raise Exception("Cannot orient: " + str(eq))


def simplify(
    t: smt.BoolRef | smt.QuantifierRef, rules: list[RewriteRule]
) -> smt.ExprRef:
    r = rewrite_of_expr(t)
    lhs = rewrite(r.lhs, rules)
    rhs = rewrite(r.rhs, rules)
    return r._replace(lhs=lhs, rhs=rhs).to_expr()


def is_trivial(t):
    r = rewrite_of_expr(t)
    return r.lhs.eq(r.rhs)


def basic(E, order=kbo):
    R = []
    for eq in E:
        R.append(orient(eq, order=order))
        # print("new", R[-1])
    i = 0
    done = False
    # print("pairing")
    while not done:
        done = True
        # print(R)
        for eq in all_pairs(R):
            # print(eq)
            eq1 = simplify(eq, R)
            if not is_trivial(eq1):
                # print("orig", eq,  "\nsimp", eq1)
                R.append(orient(eq1))
                # print("new", R[-1])
                done = False
        i += 1
    return R


def huet(E, order=kbo):
    E = E.copy()
    R = []
    while True:
        while E:
            eq = E.pop()
            eq = simplify(eq, R)
            if is_trivial(eq):
                continue
            r = orient(eq, order=order)
            Rnew = [r]
            for r1 in R:
                lhs1 = rewrite(r1.lhs, [r])
                if lhs1.eq(r1.lhs):
                    rhs1 = rewrite(r1.rhs, R + [r])
                    Rnew.append(r1._replace(rhs=rhs1))
                else:
                    E.append(r1._replace(lhs=lhs1).to_expr())
            R = Rnew
        # print(R)
        for eq in all_pairs(R):
            # by marking rules, we can prune the critical pair search, but I haven't done that
            # This is something like a semi-naive or given clause optimization
            # Always smash against at least 1 fresh new thing (rule in this case).
            # It might help a lot. Perfomance benchmarking suggests simplify is the bottleneck
            eq1 = simplify(eq, R)
            if not is_trivial(eq1):
                E.append(eq1)
                # break
        if len(E) == 0:
            return R
        # print(E[-1])


T = smt.DeclareSort("AbstractGroup")
x, y, z = smt.Consts("x y z", T)
e = smt.Const("a_e", T)
inv = smt.Function("c_inv", T, T)
mul = smt.Function("b_mul", T, T, T)

E = [
    smt.ForAll([x], mul(e, x) == x),
    # adding in these other redundant axioms makes it easier on the system
    # smt.ForAll([x], x * e == x),
    # smt.ForAll([x], x * inv(x) == e),
    smt.ForAll([x], mul(inv(x), x) == e),
    smt.ForAll([x, y, z], mul(mul(x, y), z) == mul(x, mul(y, z))),
    # smt.ForAll([x,y], inv(x * y) == inv(y) * inv(x))
]

print("Running Completion on \n", E)
print("Completed System:\n", huet(E, order=lpo))
