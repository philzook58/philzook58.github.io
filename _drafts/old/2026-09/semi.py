from dataclasses import dataclass
from collections import Counter, deque
from typing import ClassVar, Optional


class MS(tuple):
    # multiset
    def __new__(cls, xs=()):
        return super().__new__(cls, sorted(xs))

    def __lt__(self, other):
        return (len(self), tuple(self)) < (len(other), tuple(other))


@dataclass(frozen=True, slots=True, init=False)
class Semi:
    outer_order: ClassVar[str] = "multilex"
    # Store coefficients instead of repeating monomials.  The old representation
    # made 16*x a tuple containing sixteen copies of ("x",).
    terms: tuple[tuple[MS[str], int], ...]

    def __init__(self, monoms=()):
        counts = Counter(MS(m) for m in monoms)
        object.__setattr__(self, "terms", tuple(sorted(counts.items())))

    @classmethod
    def from_counter(cls, counts: Counter) -> "Semi":
        obj = object.__new__(cls)
        object.__setattr__(
            obj,
            "terms",
            tuple(sorted((MS(m), n) for m, n in counts.items() if n > 0)),
        )
        return obj

    @property
    def monoms(self) -> MS[MS[str]]:
        # Compatibility for notebook exploration.  Core operations use `terms`
        # and never expand coefficients this way.
        return MS(m for m, n in self.terms for _ in range(n))

    @staticmethod
    def _lex_runs(a, b, reverse=False) -> bool:
        """Compare expanded monomial sequences without expanding coefficients."""
        aa = tuple(reversed(a)) if reverse else a
        bb = tuple(reversed(b)) if reverse else b
        i = j = 0
        ca = cb = 0
        while i < len(aa) and j < len(bb):
            ma, na = aa[i]
            mb, nb = bb[j]
            if ma != mb:
                return ma < mb
            if ca == 0:
                ca = na
            if cb == 0:
                cb = nb
            used = min(ca, cb)
            ca -= used
            cb -= used
            if ca == 0:
                i += 1
            if cb == 0:
                j += 1
        return i == len(aa) and j != len(bb)

    @staticmethod
    def lit(name) -> "Semi":
        return Semi([[name]])

    @staticmethod
    def of_int(n: int) -> "Semi":
        assert n >= 0
        return Semi.from_counter(Counter({MS(): n}))

    def __add__(self, other: "Semi") -> "Semi":
        if isinstance(other, int):
            other = Semi.of_int(other)
        counts = Counter(dict(self.terms))
        counts.update(dict(other.terms))
        return Semi.from_counter(counts)

    def __radd__(self, other: int) -> "Semi":
        return Semi.of_int(other) + self

    def __pow__(self, n: int) -> "Semi":
        assert n >= 0
        if n == 0:
            return Semi.of_int(1)
        result = self
        for _ in range(n - 1):
            result *= self
        return result

    def __mul__(self, other: "Semi") -> "Semi":
        counts = Counter()
        for m1, n1 in self.terms:
            for m2, n2 in other.terms:
                counts[MS(m1 + m2)] += n1 * n2
        return Semi.from_counter(counts)

    def __rmul__(self, other: int) -> "Semi":
        return Semi.of_int(other) * self

    def __repr__(self) -> str:
        pieces = []
        for m, n in self.terms:
            term = " ".join(m) if m else "1"
            pieces.extend([term] * n)
        return " + ".join(pieces)

    def __lt__(self, other: "Semi") -> bool:
        if Semi.outer_order == "multilex":
            return self._lex_runs(self.terms, other.terms, reverse=True)
        return self._lex_runs(self.terms, other.terms)

    def __sub__(self, other: "Semi") -> Optional["Semi"]:
        counts = Counter(dict(self.terms))
        for m, n in other.terms:
            if counts[m] < n:
                return None
            counts[m] -= n
        return Semi.from_counter(counts)

    def divrem(self, other: "Semi") -> tuple["Semi", "Semi"]:
        # returns largest q such that self = q*other + r
        assert isinstance(other, Semi)
        if not other.terms:
            raise ValueError("division by zero")
        q = Counter()
        r = Counter(dict(self.terms))
        lm = other.terms[-1][0]
        i = len(r) - 1
        while i >= 0:
            rms = sorted(m for m, n in r.items() if n > 0)
            if i >= len(rms):
                i = len(rms) - 1
            if i < 0:
                break
            rm = rms[i]
            qm = list(rm)
            for x in lm:
                if x not in qm:
                    break
                qm.remove(x)
            else:
                qm = MS(qm)
                shifted = [(MS(qm + m), n) for m, n in other.terms]
                copies = min(r[m] // n for m, n in shifted)
                if copies:
                    q[qm] += copies
                    for m, n in shifted:
                        r[m] -= copies * n
                    i = len(r)
                    continue
            i -= 1
        return Semi.from_counter(q), Semi.from_counter(r)

    def overlaps(self, other) -> list["Semi"]:
        # return all nontrivial overlaps of self and other
        # such that ov = q1 * self + r1 and ov = q2 * other + r2
        # ov is less that lm(self) * lm(other) ?
        res = []
        seen = set()
        for (q, r), _ in self.overlaps_qr(other):
            ov = q * self + r
            if ov not in seen:
                seen.add(ov)
                res.append(ov)
        return res

    def overlaps_qr(
        self, other
    ) -> list[tuple[tuple["Semi", "Semi"], tuple["Semi", "Semi"]]]:
        # Polynomial contexts split additively, so align one monomial occurrence.
        res = []
        for m1, _ in self.terms:
            for m2, _ in other.terms:
                cm = Counter(m1) | Counter(m2)
                qm1 = MS((cm - Counter(m1)).elements())
                qm2 = MS((cm - Counter(m2)).elements())
                q1, q2 = Semi([qm1]), Semi([qm2])
                t1, t2 = q1 * self, q2 * other
                c1, c2 = Counter(dict(t1.terms)), Counter(dict(t2.terms))
                ov = Semi.from_counter(c1 | c2)
                qr = ((q1, ov - t1), (q2, ov - t2))
                if qr not in res:
                    res.append(qr)
        return res


# hypothesis tests to check supposed properties


@dataclass(frozen=True, slots=True)
class Eq:  # It is itself a multiset
    lhs: Semi
    rhs: Semi


type Rewrites = list["Rewrite"]


def reduce(semi: Semi, rewrites: Rewrites) -> Semi:
    while True:
        for rw in rewrites:
            q, r = semi.divrem(rw.lhs)
            res = q * rw.rhs + r
            if res != semi:
                semi = res
                break
        else:
            return semi


@dataclass(slots=True)
class Rewrite:  # It is itself a multiset
    lhs: Semi
    rhs: Semi
    mark: bool = False

    def __init__(self, lhs: Semi, rhs: Semi, mark: bool = False):
        if lhs < rhs:
            lhs, rhs = rhs, lhs
        self.lhs, self.rhs, self.mark = lhs, rhs, mark

    def __str__(self) -> str:
        return f"{self.lhs} -> {self.rhs}"


def naive_complete(eqs: list[Eq]) -> list[Rewrite]:
    # naive completion algorithm
    pending = list(eqs)
    rws = []
    # in loop, reduce equations and add reduced oreitned form to rewrites
    while pending:
        eq = pending.pop(0)
        lhs, rhs = reduce(eq.lhs, rws), reduce(eq.rhs, rws)
        if lhs == rhs:
            continue
        rw = Rewrite(lhs, rhs)
        if rw in rws:
            continue
        # add all overlaps of rewrite lhs to equations
        rules = rws + [rw]
        for rw1 in rules:
            for (q, r), (q1, r1) in rw.lhs.overlaps_qr(rw1.lhs):
                lhs = reduce(q * rw.rhs + r, rules)
                rhs = reduce(q1 * rw1.rhs + r1, rules)
                eq = Eq(lhs, rhs)
                if lhs != rhs and eq not in pending:
                    pending.append(eq)
        rws.append(rw)
    return rws


def huet_complete(eqs: list[Eq]) -> list[Rewrite]:
    # huet completion algorithm without marking
    # similar to previous
    # keep equations
    E, R = list(eqs), []
    while True:
        # reduce lhs, rhs according to R
        while E:
            eq = E.pop()
            lhs, rhs = reduce(eq.lhs, R), reduce(eq.rhs, R)
            if lhs == rhs:
                continue
            rw = Rewrite(lhs, rhs)

            # collapse old left sides and compose old right sides
            R1 = [rw]
            for rw1 in R:
                lhs1 = reduce(rw1.lhs, [rw])
                if lhs1 == rw1.lhs:
                    rhs1 = reduce(rw1.rhs, R + [rw])
                    if rw1.lhs != rhs1:
                        R1.append(Rewrite(rw1.lhs, rhs1))
                else:
                    E.append(Eq(lhs1, rw1.rhs))
            R = R1

        # create all critical pairs; marking would avoid redoing old pairs
        for i, rw in enumerate(R):
            for rw1 in R[: i + 1]:
                for (q, r), (q1, r1) in rw.lhs.overlaps_qr(rw1.lhs):
                    lhs = reduce(q * rw.rhs + r, R)
                    rhs = reduce(q1 * rw1.rhs + r1, R)
                    eq = Eq(lhs, rhs)
                    if lhs != rhs and eq not in E:
                        E.append(eq)
        if not E:
            return R


def huet_marked(eqs: list[Eq], goal: Optional[Eq] = None) -> list[Rewrite]:
    # the same as the above, but keep a bool in rewrite indicating if it is marked
    # the critical pair generation process picks one unwarked rules and generates critical pairs with all other rules, marking the rule after generating its critical pairs
    # if there are no unmarked rules, the algorithm terminates
    E, R = list(eqs), []
    while True:
        while E:
            eq = E.pop()
            lhs, rhs = reduce(eq.lhs, R), reduce(eq.rhs, R)
            if lhs == rhs:
                continue
            rw = Rewrite(lhs, rhs)

            R1 = [rw]
            for rw1 in R:
                lhs1 = reduce(rw1.lhs, [rw])
                if lhs1 == rw1.lhs:
                    rhs1 = reduce(rw1.rhs, R + [rw])
                    if rw1.lhs != rhs1:
                        R1.append(Rewrite(rw1.lhs, rhs1, rw1.mark))
                else:
                    E.append(Eq(lhs1, rw1.rhs))
            R = R1

            # Completion can be infinite even when the particular word problem
            # is already solved.  Equality after reduction by the current rules
            # is sound, so a goal-directed run may stop here.
            if goal is not None and reduce(goal.lhs, R) == reduce(goal.rhs, R):
                return R

        for rw in R:
            if not rw.mark:
                break
        else:
            return R

        rw.mark = True
        for rw1 in R:
            for (q, r), (q1, r1) in rw.lhs.overlaps_qr(rw1.lhs):
                lhs = reduce(q * rw.rhs + r, R)
                rhs = reduce(q1 * rw1.rhs + r1, R)
                eq = Eq(lhs, rhs)
                if lhs != rhs and eq not in E:
                    E.append(eq)


def _monom_quotient(big: MS, small: MS) -> Optional[MS]:
    """Return q when big = q*small, or None when small does not divide big."""
    q = list(big)
    for x in small:
        if x not in q:
            return None
        q.remove(x)
    return MS(q)


def rewrite_once(semi: Semi, eqs: list[Eq]):
    """Apply one equation in one monomial context, in either direction."""
    seen = set()
    for eq_index, eq in enumerate(eqs):
        for reverse, (old, new) in enumerate(((eq.lhs, eq.rhs), (eq.rhs, eq.lhs))):
            # Equations with an empty side need a separate bounded insertion rule.
            if not old.terms:
                continue
            for pm, _ in semi.terms:
                for om, _ in old.terms:
                    qm = _monom_quotient(pm, om)
                    if qm is None:
                        continue
                    context = Semi([qm])
                    rest = semi - context * old
                    if rest is None:
                        continue
                    result = rest + context * new
                    if result not in seen:
                        seen.add(result)
                        yield result, (eq_index, bool(reverse), qm)


def congruence_path(
    start: Semi,
    goal: Semi,
    eqs: list[Eq],
    *,
    max_degree: int,
    max_terms: int,
) -> Optional[list[Semi]]:
    """Bounded bidirectional search for a ground semiring-equational proof.

    `None` means no path was found within the bounds, not that the equation is
    false.  Each adjacent pair in a returned path differs by one use of an input
    equation in an additive and monomial multiplicative context.
    """

    def in_bounds(p: Semi) -> bool:
        return (
            all(len(m) <= max_degree for m, _ in p.terms)
            and sum(n for _, n in p.terms) <= max_terms
        )

    if start == goal:
        return [start]
    front = {start: None}
    back = {goal: None}
    front_queue, back_queue = deque([start]), deque([goal])

    while front_queue and back_queue:
        if len(front_queue) <= len(back_queue):
            here, there, queue = front, back, front_queue
        else:
            here, there, queue = back, front, back_queue

        for _ in range(len(queue)):
            semi = queue.popleft()
            for result, step in rewrite_once(semi, eqs):
                if not in_bounds(result) or result in here:
                    continue
                here[result] = (semi, step)
                if result in there:
                    left = []
                    p = result
                    while p is not None:
                        left.append(p)
                        parent = front[p]
                        p = None if parent is None else parent[0]
                    left.reverse()

                    right = []
                    p = result
                    while back[p] is not None:
                        p = back[p][0]
                        right.append(p)
                    return left + right
                queue.append(result)
    return None
