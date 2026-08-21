from dataclasses import dataclass, field
from collections import Counter
from typing import ClassVar, Optional


class MS(tuple):
    # multiset
    def __new__(cls, xs=()):
        return super().__new__(cls, sorted(xs))

    def __lt__(self, other):
        return (len(self), tuple(self)) < (len(other), tuple(other))


@dataclass
class Semi:
    outer_order: ClassVar[str] = "multilex"
    monoms: MS[MS[str]] = field(default_factory=MS)

    def __post_init__(self):
        self.monoms = MS(MS(m) for m in self.monoms)

    @staticmethod
    def lit(name) -> "Semi":
        return Semi([[name]])

    @staticmethod
    def of_int(n: int) -> "Semi":
        assert n >= 0
        if n == 0:
            return Semi([])
        elif n == 1:
            return Semi([[]])
        else:
            return Semi([[]]) + Semi.of_int(n - 1)

    def __add__(self, other: "Semi") -> "Semi":
        if isinstance(other, int):
            other = Semi.of_int(other)
        return Semi(MS((MS(self.monoms + other.monoms))))

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
        return Semi(MS(MS(m1 + m2) for m1 in self.monoms for m2 in other.monoms))

    def __rmul__(self, other: int) -> "Semi":
        return Semi.of_int(other) * self

    def __repr__(self) -> str:
        return " + ".join([" ".join(m) if m else "1" for m in self.monoms])

    def __lt__(self, other: "Semi") -> bool:
        if Semi.outer_order == "multilex":
            return tuple(reversed(self.monoms)) < tuple(reversed(other.monoms))
        return self.monoms < other.monoms

    def __sub__(self, other: "Semi") -> Optional["Semi"]:
        res = list(self.monoms)
        for m in other.monoms:
            if m in res:
                res.remove(m)
            else:
                return None
        return Semi(MS(res))

    def divrem(self, other: "Semi") -> tuple["Semi", "Semi"]:
        # returns largest q such that self = q*other + r
        assert isinstance(other, Semi)
        if len(other.monoms) == 0:
            raise ValueError("division by zero")
        q = []
        r = self
        lm = other.monoms[-1]
        i = len(r.monoms) - 1
        while i >= 0:
            qm = list(r.monoms[i])
            for x in lm:
                if x not in qm:
                    break
                qm.remove(x)
            else:
                term = Semi([qm])
                r1 = r - term * other
                if r1 is not None:
                    q.append(MS(qm))
                    r = r1
                    i = len(r.monoms) - 1
                    continue
            i -= 1
        return Semi(q), r

    def overlaps(self, other) -> list["Semi"]:
        # return all nontrivial overlaps of self and other
        # such that ov = q1 * self + r1 and ov = q2 * other + r2
        # ov is less that lm(self) * lm(other) ?
        res = []
        for (q, r), _ in self.overlaps_qr(other):
            ov = q * self + r
            if ov not in res:
                res.append(ov)
        return res

    def overlaps_qr(
        self, other
    ) -> list[tuple[tuple["Semi", "Semi"], tuple["Semi", "Semi"]]]:
        # Polynomial contexts split additively, so align one monomial occurrence.
        res = []
        for m1 in Counter(self.monoms):
            for m2 in Counter(other.monoms):
                cm = Counter(m1) | Counter(m2)
                qm1 = MS((cm - Counter(m1)).elements())
                qm2 = MS((cm - Counter(m2)).elements())
                q1, q2 = Semi([qm1]), Semi([qm2])
                t1, t2 = q1 * self, q2 * other
                ov = Semi((Counter(t1.monoms) | Counter(t2.monoms)).elements())
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


def huet_marked(eqs: list[Eq]) -> list[Rewrite]:
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
