import sys
import time

from semi import Eq, Semi, congruence_path, rewrite_once

x = Semi.lit("x")


def prove(name, seed, lhs, rhs, *, seed_rhs=x, degree=20, terms=300):
    eq = Eq(seed, seed_rhs)
    start = time.perf_counter()
    path = congruence_path(
        lhs, rhs, [eq], max_degree=degree, max_terms=terms
    )
    elapsed = time.perf_counter() - start
    if path is None:
        print(f"{name}: no path within bounds, {elapsed:.3f}s")
        return False
    for before, after in zip(path, path[1:]):
        assert after in {result for result, _ in rewrite_once(before, [eq])}
    print(f"{name}: {len(path) - 1} steps, {elapsed:.3f}s")
    return True


family = sys.argv[1] if len(sys.argv) > 1 else "quick"
limit = int(sys.argv[2]) if len(sys.argv) > 2 else 5

if family in ("quad", "quick"):
    for n in range(1, limit + 1):
        prove(f"quad n={n}", n + x + x**2, x**5, n * n * x)

if family in ("cyclo3", "quick"):
    for c in range(1, limit + 1):
        prove(
            f"cyclo3 c={c}",
            c * c + (c + 1) * x + x**2,
            x**4,
            c**3 * x,
        )

if family in ("cubic", "quick"):
    for n in range(1, limit + 1):
        prove(f"cubic n={n}", n + x + x**3, x**7, n * n * x)

if family in ("candidates", "quick"):
    prove("cubic candidate 1", 8 + 5 * x + 2 * x**2 + x**3, x**5, 16 * x)

if family in ("phi6", "quick"):
    c = Semi.lit("c")
    prove(
        "symbolic phi6",
        c * x,
        c * x**7,
        c**7 * x,
        seed_rhs=c**2 + x**2,
    )

if family == "hard":
    prove(
        "cubic candidate 2",
        8 + 9 * x + 4 * x**2 + x**3,
        x**7,
        64 * x,
        degree=24,
        terms=500,
    )
