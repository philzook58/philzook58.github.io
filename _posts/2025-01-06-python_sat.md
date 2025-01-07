---
title: SAT Solver Etudes I
date: 2025-01-06
---

The abilities of SAT solvers exploded in performance in the 1990s and have continued to make quite nice gains every year since.

Here is a chart comparing the performance of the SAT competition winners from the last 25 years. Quite an increase!

<blockquote class="twitter-tweet"><p lang="en" dir="ltr">Kissat dominated the main track of the SAT Competition 2024. It won 3 gold medals!<br><br>Core techniques: congruence closure (SAT&#39;24) clausal equivalence sweeping (FMCAD&#39;24), bounded variable addition (BVA) and vivification.<a href="https://t.co/kCa7LAbtgE">https://t.co/kCa7LAbtgE</a> <a href="https://t.co/keagEQW2OA">pic.twitter.com/keagEQW2OA</a></p>&mdash; Armin Biere (@ArminBiere) <a href="https://twitter.com/ArminBiere/status/1833515116186546472?ref_src=twsrc%5Etfw">September 10, 2024</a></blockquote> <script async src="https://platform.twitter.com/widgets.js" charset="utf-8"></script>

The [satisfiability problem](https://en.wikipedia.org/wiki/Boolean_satisfiability_problem) on it's face it an extremely simple one. At a rough level, it is asking it the is some input to a circuit that can drive the output to true, running the circuit backwards if you will. A more accurate description is that it finds a satisfying assignment (every variable is `true` or `false` to a giant "AND" of "OR"s, a logical normal form called Conjunctive Normal Form. This normal form is an analog in some respects to the normal FOILed out form of a polynomial. This also makes it a nice intermediate representation of sorts for other [combinatorial problems](https://en.wikipedia.org/wiki/NP-completeness).

Example SAT solvers come in kind of two flavors:

- Simple functional programming ones, maybe are recursive, etc
- The low level ones. You explicitly manage the trail and probably are in a low level language.

I'm not against the first approach. I write a lot of python. Something that is freeing about python is you know performance will suck no matter what. So just write things clearly or interestingly. On the other hand, python lacks a whole dimension of expressivity and fun that comes from performance considerations.

"A LISP programmer knows the value of everything, but the cost of nothing." - [Alan Perlis](https://www.cs.yale.edu/homes/perlis-alan/quotes.html)

Anyway, having said that, nothing that follows represents my recommendation on how to write a SAT solver. Look at MiniSAT, Cadical, Kissat, and the CrueSAT thesis for something closer to that. Maybe next post.

# Brute Solver

It is always an interesting exercise to write a brute force solver. Sometimes, it can even be useful. If your SAT problem very few variables, or you perhaps are in the "endgame", this might be the fastest SAT solver you can write.

One nice way of going about it is to just use an integer as a bitvector. You can then enumerate over the models by incrementing the integer.

One annoying design choice is how to represent your problem itself. A list of clauses is a reasonable choice.

```python
def nv(cnf):
    return max((max(map(abs,c),default=0) for c in cnf), default=0)

def bits(i,n):
    return [bool(i & (1 << j)) for j in range(n)]

def satisfies(model,cnf):
    return all(any(model[abs(l)] if l > 0 else not model[abs(l)] for l in c) for c in cnf)
    
def brute(cnf):
    n = nv(cnf) + 1
    for i in range(2**n):
        model = bits(i,n)
        if satisfies(model, cnf):
            yield model
    return "unsat"

list(brute([[0],[1,2],[-1,-2]]))

def brute_sat(cnf):
    return next(brute(cnf), None) is not None
```

Generating random SAT problems can help a bit. Random SAT may not explore all phenomena of interest though, as actual SAT problems have lots of structure.

```python
import random
def rand_cnf():
    lits = 9
    clauses = 7
    return [[random.randint(-lits, lits) for _ in range(random.randint(0,6))] for _ in range(random.randint(0,clauses))]
rand_cnf()

for i in range(10):
    print(brute_sat(rand_cnf()))

```

    True
    False
    False
    True
    True
    True
    True
    False
    True
    True

But there are a number of things unsatisfying (ha) about this. It does not lend itself well to eventually a more sophisticated SAT solver. In addition, using integers to identify variables means you will need to record what the integers correspond to elsewhere.

# Davis Putnam

A different approach is to use the [Davis Putnam](https://en.wikipedia.org/wiki/Davis%E2%80%93Putnam_algorithm) procedure. This is basically a resolution procedure, saturating the clause set.

The following is based on Harrison's code from
<https://www.cl.cam.ac.uk/~jrh13/atp/OCaml/dp.ml>

```python
def resolve_on(p : int, cnf):
    """
    Eliminate literal p via resolution.
    """
    assert isinstance(p, int)
    pos_p = [c - {p} for c in cnf if p in c]
    neg_p = [c - {-p} for c in cnf if -p in c]
    no_p = [c for c in cnf if p not in c and -p not in c]
    return set(no_p + [c1 | c2 for c1 in pos_p for c2 in neg_p])

def one_literal(cnf):
    """
    Find clause of one literal, delete clauses that contain it or remove it's negation
    """
    p = next((c for c in cnf if len(c) == 1), None)
    if p is None:
        return None
    p, = p
    return set([c - {-p} for c in cnf if p not in c])
    
def affirm_negative(cnf):
    lits = set(l for c in cnf for l in c)
    pure_lits = [l for l in lits if -l not in lits]
    if len(pure_lits) == 0:
        return None
    return set([c for c in cnf if all(l not in pure_lits for l in c)])

def remove_pos_neg(cnf):
    # delete all clasuses that contain both p and not p
    if any(any(-l in c for l in c) for c in cnf):
        return set([c for c in cnf if not any(-l in c for l in c)])
    else:
        return None


def dp(cnf):
    cnf = set([frozenset(c) for c in cnf])
    while cnf:
        if frozenset() in cnf:
            # unsatisfiable
            return False
        cnf1 = remove_pos_neg(cnf)
        if cnf1 is not None:
            cnf = cnf1
            continue
        cnf1 = one_literal(cnf)
        if cnf1 is not None:
            cnf = cnf1
            continue
        cnf2 = affirm_negative(cnf)
        if cnf2 is not None:
            cnf = cnf2
            continue
        print(cnf)
        p = next(iter(next(iter(cnf))))
        cnf = resolve_on(p,cnf)
    return True

dp([[0],[1,2],[-1,-2]])

```

    {frozenset({-1, -2}), frozenset({1, 2})}





    True

To show we're kind of making sense, compare the results to the brute force solver.

```python
for i in range(100):
    cnf = rand_cnf()
    assert brute_sat(cnf) == dp(cnf)
```

A different style of resolution solver uses a given clause loop. This is something like semi naive from datalog.

```python
def negate_clause(clause : frozenset[int]):
    return frozenset([-l for l in clause])

def saturate(cnf):
    processed = set()
    unprocessed = [frozenset(c) for c in cnf]
    while unprocessed:
        #print("unprocessed", unprocessed)
        given = unprocessed.pop()
        if given == frozenset():
            return False
        if any(-l in given for l in given):
            continue
        for c2 in processed:
            res_lits = given & negate_clause(c2)
            #print("given", given, "c2", c2, res_lits)
            if len(res_lits) != 0:
                res = (given | c2) - res_lits - negate_clause(res_lits)
                if res not in processed:
                    unprocessed.append(res)
        processed.add(given)
    #print(processed)
    return True #processed

#given([[0],[1,2,3],[-1,-2]])
#saturate([[1,2], [2,3], [3,-1], [1]])
#saturate([[6], [-3, 0, 4], [-6, 5, -8, 8, -5]])
#brute_sat([[6], [-3, 0, 4], [-6, 5, -8, 8, -5]])

for i in range(100):
    cnf = rand_cnf()
    if brute_sat(cnf) != saturate(cnf):
        print(cnf)
        assert False



```

```python

```

# Bits and Bobbles

A queue on length of clause will give you a kind of unit propagation.
A queue based on maximum literal maybe give you something like recursive elimination of variables.

You could reorganize (vectorize?) given clause algorithm to be more like a seminaive datalog.

Storing clauses in normal form  or Subsumption is kind of necessary for satruation to be achived

while len(new) > 0:
    d = resolve(new, old)
    old = new + old
    new = d - old

```python
from z3 import *
# using z3expr as my propositions
def negate(p : z3.BoolRef):
    if z3.is_not(p):
        return p.arg(0)
    return z3.Not(p)


#bool(BoolVal(True) == BoolVal(True))
x,y = Ints("x y")
x in [y]
x + y in {x, y}
```

    False

### Partial evaluation of sat solvers

Considering concrete problems before going into the generic solver can be informative. Also, building the generic system can be pointless and expensive if you really only have 1 or a couple problems to actually solve.
You can usually look back at these specialized solvers as instances of partial evaluation of a generic solver with respect to a particular problem data.
I am not aware of anyone really going for partial evaluation of SAT solvers. It must surely have been done.

```python
import itertools
#list(brute([[0],[1,2],[-1,-2]]))
# each of these is a partial evaluation of eval_clause(clause, m):
def clause1(m):
    return m[0]
def clause2(m):
    return m[1] or m[2]
def clause3(m):
    return not m[1] or not m[2]
for m in itertools.product([True,False], repeat=3):
    if clause1(m) and clause2(m) and clause3(m): # partial eval of satisfies(cnf, m)
        print(m)

```

    (True, True, False)
    (True, False, True)

# SAT

There is a dpll1 and dpll2 in sympy.logic.algorithms
Also lra. also interface to z3 (!)

cadical 2023 - SBVA strcutured blcoked clause addition
<https://cca.informatik.uni-freiburg.de/papers/BiereFallerFazekasFleuryFroleyksPollitt-SAT-Competition-2024-solvers.pdf> kissat

kissat 2024 - clausal congruence closure <https://github.com/arminbiere/kissat/blob/master/src/congruence.c> <https://cca.informatik.uni-freiburg.de/papers/BiereFazekasFleuryFroleyks-SAT24-preprint.pdf>

"SAT-sweeping technique using our embedded SAT solver Kitten" Kitten is a smaller sat solver inside kissat?

<https://m-fleury.github.io/>

<https://github.com/IsaFoL/IsaFoL/>

sat competition benchmarks descriptions

- replacing riscv
- circuit equiv checking

avatar

rapid restart might make for a simple implementation.
Restart fully after each conflict.
Don't have to clean trail or model.

With my egraph, if i wrote a sat solver, I'd have a mini
Put in SAT comp?

[The silent revolution of sat](https://news.ycombinator.com/item?id=36079115#36081904)

[creusat](https://sarsko.github.io/_pages/SarekSkot%C3%A5m_thesis.pdf) <https://github.com/sarsko/CreuSAT>

<https://fmv.jku.at/fleury/papers/Fleury-thesis.pdf>

<https://github.com/marijnheule/microsat>

<https://github.com/msoos/minisat-v1.14>

<https://x.com/SoosMate/status/1760817528236818456?s=20> phind know sat solvers
"Yes (about the role of Kitten in Kissat) but the explanation is still bogus. It sounds like a weak student who does not understand anything but tries to pass the exam by randomly arguing about concepts discussed in this context. I probably would let it pass (but just)."

<https://sahandsaba.com/understanding-sat-by-implementing-a-simple-sat-solver-in-python.html>
wait this blog is sweet

<https://easychair.org/publications/open/b7Cr> CDCL as rewrite syste,

<https://x.com/krismicinski/status/1856341897331003842>  "Trying to turn in my class material into a few recorded lectures on CDCL. I have seen some good talks on CDCL history by experts (e.g., Armin Biere's Simmons institute talk), but think there is still room for more discussion that starts from a as-functional-as-possible style."

2 watched literal is related to simplex tableau method?
<https://types.pl/@krismicinski/113470474347084554>

Jules Jacobs - Retconning out DPLL and treat it as iterative clause learning from the start?

We could enumerate all models.
Upon each model failure, perhaps we can determinate a backjump skip instead of just go to next one.
Or we could clause learn.
This might be especially useful if we're trying to get minimal model according to variable ordering.

Ordered resolution and CDCL
Given a resolution state, we can start to build a partial model.
The literal ordering means that the "datalog" rules are unit propagations, we've already assigned all the other bits by the time we consider each rule.
The trail is the current partial model.

Decision vs propapgation clauses...

The conflict clause should be resolved with a previous one.

CDCL is kind of pivoting on useful literal orderings. The current ordering _is_ the trail.
But even if we had the best ordering a priori, it wouldn't be as good because it is

avatar. Maybe an avatar loop would be smart

<https://github.com/NikolajBjorner/ShonanArtOfSAT>
satsifiability modulo rewriting

<https://www-cs-faculty.stanford.edu/~knuth/programs.html> knuth sat solvers and others

<https://www.labri.fr/perso/lsimon/research/glucose/> glucose <https://github.com/audemard/glucose> huh glucose is a minisat fork. i didn't know that

lingeling <https://github.com/arminbiere/lingeling>

trail is current literal ordering.
pivoting between orderings. Hmm.

## DPLL
<https://en.wikipedia.org/wiki/DPLL_algorithm>
DP

pure literal elim

<https://github.com/safwankdb/SAT-Solver-using-DPLL/blob/master/SATSolver.py>
<https://github.com/charliermarsh/OCaml-SAT-Solvers/blob/master/dpll.ml>
<https://github.com/baptiste-fourmont/dpll/blob/main/dpll.ml>
<https://simon.cedeela.fr/sat.html>  
<https://github.com/Gbury/mSAT>
<https://github.com/qnighy/ratsat> rust reimplemnt of minisat
<https://github.com/imandra-ai/minisat-ml> <https://github.com/imandra-ai/minisat-ml/blob/master/docs/tech_report.md> tehch report. cost of using ocaml vs C++ for exact minisat copy

Harrison treatment
<https://matryoshka-project.github.io/pubs/splitting_paper.pdf> Unifying Splitting Framework

splitting rules. Another approach is to split some clause. Hmm.
convert the disj in the clause to meta disjunction.

Dumbest possible things. Use integer as model. iterate through them.
We still need the ability to represent the clauses.
We need the ability to revaluate the clauses

Use vector as model.

Separating the trail from the model. It is serving both repsonsilbities.

unit propagation

3 valued logic of true false ?. True False None. Or refactor into true false, false true, false false. true true is contradiction.

```
trues = [] # 
falses = []

trues = set()
falses = set()

```

Design choices
recursion, loop
mutate, pure
Trail, model, clauses.

simplify clauses vs not
clause rep: vecvec,
model rep: vec, implicit in trail, sets, others?
literal rep: +- literal vs struct bool literals
ints as atoms.
objects as atoms.

learned claues ve initial clauses.

Looking at these low level fastest versions may not be the most mind opening

```python
def simplify(cs):
    # units is assignment
    units = []
    for i in range(4):
        units.extend([c[0] for c in cs if len(c) == 1])
        cs = [[l for l in c if l not in units] for c in cs if len(c) != 1]


# where does split even go. Like into a universe branching?
def split(c):
    return c[0], c[1:]

```

3sat or nsat
Maybe there is simplifcation or even perf gains from restruicting to 3sat.
1sat   # model
2sat   # watchlist
3sat   # clauses

```python
# 3sat or Nsat

```

```python
# a style of simplify the clause and recursing instead of maintaining model
def replace(c, n):
    if n in c:
        return True
    else:
        return c.remove(-n)
def units(cs):
    return {c[0] for c in cs if len(c) == 1}
def search(cs, vs):
    # pick lit. nvar
    if any(len(c) == 0 for c in cs): # empty clause is can't be satisfied
        return False
    v = vs.pop()
    for decide in [v, -v]:
        todo = {decide}
        vs1 = vs.copy()
        cs1 = cs.copy()
        while todo:
            lit = todo.pop()
            vs1.remove(abs(lit))
            cs1 = [replace(c,lit) for c in cs1] # simplify clauses
            todo |= units(cs1) # unit propagate
        if search(cs1, vs1):
            return True
    return False
    
    # replace and simplify
    # propagate units
    # recursively call self on nvar-1
```

```python
def search_rec(cs):
    model = []
    def lit_sat(l):
        neg = l < 0
        v = model.get(abs(l))
        if v is None:
            return None
        return v if not neg else not v
    def is_sat(): 
        return all(any(lit_sat(l) for l in c) for c in cs) 
    def decide():
        model.append(True)
        """for l in cs[0]:
            if model.get(abs(l)) is None:
                model[abs(l)] = l > 0
                return True
        return False"""

    def backtrack():
        while model[-1]:
            model.pop()
        model.append(False)
        """
        if model[-1]:
            model[-1] = False
        else:
            model.pop()
            backtrack()
        """
    def propagate():
        pass
    model.append(True)
    while model:
        status = is_sat()
        if status is None:
            decide()
        elif status is False:
            backtrack()
        elif status is True:
            return model
    return "unsat"




```

## Brute

What form should cnf take

```python

```

    ---------------------------------------------------------------------------

    ModuleNotFoundError                       Traceback (most recent call last)

    Cell In[6], line 2
          1 import pysat
    ----> 2 import pysat.formula


    ModuleNotFoundError: No module named 'pysat.formula'

```python

from pysat.formula import CNF
from pysat.solvers import Solver

# create a satisfiable CNF formula "(-x1 ∨ x2) ∧ (-x1 ∨ -x2)":
cnf = CNF(from_clauses=[[-1, 2], [-1, -2]])

# create a SAT solver for this formula:
with Solver(bootstrap_with=cnf) as solver:
    # 1.1 call the solver for this formula:
    print('formula is', f'{"s" if solver.solve() else "uns"}atisfiable')

    # 1.2 the formula is satisfiable and so has a model:
    print('and the model is:', solver.get_model())

    # 2.1 apply the MiniSat-like assumption interface:
    print('formula is',
        f'{"s" if solver.solve(assumptions=[1, 2]) else "uns"}atisfiable',
        'assuming x1 and x2')

    # 2.2 the formula is unsatisfiable,
    # i.e. an unsatisfiable core can be extracted:
    print('and the unsatisfiable core is:', solver.get_core())
```

    formula is satisfiable
    and the model is: [-1, -2]
    formula is unsatisfiable assuming x1 and x2
    and the unsatisfiable core is: [1]

```python
cnf = CNF(from_clauses=[[-1, 2], [-1, -2], [14]])
cnf.clauses
cnf.nv
dir(cnf)
```

    ['__and__',
     '__class__',
     '__deepcopy__',
     '__delattr__',
     '__dict__',
     '__dir__',
     '__doc__',
     '__eq__',
     '__format__',
     '__ge__',
     '__getattribute__',
     '__gt__',
     '__hash__',
     '__iand__',
     '__ilshift__',
     '__imatmul__',
     '__init__',
     '__init_subclass__',
     '__invert__',
     '__ior__',
     '__irshift__',
     '__iter__',
     '__ixor__',
     '__le__',
     '__lshift__',
     '__lt__',
     '__matmul__',
     '__module__',
     '__ne__',
     '__new__',
     '__or__',
     '__reduce__',
     '__reduce_ex__',
     '__repr__',
     '__rshift__',
     '__setattr__',
     '__sizeof__',
     '__str__',
     '__subclasshook__',
     '__weakref__',
     '__xor__',
     '_clausify',
     '_compute_nv',
     '_context',
     '_get_key',
     '_instances',
     '_iter',
     '_merge_suboperands',
     '_vpool',
     'append',
     'attach_vpool',
     'clauses',
     'clausify',
     'cleanup',
     'comments',
     'copy',
     'export_vpool',
     'extend',
     'formulas',
     'from_aiger',
     'from_clauses',
     'from_file',
     'from_fp',
     'from_string',
     'literals',
     'name',
     'negate',
     'nv',
     'satisfied',
     'set_context',
     'simplified',
     'to_alien',
     'to_dimacs',
     'to_file',
     'to_fp',
     'type',
     'weighted']

```python
def nv(cnf):
    return max(max(map(abs,c)) for c in cnf)

def bits(i,n):
    return [bool(i & (1 << j)) for j in range(n)]

def satisfies(model,cnf):
    return all(any(model[abs(l)] if l > 0 else not model[abs(l)] for l in c) for c in cnf)
    
def brute(cnf):
    n = nv(cnf) + 1
    for i in range(2**n):
        model = bits(i,n)
        if satisfies(model, cnf):
            yield model
    return "unsat"

list(brute([[0],[1,2],[-1,-2]]))


```

    [[False, True, False], [False, False, True]]

```python
def brute_rec(pmodel, cnf):
    n = nv(cnf)
    if len(pmodel) == n+1:
        if satisfies(pmodel, cnf):
            yield pmodel
    else:
        yield from brute_rec(pmodel + [False], cnf)
        yield from brute_rec(pmodel + [True], cnf)

list(brute_rec([], [[0],[1,2],[-1,-2]]))
```

    [[False, False, True], [False, True, False]]

```python
def psatisfies(model,cnf):
    return all(any(False if len(model) < abs(l) else model[abs(l)] if l > 0 else not model[abs(l)] for l in c) for c in cnf)

```

```python
def brute_cps(cnf, fail, succ):
    pass
def brute_cps(succ, backtracklist):
    pass
```

```python
def decide(model):
    model.append(False)
def backtrack(model):
    while model[-1]:
        model.pop()
    model[-1] = True

def brute_loop(cnf): # bruit loop?
    n = nv(cnf) + 1
    model = []
    while model != [True] * n:
        print(model)
        if len(model) != n:
            decide(model)
        else:
            if satisfies(model,cnf):
                yield model.copy()
            backtrack(model)
    return "unsat"

list(brute_loop([[0],[1,2],[-1,-2]]))
```

    []
    [False]
    [False, False]
    [False, False, False]
    [False, False, True]
    [False, True]
    [False, True, False]
    [False, True, True]
    [True]
    [True, False]
    [True, False, False]
    [True, False, True]
    [True, True]
    [True, True, False]





    [[False, False, True], [False, True, False]]

## Techniques

bounded varaible elimination - important preprocessing. Most important maybe? <https://fmv.jku.at/papers/EenBiere-SAT05.pdf>

phase saving - easy to implement, nice jump in perf. record old values of variables and prefer that?

average glue LBD. glucose

'vivification"
instantiation

binary reason jumping
lucky phase detection
SLUR lookahead

Blocked clauses
<https://fmv.jku.at/papers/JarvisaloBiereHeule-TACAS10.pdf>

VMTF variable move to front - verified sat solvers seem to use because doesn't need floats like vsids
VSIDS . evsids?

luby
restarts

<https://www.msoos.org/2023/10/the-inprocessing-api-of-cryptominisat/>
<https://fmv.jku.at/biere/talks/Biere-POS14-talk.pdf>  Ternary resolution
Backbone simplification  <https://wenxiwang.github.io/papers/cadiback.pdf>
distillation <https://dl.acm.org/doi/10.1145/1278480.1278628>
 Vivify clauses using the Oracle tool by Korhonen and Jarvisalo <https://arxiv.org/pdf/2308.15819.pdf>

```python
%%file /tmp/sat.c

#define VAR(n) ((1 << n) & model)
//bool var(int model, int i){
//
//}

bool clause1(int model){
    return VAR(3) | VAR(4) | VAR(5);
}

#define VNUM 4
int main(){
    for(int model = 0; model < 2**VNUM; model++){
        if(clause1(model) && clause2(model) && clause3(model)){
            printf("%d\n", model);
            return 0;
        }
    }
    printf("unsat");
    return 1;
}
```

## Clause Learning
<https://en.wikipedia.org/wiki/Conflict-driven_clause_learning>

How do you actually do it
implication graph (bad perspective?)

Traverse the trail.

single conflict clause or multiple? We unit prop somethining then in our unit prop queue we may have multiples
The "reason". Like proof producing congruence clousre?
Each unit prop could be marked with reason clause or decide.

<https://sarsko.github.io/_pages/SarekSkot%C3%A5m_thesis.pdf> section 5

clause learning and resolution.

## Two Watched Literal

Compare with 2-SAT
2-sat ~ congruence closure.

tw watched literal freedom ~ union find freedom

b | a
b = ite(a, b, true)
a = ite(b, a, true)
ite(false,b,true) = true
iter(false,b,true) = true

really don't need ite... uh but what if two things are fozxren on a.
Ok maybe we do need it

b = freeze(clause7, a, true)
freeze(clause7,false)

```python
# two watched literal
Lit = int
clauses = []
from collections import defaultdict
vmap = defaultdict(list)

def unit(cnum):
    for lit in clauses[cnum]:
        v = model[lit]
        if v is None:
            
        


def propagate(lit):
    queue = [lit]
    while queue:
        lit = queue.pop()
        for cid in vmap[lit]:
            #cls = clauses[cid]

            for l2 in cid:
                v2 = model[l2]
                if v2 is True:
                    break # clause true
                elif v2 is None:
                    if cid in vmap[l2]: # other watched literal
                        continue
                    else:
                        vmap[l2].append(cid)
                        break
            



            l2 = unit(cid)
            if l2 is not None:
                queue.append(l2)
            










```

```python
def solve():
    trail = []
    clauses = []
    def clause(n):
        c = clauses[n]
        for lit in c:

    while True:
        # propagate
        # decided
        # backjump
        # learn
        # forget
class Solver():
    model : dict[int, bool]
    trail : list[tuple[bool, int, int]]
    twl : dict[int, list[int]]

    def eval_clause(self, nc):
        c = self.clauses[c]
        done = True
        for l in c:

            v = self.model.get(l)
            if v is True:
                return True
            if v is None:
                done = False
                continue
        if done:
            return False # conflict
        else:
            return None # undecided
    def decide(self, l):
        self.trail.append((True, l))
        self.model[l] = True
        
    def backjump(self, n):
        for i in range(n):
            l = self.trail.pop()
            del self.model[l]

```

# Solvers

## Cadical

- blocking literals 2008 JSAT paper by Chu, Harwood and Stuckey
- Finally, for long clauses we save the position of the last watch replacement in 'pos', which in turn reduces certain quadratic accumulated propagation costs (2013 JAIR article by Ian Gent

<https://cca.informatik.uni-freiburg.de/papers/BiereFallerFazekasFleuryFroleyksPollitt-CAV24.pdf> cadical 2

- `cdcl_loop_with_inrpcoessing` is core in Internal <https://github.com/arminbiere/cadical/blob/31f9aae44947c673dc6190c9beb399acb9ffec6a/src/internal.cpp#L246>

```
mode = PROPAGATE
def analyze():
def propagate():
def decide():

while True:
    match mode:
        case PROPAGATE:
        case DECIDE:

```

- propagate <https://github.com/arminbiere/cadical/blob/master/src/propagate.cpp#L227>
- watch <https://github.com/arminbiere/cadical/blob/master/src/watch.hpp>
- analyze conflict <https://github.com/arminbiere/cadical/blob/31f9aae44947c673dc6190c9beb399acb9ffec6a/src/analyze.cpp#L860>
- decide <https://github.com/arminbiere/cadical/blob/31f9aae44947c673dc6190c9beb399acb9ffec6a/src/decide.cpp#L122>
- trail is vector of in <https://github.com/arminbiere/cadical/blob/31f9aae44947c673dc6190c9beb399acb9ffec6a/src/internal.hpp#L236> . control is also kind of part of trail <https://github.com/arminbiere/cadical/blob/31f9aae44947c673dc6190c9beb399acb9ffec6a/src/internal.hpp#L254> . backtracking the trail <https://github.com/arminbiere/cadical/blob/master/src/backtrack.cpp>

```
control : list[tupel[level, unitlitnum]] # control only push on decisions
trail : # every literal assigned is on trail 
```

- clause <https://github.com/arminbiere/cadical/blob/master/src/clause.hpp> glucose L53  See the IJCAI'09 paper by Audemard & Simon for more details

```
Clause:
    #id : maybe
    lits : list[int]
    glue: int

```

satsifiability modulo symmettries <https://sat-modulo-symmetries.readthedocs.io/en/latest/>

Partik Simons et al Alg. 4 in his JAIR article from 2002. smodels. lookeahead. probing

Idea. what if we incrementally put cadical back together

<https://www.youtube.com/watch?v=II2RhzwYszQ&t=14916s&ab_channel=SimonsInstitute>

## Satch
<https://www.youtube.com/watch?v=II2RhzwYszQ&t=14916s&ab_channel=SimonsInstitute>
<https://github.com/arminbiere/satch>

## MicroSAT
<https://github.com/marijnheule/microsat>

## MiniSAT

## PicoSAT

## KISSAT

## CreuSAT

## IsaSAT

# Encodings

pysat
pseudo boolean

# SAT

<https://en.wikipedia.org/wiki/DPLL_algorithm>
<https://chatgpt.com/c/66e9eb94-8984-8008-9db9-c0190f98e25c>

```python
from typing import NamedTuple

Literal = NamedTuple('Literal', [('idx', int), ('polarity', bool)])
Clause = NamedTuple('Clause', [('literals', list)])
Formula = NamedTuple('Formula', [('clauses', list[Clause]), ('num_vars', int)])

Assignment = NamedTuple('Assignment', [('values', list[bool])])
Pasn = NamedTuple('Pasn', [('assignment', Assignment), ('satisfiable', bool)])

```

## Z3 dimacs

Can we use z3 to do cnf transformation?
<https://microsoft.github.io/z3guide/docs/strategies/summary#tactic-tseitin-cnf>

def dimacs(self, include_names=True): also apparently solver has a dimacs printer...

<https://stackoverflow.com/questions/13059096/z3-and-dimacs-output>
<https://github.com/RobinDavid/pydimacs>

I put it into knuckeldragger

```python
from z3 import *

x,y,z,w = Bools("x y z w")
G = Goal()
G.add(Implies(x, And(z,w)))
G.add(Implies(y, Or(x,z)))
t1 = Tactic('tseitin-cnf')
tactic = z3.Then('simplify', 'bit-blast', 'tseitin-cnf')
for c in tactic(G):
    print(c)
    print(c.dimacs())

import subprocess
class SATSolver():
    def __init__(self):
        self.G = z3.Goal()
    def add(self, clause):
        self.G.add(clause)
    def check(self, debug=False):
        t = z3.Then('simplify', 'bit-blast', 'tseitin-cnf')
        c = t(self.G)
        assert(len(c) == 1)
        with open("/tmp/sat.cnf", "w") as f:
            f.write(c[0].dimacs())
            f.flush()
        self.res = subprocess.run(["kissat", "--relaxed", "/tmp/sat.cnf"], capture_output=True)
        res = self.res.stdout.decode()
        if "s SATISFIABLE" in res:
            return z3.sat
        elif "s UNSATISFIABLE" in res:
            return z3.unsat
        else:
            return z3.unknown

s = SATSolver()
s.add(Implies(x, And(z,w)))
s.add(Implies(y, Or(x,z)))
assert s.check() == z3.sat
#print(s.res.stdout.decode())


```

    [Or(z, Not(x)), Or(w, Not(x)), Or(x, z, Not(y))]
    p cnf 4 3
    1 -2 0
    3 -2 0
    2 1 -4 0
    c 2 x
    c 4 y
    c 1 z
    c 3 w

```python
! cat /tmp/sat.cnf
```

    p cnf 12 29
    52 -48 -49 0
    52 -48 0
    52 -49 0
    48 49 -52 0
    52 50 46 -53 0
    50 -53 -52 -46 0
    52 -50 -53 -46 0
    46 -50 -53 -52 0
    -50 -52 53 -46 0
    52 46 -50 53 0
    50 46 -52 53 0
    52 50 53 -46 0
    -53 0
    48 -54 -44 0
    44 -48 -54 0
    -48 54 -44 0
    44 48 54 0
    -54 0
    50 55 0
    52 55 0
    -50 -52 -55 0
    47 51 55 0
    47 -51 -55 0
    51 -47 -55 0
    -51 -47 55 0
    45 48 49 0
    45 -48 -49 0
    -48 49 -45 0
    48 -49 -45 0

```python
x = BitVec('x', 4)
y = BitVec('y', 4)
s = SATSolver()
s.add(x == y + 3)
assert s.check() == z3.sat
#print(s.res.stdout.decode())

s = SATSolver()
s.add(x == x + y)
s.add(y != z3.BitVecVal(0, 4))
assert s.check() == z3.unsat

```

```python
from z3 import *
a,b,c = Ints("a b c")
s = SimpleSolver()
s.add(a == b)
s.add(b == c)
s.check()
print([s.root(x) for x in [a,b,c]])
[s.next(x) for x in [a,b,c]]    
#s.next(b)
```

    [b, b, b]





    [b, c, a]

```python
from z3 import *
s = SimpleSolver()
x, y, z = Ints('x y z')
s.add(x == y)
s.add(y == z)
s.check()
print(s.root(x), s.root(y), s.root(z))
print(s.next(x), s.next(y), s.next(z))
```

```python
from z3 import *

x,y,z,w = Bools("x y z w")
G = Goal()
G.add(Implies(x, And(z,w)))
t1 = Tactic('tseitin-cnf')
t1(G)

```

[[z &or; &not;x, w &or; &not;x]]

Match the z3 api

```python
from dataclass import dataclass

Id = int

@dataclass
class Context():
    hashcons : dict[tuple[Id] | str | int, Id]
    def intern(self, x : tuple[Id] | str | int) -> Id:
        if x in self.hashcons:
            return self.hashcons[x]
        else:
            id = len(self.hashcons)
            self.hashcons[x] = id
            return id

  


@dataclass(frozen=True)
class AstRef():
    ctx : Context
    ast : Id
    def __eq__(self, other : AstRef) -> bool:
        assert self.cxt == other.ctx
        return self.ast == other.ast
    def __hash__(self) -> int:
        return hash(self.ast)
    
    # fill in
_main_ctx : Context = Context({})
def get_ctx(ctx):
    if ctx is None:
        return _main_ctx
    return ctx

def to_symbol(x : int | str, ctx=None) -> int:
    ctx = get_ctx(ctx)
    return ctx.intern(x)
    
def is_ast(x):
    return isinstance(x, AstRef)

@dataclass(frozen=True)
class SortRef(AstRef):

@dataclass(frozen=True)
class ExprRef(AstRef):
    # fill in
    ast : AstRef
```

```python

```

```python
# parsing DIMACS
def parse_dimacs(filename):
    with open(filename, 'r') as f:
        lines = f.readlines()
    clauses = []
    for line in lines:
        if line[0] == 'c':
            continue
        if line[0] == 'p':
            n_vars = int(line.split()[2])
            continue
        clause = [int(x) for x in line.split()[:-1]]
        clauses.append(clause)
    return n_vars, clauses
```

```python
import numpy
nclauses = 10
clause_size = 
np.zeros((len(clauses), ) , dtype=np.uint8)


```

```python
def unit_prop(solution, clauses):
    while True:
        unit_clauses = [c for c in clauses if len(c) == 1]
        if len(unit_clauses) == 0:
            break
        unit_clause = unit_clauses[0]
        unit_literal = unit_clause[0]
        solution[abs(unit_literal)] = 1 if unit_literal > 0 else 0
        clauses = [c for c in clauses if unit_literal not in c]
    return solution, clauses




```

```python
def CDCL():
    while True:
        if [] in clauses: return UNSAT
        elif in_conflict(): learn(); backtrack()
        elif not free_vars: return SAT
        elif should_propagate(): propagate()
        elif should_simplify(): simplify()
        elif should_restarty(): restart()
        elif: should_prune(): prune*()
        else:
            var= chooce_var()
            sign = choose_sign()
            assign(var,sign)

```

Metatarki
<https://z3prover.github.io/papers/z3internals.html>

<https://github.com/sarsko/CreuSAT/blob/master/Friday/src/lib.rs> Friday

```python
assignment= list[bool]
lit = tuple[int, bool]
clause = list[lit]


def eval(formula, assignment):
    pass

def solve(formula):
    assignment = [[None] * f.num_vars]
    ix = 0
    while True:
        if ix == f.num_vars:


# 
assignment = 0

while True:
    assignment += 1
    eval(formula, assignment)


```

# SMT

difference logic
<https://docs.scipy.org/doc/scipy/reference/generated/scipy.sparse.csgraph.shortest_path.html>

<https://users.aalto.fi/~tjunttil/2020-DP-AUT/notes-smt/diff_solver.html>

<https://leodemoura.github.io/files/oregon08.pdf>

Engineering DPLL(T) + sautriation
<https://leodemoura.github.io/files/z3spc.pdf>

<https://leodemoura.github.io/files/sbmf09.pdf>

<https://dl.acm.org/doi/10.1145/1459010.1459014> New results on rewrite-based satisfiability procedures

Gallier, J., Narendran, P., Plaisted, D., Raatz, S., Snyder, W.: An algorithm for
finding canonical sets of ground rewrite rules in polynomial time. J. ACM 40
(1993) - convert egraph into rules?

<https://ocamlpro.github.io/alt-ergo/latest/index.html>

<https://homepage.cs.uiowa.edu/~tinelli/papers/NieOT-JACM-06.pdf> Solving SAT and SAT Modulo Theories: from an
Abstract Davis-Putnam-Logemann-Loveland
Procedure to DPLL(T)

<https://alt-ergo.ocamlpro.com/#publications>
<https://inria.hal.science/hal-01522770> three tier strategy for floating point

<https://citeseerx.ist.psu.edu/document?repid=rep1&type=pdf&doi=45036ae8e05d71ea39253f863cfa270b6cdd9aa2> simplify paper

User theories. <https://microsoft.github.io/z3guide/programming/Example%20Programs/User%20Propagator/>

<https://cs.stanford.edu/~preiner/talks/Preiner-Shonan23.pdf> ipasir-up

```
notifications (for Inspecting CDCL Search)
∠ notify assignment
∠ notify new decision level
∠ notify backtrack
Callbacks (for Influencing CDCL Search)
∠ cb propagate
∠ cb add reason clause lit
∠ cb decide
∠ cb add external clause lit
∠ cb check found model
```

<https://resources.mpi-inf.mpg.de/departments/rg1/conferences/vtsa08/slides/barret2_smt.pdf>
shostak. solver solve, and canonizier canon. Hmm. so that is both e-unification and completion.

<https://github.com/usi-verification-and-security/opensmt>

<https://github.com/Z3Prover/z3/blob/master/src/smt/smt_theory.h>

```python
class Theory():
    def mk_var(self, enode):
        pass
    def getvar(self, enode):
        pass
    def propagate(self):
        pass
    def push(self):
        pass
    def pop(self, n):
        pass
    def assign(self, bvar, sign):
        pass
    def new_eq(self, v1, v2):
        pass
    def new_diseq(self, v1,v2):
        pass
    def validate_model(self, mode):
        pass
    # model generate
    def 
    # model check
    def m

```

<https://github.com/cvc5/cvc5/blob/main/src/theory/theory.h>
<https://github.com/cvc5/cvc5/blob/main/src/theory/output_channel.h>

<https://ocamlpro.github.io/alt-ergo/latest/API/alt-ergo-lib/AltErgoLib/Theory/module-type-S/index.html>

```python
from typing import NamedTuple


ctx = {}

#@dataclass
class AstRef(NamedTuple):
    #head : str
    #sort : AstRef
    #children : tuple[AstRef, ...]
    def eq(self, other):
        return self == other
    def sexpr(self):
        return 



class SortRef(AstRef):
    name : str

# smtlib3
class TVarRef(SortRef):
    pass

class TForAll(SortRef):
    pass

    
class FuncDeclRef(AstRef):
    name : str
    dom : tuple[SortRef, ...]
    cod : SortRef
    def range(self):
        return self.cod
    def arity(self):
        return len(self.dom)
    def __call__(self, *args):
        return ExprRef(self, args)   

class ExprRef(AstRef):
    _decl : FuncDeclRef
    _args : tuple[ExprRef, ...]
    def decl(self):
        return self._decl
    def arg(self, i):
        return self._args[i]
    def children(self):
        return self._args
    def sort(self):
        return self._decl.cod


class BoolSortRef(SortRef):
    name = "Bool"

def BoolSort():
    return BoolSortRef()

class VarRef(AstRef):
    ind : int
#def QuantifierRef(ExprRef):


#isinstance(BoolSort(),NamedTuple)

def is_app(x):
    return isinstance(x, ExprRef)
def is_var(x): return isinstance(x, VarRef)
def Function(name, *args):
    return FuncDeclRef(name, args[:-1], args[-1])

def And(*args):
    AndDecl = Function("And", *args)
    #return AndDecl(*args)

```

    ---------------------------------------------------------------------------

    TypeError                                 Traceback (most recent call last)

    Cell In[6], line 34
         31 def BoolSort():
         32     return BoolSortRef()
    ---> 34 isinstance(BoolSort(),NamedTuple)


    TypeError: isinstance() arg 2 must be a type, a tuple of types, or a union

```python
import z3
x,y = z3.Bools("x y")
z3.ForAll([x,y], z3.And(x,y)).decl()
```

    ---------------------------------------------------------------------------

    Z3Exception                               Traceback (most recent call last)

    /tmp/ipykernel_81342/923796132.py in ?()
          1 import z3
          2 x,y = z3.Bools("x y")
    ----> 3 z3.ForAll([x,y], z3.And(x,y)).decl()
    

    ~/.local/lib/python3.10/site-packages/z3/z3.py in ?(self)
       1069         >>> (a + 1).decl()
       1070         +
       1071         """
       1072         if z3_debug():
    -> 1073             _z3_assert(is_app(self), "Z3 application expected")
       1074         return FuncDeclRef(Z3_get_app_decl(self.ctx_ref(), self.as_ast()), self.ctx)


    ~/.local/lib/python3.10/site-packages/z3/z3.py in ?(cond, msg)
        105 def _z3_assert(cond, msg):
        106     if not cond:
    --> 107         raise Z3Exception(msg)
    

    Z3Exception: Z3 application expected

```python
%%file /tmp/test.lean

inductive Expr : Type
| UVar : String -> Expr
| App : String -> List Expr -> Expr

deriving instance BEq, Hashable, Inhabited, Repr for Expr

def main : IO Unit :=
    do
        IO.println "Hello, world!"
        IO.println "hi"
        IO.println (repr (Expr.App "c" []))
```

    Overwriting /tmp/test.lean

```python
!lean --run /tmp/test.lean
```

    Hello, world!
    hi
    Expr.App "c" []

### z3 as a theory

One of the easiest ways of getting a theory solve is to just use z3 as one.
If you assert only theory atoms, basically it's a theory.
You can propagate via many queries.

We could also bolt z3 to cvc5 as an abomination.
Or bolt kissat to z3.
Or z3 that doesn't know what the other hand do-eth

```python
from z3 import *

boolmap = {}





```

### Intercommunicating cvc5 and z3

### dreal = z3 + flint (?)

SMT modulo convex

Could I find piles of interesting little SMT theories to prototype up?
