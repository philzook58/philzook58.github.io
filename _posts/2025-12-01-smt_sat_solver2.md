---
title: "SAT Etudes 2: Toy DPLL"
date: 2025-12-01
---

Another post about SAT solvers, probably heading towards SMT solvers.

A previous post <https://www.philipzucker.com/python_sat/>

I may be on the hook for an SMT tutorial, and also it's interesting to think about so I wrote up a toy DPLL solver.

It is somewhat modelled after the Z3py api.

A SAT problem is given as a giant `and` of `or` of possibly negated boolean variables (Conjunctive normal form). You are trying to find an assignment to the variables such that all the clauses evaluate to true. This is a big search problem and it's obviously solvable by just big honking loops trying every assignment. For some small number of variables that is probably a good method also.

DPLL <https://en.wikipedia.org/wiki/DPLL_algorithm> combines backtracking search with unit propagation. I guess I didn't implement pure literal elimination. Eh, whatever.

The combination of the propagation and the search make the structures a bit more complex to build.

A big idea is the notion of a Trail. This is very similar to your host language stack. The trail needs to record both propagation and branching, but should note which is which, because the number of variables that propagate is discovered dynamically. Here I use a list of decision level lists. One could also just have a big list and a separate list to point out which ones are the decision points.

Propagation iteratively searches through the clauses for ones with a single unassigned literal and all assigned literals are false in the current model. We are forced to assign the variable. This is like having a single empty box in a Sudoku row.

```python
from dataclasses import dataclass
from typing import Optional
type Var = int # Var should always be positive
type Lit = int # Lits can be negative to indicate logical negation
type Clause = list[Lit]

@dataclass
class Solver():
    trail : list[list[Var]] = field(default_factory=list)
    model : list[Optional[bool]] = field(default_factory=lambda: [None]) # Mapping from Var to value in current partial model. var0 unused because -0 = 0
    clauses : list[Clause] = field(default_factory=list)
    def makevar(self):
        vid = len(self.model)
        self.model.append(None)
        return vid
    def eval_lit(self, lit:Lit) -> Optional[bool]:
        "Find value of lit in current model"
        val = self.model[abs(lit)]
        if val is None:
            return None
        return val if lit > 0 else not val
    def propagate(self) -> bool:
        "Find clauses with a single unassigned lit and make it true in the model"
        changed = False
        while changed:
            changed = False
            for clause in self.clauses:
                if any(self.eval_lit(lit) for lit in clause):
                    continue
                else:
                    unassigned = [lit for lit in clause if self.eval_lit(lit) is None]
                    if len(unassigned) == 0:
                        return True # conflict
                    elif len(unassigned) == 1:
                        unit = unassigned[0]
                        print("propagate", unit)
                        v = abs(unit)
                        self.model[v] = (unit > 0)
                        self.trail[-1].append(v)
                        changed = True
        return False

    def backtrack(self):
        "Backtrack to previous decision level. Returns True if no more levels to backtrack to."
        if not self.trail:
            return True
        cur = self.trail.pop()
        while len(cur) > 1:
            v = cur.pop()
            self.model[v] = None
        v = cur.pop()
        if self.model[v]:
            print("backtrack", v, False)
            self.model[v] = False # try false after true
            cur.append(v)
            self.trail.append(cur)
            return False
        else:
            # We've already tried true and false
            self.model[v] = None
            return self.backtrack()

    def is_conflict(self):
        for clause in self.clauses:
            if all(self.eval_lit(lit) is False for lit in clause):
                print("conflict", clause)
                return True
        return False

    def is_sat(self):
        for clause in self.clauses: # I guess this could be a giant comprehension. harder to read probably.
            if any(self.eval_lit(lit) is True for lit in clause):
                continue
            else:
                return False
        return True

    def decide(self):
        "Pick first unassigned variable and assign it True. Make new decision level in trail"
        for v in range(1,len(self.model)):
            if self.model[v] is None:
                self.model[v] = True
                self.trail.append([v]) # start new trail level
                print("decide", v, True)
                return
        else:
            raise Exception("No unassigned variables to decide")

    def check(self):
        "DPLL loop. return True for sat, False for unsat"
        while True:
            print("top of loop:", self)
            self.propagate()
            if self.is_conflict():
                if self.backtrack():
                    return False
            elif self.is_sat():
                return True
            else:
                self.decide()
```

A simple satisfiable problem

```python
s = Solver()
x = s.makevar()
s.clauses.append([x])
assert s.check()
assert s.model == [None, True]
```

    top of loop: Solver(trail=[], model=[None, None], clauses=[[1]])
    decide 1 True
    top of loop: Solver(trail=[[1]], model=[None, True], clauses=[[1]])

The simplest unsatisfiable problem $x \land \lnot x $

```python
s = Solver()
x = s.makevar()
s.clauses.append([x])
s.clauses.append([-x])
assert not s.check()
```

    top of loop: Solver(trail=[], model=[None, None], clauses=[[1], [-1]])
    decide 1 True
    top of loop: Solver(trail=[[1]], model=[None, True], clauses=[[1], [-1]])
    conflict [-1]
    backtrack 1 False
    top of loop: Solver(trail=[[1]], model=[None, False], clauses=[[1], [-1]])
    conflict [1]

Something with a little more backtracking

```python
s = Solver()
x,y,z = [s.makevar() for _ in range(3)]
s.clauses.append([-x, -y,-z])
s.clauses.append([-x, -y,z])
s.clauses.append([-x, y,-z])
s.clauses.append([-x, y,z])
assert s.check()
assert s.model == [None, False, None, None]
```

    top of loop: Solver(trail=[], model=[None, None, None, None], clauses=[[-1, -2, -3], [-1, -2, 3], [-1, 2, -3], [-1, 2, 3]])
    decide 1 True
    top of loop: Solver(trail=[[1]], model=[None, True, None, None], clauses=[[-1, -2, -3], [-1, -2, 3], [-1, 2, -3], [-1, 2, 3]])
    decide 2 True
    top of loop: Solver(trail=[[1], [2]], model=[None, True, True, None], clauses=[[-1, -2, -3], [-1, -2, 3], [-1, 2, -3], [-1, 2, 3]])
    decide 3 True
    top of loop: Solver(trail=[[1], [2], [3]], model=[None, True, True, True], clauses=[[-1, -2, -3], [-1, -2, 3], [-1, 2, -3], [-1, 2, 3]])
    conflict [-1, -2, -3]
    backtrack 3 False
    top of loop: Solver(trail=[[1], [2], [3]], model=[None, True, True, False], clauses=[[-1, -2, -3], [-1, -2, 3], [-1, 2, -3], [-1, 2, 3]])
    conflict [-1, -2, 3]
    backtrack 2 False
    top of loop: Solver(trail=[[1], [2]], model=[None, True, False, None], clauses=[[-1, -2, -3], [-1, -2, 3], [-1, 2, -3], [-1, 2, 3]])
    decide 3 True
    top of loop: Solver(trail=[[1], [2], [3]], model=[None, True, False, True], clauses=[[-1, -2, -3], [-1, -2, 3], [-1, 2, -3], [-1, 2, 3]])
    conflict [-1, 2, -3]
    backtrack 3 False
    top of loop: Solver(trail=[[1], [2], [3]], model=[None, True, False, False], clauses=[[-1, -2, -3], [-1, -2, 3], [-1, 2, -3], [-1, 2, 3]])
    conflict [-1, 2, 3]
    backtrack 1 False
    top of loop: Solver(trail=[[1]], model=[None, False, None, None], clauses=[[-1, -2, -3], [-1, -2, 3], [-1, 2, -3], [-1, 2, 3]])

# Bits and Bobbles

Even for DPLL, using the Two watched literal scheme could improve the thing, avoiding the big sweeps over all clauses. It's python though man. We exalt in our sin.

Something I find kind of interesting is that DPLL has enough structure to make an SMT solver. You don't need clause learning, and it avoids the need for theories to produce unsat cores. I've never really internalized how you actually figure out the learned clause anyway. Seems like a mostly uninteresting detail unless you're for serious going to build a sat solver.

idea. Try using knownbit <https://pypy.org/posts/2024/08/toy-knownbits.html> domain for model. Then could use integers. clauses are bitmasks and posneg bitvec.

[The silent revolution of sat](https://news.ycombinator.com/item?id=36079115#36081904)

[creusat](https://sarsko.github.io/_pages/SarekSkot%C3%A5m_thesis.pdf) <https://github.com/sarsko/CreuSAT>

<https://fmv.jku.at/fleury/papers/Fleury-thesis.pdf>

<https://github.com/marijnheule/microsat>

<https://www-cs-faculty.stanford.edu/~knuth/programs.html> knuth sat solvers and others

- <https://www.youtube.com/watch?v=II2RhzwYszQ&t=14916s&ab_channel=SimonsInstitute>
- <https://github.com/arminbiere/satch>
-

<https://kmicinski.com/algorithms/sat/2012/09/22/efficient-sat-solving/>

Monoid Floyd Warshall. Semiring. Category (groupoid. Partial semring).

Kleene?
Analog of all UF variants?
Canonized for first class transitive

probably (?) sparse.
Ordered lists might be nice.

x - y <= 4
y - z <= 8
x - zero <= 9 # special zero node

Quantifier Instantiation

Nelson Oppen

<https://arxiv.org/html/2508.13811v1> top mimic or revolt - probablistic grammara learning and exlporing from other methods
<https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/nbjorner-qplay-lpar20.pdf>

SAT + UF. Not a very interesting theory (?)
SAT + ADT . Unification with occurs check, not an egraph. A little easier.

<https://dl.acm.org/doi/10.1007/978-3-031-71177-0_31> smt tutorial cvc5 2024 <https://cvc5.github.io/tutorials/beginners/>

Ge quantifier instantion papers

slotted union

```python
import bisect
# but doing this instead of a hashmap seems nuts. Shrug
class Sparse():
    data:list[tuple[int,object]]
    def items():
        yield from self.data
    
    


```

      Cell In[19], line 2
        class Sparse()
                      ^
    SyntaxError: expected ':'

Maybe this should be in refinement egraphs

```python
from dataclasses import dataclass, field
@dataclass
class Floyd():
    dists : list[list[int]] = field(default_factory=list)
    #dirty : list[tuple[int,int,int]]
    dirty : set[int] = field(default_factory=set)
    #reasons : list[list[object]]
    def makeset(self):
        inf = float("inf")
        for d in self.dists:
            d.append(inf)
        eid = len(self.dists)
        self.dists.append([inf]*(eid + 1))
        self.dists[-1][-1] = 0
        return eid
    # def find(self, i): ? frontier? Single source query
    #def cost(self, i, j):
    #    # do on demand like find?
    #    costs = [[]*len(self.dists) for range(len(self.dists))]

    def __len__(self):
        return len(self.dists)

    def reachable(self, i): # analog of enumerate eclass
        di = self.dists[i]
        inf = float("inf")
        for j in len(self):
            if di[j] != inf:
                yield j,di[j]


    def add_edge(self, i,j,w): # assert_le
        dij = self.dists[i][j]
        if w < dij: # hmm. This judgement requires... uhhh. No. This makes sense.
            self.dists[i][j] = w #min(self.dict[i][j], w)
            self.dirty.add(i)
            self.dirty.add(j)
        #for l in len(self):
        #    for k in len(self):
        #        self.dist[l][k] = min()
    def rebuild(self):
        #for k in range(len(self)): # k in dirty
        inf = float("inf")
        for k in self.dirty: # is this correct?
            dk = self.dists[k]
            for i in range(len(self)):
                di = self.dists[i]
                dik = di[k]
                if dik == inf:
                    continue
                for j in range(len(self)):
                    dkj = dk[j]
                    if dkj == inf:
                        continue
                    dij = di[j]
                    dikj = dik + dkj
                    if dikj < dij:
                        di[j] = dikj
        self.dirty.clear()

f = Floyd()
inf = float("inf")
x,y,z = [f.makeset() for _ in range(3)]
f.add_edge(x,y,1)
f.add_edge(y,z,4)
assert f.dists[x][z] == inf
f.rebuild()
assert f.dists[x][z] == 5
f
```

    Floyd(dists=[[0, 1, 5], [inf, 0, 4], [inf, inf, 0]], dirty=set())

```python
class Floyd2():
    dists : list[dict[int, int]]
    def makeset(self):
        self.dists.append({})
    def add_edge(self, i, j, w):
        di = self.dists[i]
        w0 = di.get(j)
        if w0 is None or w < w0:
            di[j] = w
            self.dirty.add(i)
            self.dirty.add(j)
    def rebuild(self): # This looks more like a seminaive.
        for k in self.dirty:
            dk = self.dists[k]
            for j,wki in dk.items():



    
```

      Cell In[20], line 7
        if w0 is None or w < w0:
                                ^
    SyntaxError: incomplete input

```python
def floyd(edges):
    
    for i,j,w in edges:

```

## 03/2025

Harrison DPLL. Add splitting rule to DP.

Harrison Iterative.

The concept of a trail. It is often a required judo move to remember that your language is maintaining an explicit stack for you and refiying it as a manipulable object. Odds are your language's stack management does not make it efficient or convenient to do to go beyond simple depth first search.

<https://github.com/satlecture/kit2025> Lecture: Practical SAT Solving
<https://github.com/jezberg/maxpre-mallob>

```python
from dataclasses import dataclass
from typing import Optional
type Clause = int
type Var = int
type Lit = int
type TrailInd = int

@dataclass
class Solver():
    """
    trail holds variable number in the order they are assigned. Backtracking reverts the model back to None
    decisions holds the indices of trail where decisions were made.
    model holds the current assignment of variables. None = unassigned, True = assigned true, False = assigned false. Variable 0 is a dummy and unused.
    clauses holds the list of clauses, each clause is a list of literals. A literal is a signed variable number, positive for true, negative for false.
    A clause represents a disjunction of its literals.
    """
    trail : list[Var] = field(default_factory=list)
    decisions : list[TrailInd] = field(default_factory=list)
    model : list[Optional[bool]] = field(default_factory=list)
    clauses : list[list[Lit]] = field(default_factory=list)
    def __post_init__(self):
        self.model.append(None) # var 0 is unused
    def makevar(self):
        vid = len(self.model)
        self.model.append(None)
        return vid
    def propagate(self):
        dirty = False
        while True:
            for clause in self.clauses:
                if any(self.model[abs(lit)] == (lit > 0) for lit in clause):
                    continue
                else:
                    unassigned = [lit for lit in clause if self.model[abs(lit)] is None]
                    if len(unassigned) == 0:
                        return False
                    elif len(unassigned) == 1:
                        unit = unassigned[0]
                        print("propagate", unit)
                        v = abs(unit)
                        self.model[v] = (unit > 0)
                        self.trail.append(v)
                        dirty = True
                        break
            else:
                return True
            if not dirty:
                return None

    def backtrack(self):
        """ return done """
        if not self.decisions:
            return True
        level = self.decisions[-1]
        while len(self.trail) > level + 1:
            v = self.trail.pop()
            self.model[v] = None
        v = self.trail[-1]
        print("backtrack", v, self.model[v])
        if self.model[v]:
            self.model[v] = False # try false after true
            return False
        else:
            self.decisions.pop()
            return self.backtrack()

    def is_conflict(self):
        for clause in self.clauses:
            if all(self.model[abs(lit)] == (lit < 0) for lit in clause):
                #print("conflict", clause, self.model)
                return True
        return False

    def is_sat(self):
        for clause in self.clauses:
            if any(self.model[abs(lit)] == (lit > 0) for lit in clause):
                continue
            else:
                return False
        return True

    def decide(self):
        for v in range(1,len(self.model)):
            if self.model[v] is None:
                self.model[v] = True
                self.decisions.append(len(self.trail))
                self.trail.append(v)
                print("decide", v)
                return
        else:
            raise Exception("No unassigned variables to decide")

    def check(self):
        while True:
            print(self)
            self.propagate()
            print("prop", self)
            if self.is_conflict():
                if self.backtrack():
                    return False
            elif self.is_sat():
                return True
            else:
                self.decide()

s = Solver()
x,y,z = [s.makevar() for _ in range(3)]
s.clauses.append([-x, -y,-z])
s.clauses.append([-x, -y,z])
s.clauses.append([-x, y,-z])
s.clauses.append([-x, y,z])
print(s.check())
s

```

    Solver(trail=[], decisions=[], model=[None, None, None, None], clauses=[[-1, -2, -3], [-1, -2, 3], [-1, 2, -3], [-1, 2, 3]])
    prop Solver(trail=[], decisions=[], model=[None, None, None, None], clauses=[[-1, -2, -3], [-1, -2, 3], [-1, 2, -3], [-1, 2, 3]])
    decide 1
    Solver(trail=[1], decisions=[0], model=[None, True, None, None], clauses=[[-1, -2, -3], [-1, -2, 3], [-1, 2, -3], [-1, 2, 3]])
    prop Solver(trail=[1], decisions=[0], model=[None, True, None, None], clauses=[[-1, -2, -3], [-1, -2, 3], [-1, 2, -3], [-1, 2, 3]])
    decide 2
    Solver(trail=[1, 2], decisions=[0, 1], model=[None, True, True, None], clauses=[[-1, -2, -3], [-1, -2, 3], [-1, 2, -3], [-1, 2, 3]])
    propagate -3
    prop Solver(trail=[1, 2, 3], decisions=[0, 1], model=[None, True, True, False], clauses=[[-1, -2, -3], [-1, -2, 3], [-1, 2, -3], [-1, 2, 3]])
    backtrack 2 True
    Solver(trail=[1, 2], decisions=[0, 1], model=[None, True, False, None], clauses=[[-1, -2, -3], [-1, -2, 3], [-1, 2, -3], [-1, 2, 3]])
    propagate -3
    prop Solver(trail=[1, 2, 3], decisions=[0, 1], model=[None, True, False, False], clauses=[[-1, -2, -3], [-1, -2, 3], [-1, 2, -3], [-1, 2, 3]])
    backtrack 2 False
    backtrack 1 True
    Solver(trail=[1], decisions=[0], model=[None, False, None, None], clauses=[[-1, -2, -3], [-1, -2, 3], [-1, 2, -3], [-1, 2, 3]])
    prop Solver(trail=[1], decisions=[0], model=[None, False, None, None], clauses=[[-1, -2, -3], [-1, -2, 3], [-1, 2, -3], [-1, 2, 3]])
    True





    Solver(trail=[1], decisions=[0], model=[None, False, None, None], clauses=[[-1, -2, -3], [-1, -2, 3], [-1, 2, -3], [-1, 2, 3]])

```python
class Theory(Protocol):
    def push(self):
    def pop(self):
    def propagate(self, )

class SMTSolver(SATSolver):
    theories : list[Theory]
    registered : list[list[Theory]] # inform theory of this variables assignement
    def propagate(self):

class Undo(Protocol):

class Decide(NamedTuple):
    var : Var
class Propagate(NamedTuple):
    var : Var
    reason : Clause



type EID = int
class UFSAT(SATSolver):
    parents : list[EId]
    eqs : list[tuple[EId, EId]] # mapping from bool vars to equality
    def makeset(self):
        # should makeset and makevar be the same?
    def make_eq(self, x, y):
        v = self.make_var()
    def find(self, x):
        while x == self.parents[x]:
            x = self.parents[x]
        return x
    def conflict(self):
        for clause in clauses:
            for eq in self.eqs:
                if self.find(eq[0]) == self.find(eq[1]):
                    return True
        return False
                
    def  union(self, x, y):
        rx = self.find(x)
        ry = self.find(y)
        if rx != ry:
            self.parents[rx] = ry
            self.undo.append(rx)

        



```

```python
        for lit in clauses:
            v = abs(lit)
            val = self.model[v]
            if val is None:
                unassigned.append(lit)
                pass
            elif val == (lit > 0):
                break
        else:
            if len(unassigned) == 0:
                return False
            elif len(unassigned) == 1:
                unit = unassigned[0]
                v = abs(unit)
                self.model[v] = (unit > 0)
                self.trail.append(unit)
```

```python
    def add_clause(self, lits):
        c = sorted(set(lits))
        if len(c) == 0:
            raise Exception("unsat")
        elif len(c) == 1:
            unit = c[0]
            v = abs(unit)
            self.model[v] = (unit > 0)
            self.trail.append(unit)
        else:
            cid = len(self.clauses)
            self.clauses.append(c)
            x,y = abs(c[0]), abs(c[1])
            self.twl[x].append(cid)
            self.twl[y].append(cid)
    
    def set_var(self, vid, value):
        self.model[vid] = value
        lit = vid if value else -vid
        self.trail.append(lit)
        for cid in self.twl[vid]:
            clause = self.clauses[cid]
            # process clause
            for lit in clause:
                v = abs(lit)
                val = self.model[v]
                if val is None:
                    if cid in self.twl[v]:
                        continue
                    else:
                        self.twl[v].append(cid)
                        break
```

## DPLL 1

## DPLL 2

```python
from typing import Optional
from enum import Enum
from dataclasses import dataclass
Lit = int
Trail = tuple[list[Lit], list[int]] # implicit model in trail, second list is decision points. Instead of tagged list[tuple[List, bool]] trail.
Clause = frozenset[Lit]



def unassigned(trail: Trail, cls : Clause) -> set[Lit]:
    return set(abs(l) for l in cls) - set(abs(l) for l in trail[0])

def unit_prop(trail, cnf) -> Optional[Lit]:
    for cls in cnf:
        unassigned_cls = unassigned(trail, cls)
        if len(unassigned_cls) == 1:
            return next(iter(unassigned_cls))
    return None

Truthy = Enum("Truthy", "SAT UNSAT UNKNOWN")

def truthiness(trail, cnf) -> Truthy:
    pmodel = {**{l : True for l in trail[0] }, **{-l : False for l in trail[0]}} 
    if all(any(pmodel.get(l, False) for l in cls) for cls in cnf):
        return Truthy.SAT
    elif any(all(not pmodel.get(l, True) for l in cls) for cls in cnf):
        return Truthy.UNSAT # given current trail, we can't satisfy the cnf
    else:
        return Truthy.UNKNOWN

def backtrack(trail):
    last_decision_index = trail[1].pop()
    last_decision = trail[0][last_decision_index]
    while len(trail[0]) > last_decision_index:
        trail[0].pop()
    return last_decision

def dpll(cnf):
    trail = ([], [])
    for i in range(100):
        print(trail)
        unit_prop(cnf,trail)
        match truthiness(trail, cnf):
            case Truthy.SAT:
                return Truthy.SAT, trail
            case Truthy.UNSAT:
                # backtrack
                print("backtrack")
                l = backtrack(trail)
                while l < 0:
                    if len(trail[0]) == 0:
                        return Truthy.UNSAT, None
                    l = backtrack(trail)
                trail[0].append(-l)
                trail[1].append(len(trail[0])-1)
            case Truthy.UNKNOWN:
                # decide
                unassigned_lits = set(abs(l) for cls in cnf for l in cls) - set(abs(l) for l in trail[0])

                l = next(iter(unassigned_lits)) # is this okay?
                trail[0].append(abs(l))
                trail[1].append(len(trail[0]) - 1)

#dpll([[1,2],[-2]])
#dpll([[1,2],[-2], [-1]])
dpll([[1,2,3],[-2], [-1], [-1]])

```

    ([], [])
    ([1], [0])
    backtrack
    ([-1], [0])
    ([-1, 2], [0, 1])
    backtrack
    ([-1, -2], [0, 1])
    ([-1, -2, 3], [0, 1, 2])





    (<Truthy.SAT: 1>, ([-1, -2, 3], [0, 1, 2]))

```python
@dataclass
class Trail():
    lits : list[Lit]
    decision_points : list[int]
    model : dict[Lit, Optional[bool]] # could be a list.
    def pop(self): # backtrack
        last_decision_index = self.decision_points.pop()
        # TODO: reset model
        last_decision = self.lits[last_decision_index]
    
        return last_decision
    def decide(self, l : Lit):
        self.decision_points.append(len(self.lits))
        self.prop(l)
    def prop(self,  l : Lit):
        self.lits.append(l)
        self.model[abs(l)] = l > 0

# What is the disction between trail and solver. I guess solver has the cnf. two watched literal, etc.

```

# Modelling

Maybe I need more infrastructure for modeling before I get into the nuts and bolts. Start with the brute force solver, show how it fails on problems of interest. That's a nice narrative.

BitVectors.
BitBlasting
Finitedomains

Use z3 or pysat

Hmm. Maybe this is why harrison starts with cnf encoding.

You can build a CNF formula from a truth table. Take each row that evaluates to false and add the negation of that as a clause.

For operations, you can treat them relationally.

Ok so the truth table of `and` is

| x | y | x and y |
|---|---|---------|
| 0 | 0 | 0       |
| 0 | 1 | 0       |
| 1 | 0 | 0       |
| 1 | 1 | 1       |

But the relational form should have twice as many rows.

| x | y | z | z = x and y |
|---|---|---|-------------|
| 0 | 0 | 0 | 1           |
| 0 | 0 | 1 | 0           |
| 0 | 1 | 0 | 1           |
| 0 | 1 | 1 | 0           |
| 1 | 0 | 0 | 1           |
| 1 | 0 | 1 | 0           |
| 1 | 1 | 0 | 0           |
| 1 | 1 | 1 | 1           |

```
x | y | ~z
x | ~y | ~z
~x | y | ~z
~x | ~y | z
```

| x | y | x = y |
|---|---|-------|
| 0 | 0 | 1     |
| 0 | 1 | 0     |
| 1 | 0 | 0     |
| 1 | 1 | 1     |

From this we read off  `x = y` is equivalent to `(~x | y) & (x | ~y)`

Given this, how can there be different encodings? Well they make different intermediate variables. This is a full expansion.

In some respects clausify is a form of my reflection by symbolic execution. Or type directed reification. I know it's bool inputs.

```python
import itertools
def clausify(lits, f):
    for m in itertools.product([True, False], repeat=len(lits)):
        if not f(*m):
            yield [-l if val else l for l, val in zip(lits,m)]

assert list(clausify([1,2], lambda x,y: x or y)) == [[1,2]]
assert list(clausify([1,2], lambda x,y: not x or y)) == [[-1,2]]


def check_equiv(lits, f, cnf):
    litmap = {l : i for i, l in enumerate(lits)}
    return all(f(*m) == all(any(m[litmap[l]] if l > 0 else not m[litmap[-l]] for l in cls) for cls in cnf) for m in itertools.product([True, False], repeat=len(lits)))

assert check_equiv([1,2], lambda x,y: x or y, [[1,2]])
assert check_equiv([1,2], lambda x,y: not x or y, [[-1,2]])
assert check_equiv([1,2,3], lambda x,y,z: (x and y) == z, list(clausify([1,2,3], lambda x,y,z: (x and y) == z)))
list(clausify([1,2,3], lambda x,y,z: (x and y) == z))

```

    [[-1, -2, 3], [-1, 2, -3], [1, -2, -3], [1, 2, -3]]

```python
def apply(f, *args):
    global cnf
    res = Var()
    lits = [l.idx for l in args]
    lits.append(res.idx)
    cnf.extend(clausify(list, f))
    return res


```

```python
import functools
from dataclasses import dataclass
Lit = int

@dataclass
class Ctx():
    cnf : list[list[Lit]]
    counter : int
    def __init__(self):
        self.cnf = []
        self.counter = 0
    def var(self, name=None):
        self.counter += 1
        return Var(self.counter, name, self)
    def apply(self, f, *args):
        res = self.var()
        lits = [l.idx for l in args]
        lits.append(res.idx)
        self.cnf.extend(clausify(lits, lambda *args: args[-1] == f(*args[:-1])))
        return res
    def add(self, v):
        # force v to be true. A way to add constraints
        self.cnf.append([v.idx])
    def check(self):
        cnf = pysat.CNF(from_clauses=self.cnf)
    def to_dimacs(self):
        out = [f"p cnf {len(self.cnf)} {self.counter}]"]
        for cls in self.cnf:
            out.append(" ".join(str(l) for l in cls) + " 0")


@dataclass
class Var():
    name : str
    idx : int # assume positive. We could inline negation a little bit.
    def __init__(self, idx=None, name=None, ctx=None):
        self.idx = idx
        self.name = name
        self.ctx = ctx    
    # This might memoize. Overloading _eq__ makes things a touch fishy.
    #@functools.cache
    def __or__(self, other): return self.ctx.apply(lambda x,y: x or y, self, other)
    def __invert__(self): return self.ctx.apply(lambda x: not x, self)
    def __and__(self, other): return self.ctx.apply(lambda x,y: x and y, self, other)
    def __eq__(self, other): return self.ctx.apply(lambda x,y: x == y, self, other)
    def __hash__(self): return hash(self.idx)


ctx = Ctx()
a = ctx.var("a")
b = ctx.var("b")

(a | b) & b

c = a | b
~a 
d = a | b
print(d)
print(c)
# some memoization might be nice
ctx.add(d == c)
ctx
```

    Var(name=None, idx=3)
    Var(name=None, idx=3)





    Ctx(cnf=[[-1, -2, 3], [-1, 2, 3], [1, -2, 3], [1, 2, -3], [-3, -2, 4], [-3, 2, -4], [3, -2, -4], [3, 2, -4], [-1, -5], [1, 5], [-3, -3, 6], [-3, 3, -6], [3, -3, -6], [3, 3, 6], [6]], counter=6)

```python
from dataclasses import dataclass
cnf = []
def clear_cnf():
    global cnf
    cnf = []

@dataclass
class Var():
    name : str
    counter = [0]
    def __init__(self, name):
        self.name = name
        self.idx = self.counter[0]
        self.counter[0] += 1 #?
    def __add__(self, other):
        cnf.append(yada)
        z = Var("z")
    def __eq__(self, other):
        res = Var("res")
        cnf.append([res, -self.idx, -other.idx])  # other & self => res
        cnf.append([-res, self.idx, -other.idx])  
        cnf.append([-res, -self.idx, other.idx]) 
        cnf.append([res, self.idx, other.idx])   # not other & not self => res
        return res
    def __and__(self, other):
    def __not__(self):
        res = Var("~" + self.name)
        res.idx = -self.idx
        return res


    def __or__(self, other):
        res  = Var("res")
        cnf.append([-res, self.idx, other.idx])
        cnf.append([res, -self.idx, -other.idx])

    def __sub__(self, other):
        pass

def half_adder(a,b):
    s = a ^ b
    c = a & b
    return s, c
def full_adder(a,b,c):
    s = a ^ b ^ c
    c = (a & b) | (a & c) | (b & c)
    return s, c
class BV():
    def __init__(self, name, n, vs=None):
        self.name = name
        self.n = n
        if vs:
            self.vars = vs
        else:
            self.vars = [Var(f"{name}_{i}") for i in range(n)]
    def __getitem__(self, i):
        return self.vars[i]
    def __add__(self, other):
        pass






# class Var(): name, counter, cnf # a global cnf?
x = Var("x")
y = Var("y")
x.idx
y.idx
Var("z").idx

BV = list[Var]

def bvadd(self, a, b):
    c = 0
    cnf = []
    for i in range(len(a)):

        s = a[i] ^ b[i] ^ c
        c = (a[i] & b[i]) | (a[i] & c) | (b[i] & c)
        cnf.append(s)
    res.append(c)
    return c, cnf
class Solver():
    def bvadd(self, a, b):
        c = 0
        res = []
        for i in range(len(a)):
            s = a[i] ^ b[i] ^ c
            c = (a[i] & b[i]) | (a[i] & c) | (b[i] & c)
            res.append(s)
        res.append(c)
        return res
    def bvsub(self, a,b):

    def bveq(self, a,b):


```

    2

```python

```

<https://content.iospress.com/download/journal-on-satisfiability-boolean-modeling-and-computation/sat190085?id=journal-on-satisfiability-boolean-modeling-and-computation/sat190085>  Successful SAT Encoding Techniques

<https://escholarship.org/content/qt5131m4f5/qt5131m4f5_noSplash_0383d245979f16ebc5eae9afdf379bf4.pdf?t=rbvajz>  Satune: Synthesizing Efficient SAT Encoders
THESIS

<https://www.amazon.com/Satisfiability-Problem-Algorithms-Mathematik-Anwendungen/dp/386541527X>  The Satisfiability Problem: Algorithms and Analyses ( schoning toran

# Ackermannization

An online ackermannization could be fun.
Use a hash cons

# Sequent and SAT

Why? A study into sequenty claculus and continuatyions / throw / alegrabci effects. Classical is somehow backtracking. CPS type sig is somehow pierce's law.
2. By understanding where the classicallity is, maybe we can transfer SAT techniques to other logics.
3. Direct proof production out of sat solvers instead of   not `M |= phi` -> M |- not phi  completeness transfer.

A list of backtracking continuations
specializing a sat solver to particular problem generates a proof of that problem.
That code _is_ a proof.
intuitionsitic logic
<https://en.wikipedia.org/wiki/Intuitionistic_logic>
<https://pauldownen.com/publications/cdsc.pdf>  Computational duality and the sequent calculus

"excluded middle = cps / time travel"
Haskell continuation monad. double negation translation

"One potentially helpful way of looking at it: The continuation monad is just a wrapper around (a -> r) -> r) , so Cont r a is essentially just (a -> r) -> r).
Because it's a monad, it's a functor. So if you have an "implication between types", a -> b, then you've got that implication "under the continuation monad", as Cont r a -> Cont r b.  Implications between types capture intuitionistic logic, so the implications "under the continuation monad" also captures at least intuitionistic logic.
But, because the continuation monad is a monad, you've also got join : Cont r (Cont r a) -> Cont r a . And Cont r a is just a wrapper around (a -> r) -> r, so you can get `join : Cont r ((a -> r) -> r) -> Cont r a , which means that "under the continuation monad", (a -> r) -> r implies a. In the special case where r is an uninhabited type, this is double negation elimination, which together with intuitionistic logic, gets you full classical logic. So if P is a classically provable proposition, with the usual connectives, and r is uninhabited, then Cont r P is going to be inhabited.
One big challenge though, (which is what the lambda-mu stuff is about) is finding a good term calculus where
you can construct terms that inhabit exactly the types corresponding to classically provable propositions (without the Cont r indirection), and
which has good properties like normalization that entail corresponding properties for the associated natural deduction system for classical logic (the proof system you get by erasing the terms from the typing rules of the term calculus)." - Graham

`forall a, a` is one encoding of `_|_`. Graham mentions that this is explcitly the principle of explosion. This is a "set" from which you can get anything.

<https://www.cs.cmu.edu/~fp/courses/15317-s23/lectures/12-cont.pdf>
<https://cstheory.stackexchange.com/questions/44078/how-do-continuations-represent-negations-under-the-curry-howard-correspondence>
<https://www.typetheoryforall.com/episodes/realizability-bhk-cps-translation-dialectica>
<https://www.xn--pdrot-bsa.fr/montevideo2016/miquel-slides-krivine-2.pdf>
<https://arxiv.org/search/cs?searchtype=author&query=Downen,+P>
<https://xavierleroy.org/CdF/2018-2019/4.pdf>
<https://en.m.wikipedia.org/wiki/Double-negation_translation>

"continuations are gotos" but double negation shows that typed CPS is terminating. Classical argumentation is "circular" in some sense, but still bounded in another

"That is sort of puzzling. On the one hand, the Cont monad/CPS translation stuff tells you that everything can be embedded in just a simply typed system. On the other hand, there's the perspective where you're actually kind of jumping around in the term, and doing complicated control flow, and it's hard to intuitively see why that ought to terminate.
I'm not sure, but one thing that sort of makes sense to me is that the callcc term (in Pfenning's system) needs to have the data it throws to the continuation as a subterm. So unless it embeds itself as a subterm (so I maybe this is a little question-begging as an explnation if we're asking why it doesn't terminate, since if you're not terminating, maybe you can have a term T that evaluates to something with T as a subterm), it can't "throw itself" to the continuation. So the second time the continuation is called (by a throw), it'll have a different, simpler argument than the first time" - Graham

"
Well, that’s another thing. They are backtracky. And pierces law / cps is somehow backtracky
But I don’t understand a connection better than that statement
How to convert the run of a backtracky sat solver into a sequent calc proof with continuationy proof terms

That's a cool thought
I mean looking at the realizers for EM and resolution would be a start
There you don't need lambdas, just primitive call/cc

Also writing a functional programming cps style backtracky solver

Yeah
Maybe by translation
Leo has this "early return" monad in Lean

I haven’t written an imperative sat solver I’m happy with yet

Yeah that's already a task
I'll put it on the pile
Along with "a stupid SMT solver"
Should be possible
Hard part is the clause learning

But to be clear: proof search != Realizer execution
The realizer is a program that runs the complete proof

Indeed. But sat solvers are model search. And completely failed model search is their notion of proof of negated tautology.
Dis association — 12/21/24, 11:01 AM
Yes that is true

I guess sat solvers are somehow viewable as a direct proof construction routine. No search.
(?)
Naively, a massive proof
Dis association — 12/21/24, 11:05 AM
I guess, but there's definitely backtracking in the implementation

There’s backtracking in the proof system

Yeah maybe
Yeah
Though I'm not sure how restarts fits into all this

Me either
That part does seem deletable

Tbh I think the proof of completeness for a SAT solvers is a nightmare

If you directly interpret its moves as proof steps, I’m not sure you need completeness

Yeah for sure, a case split is a left or elim

Completeness as in relating a property of the models to a property of the proof system

Agree
"""

```

--------
A \/ ~A


SAT solver is trying to prove this sequent. Or at least this is one formulation. You could also start from just cnf, or `|- ~cnf` but all the excluded middles are derivable from nothing.

------------------------------------------
  l1 \/ ~l1  , l2 \/ -l2 , cnf  |-  false

```

Picking a variable is probably using Lor on one of the excluded middle guys

`c2 = l1 \/ l2` the clauses

```
-----------------------------
l1, l2, l3, c1, c2, c3 |- false
```

Or is the callcc from trying to just assume a literal from a clause

```
  -l1       -l2

  ...       ...
  
   l1 |-      l2 |-
----------------
l1 \/ l2 |-

```

unit propagation dignified from sequent rules... hmmm.

I partially evaled with respect to cnf. I need to completely eval with respect to m also to actually have a proof. This is a proof generator still.
Unless I allowed new rules into my sequent calculus. Nothing against that really.
I need to pretty print a program that would have the same execution trace.

Special form only allows me to raise to most recent handler.
Uhhh, No I can use different exception types to jump higher.

I could start from a proof of A \/ ~A

pfenning is really enhaving natural deduction rules.

Cody mentioned resolution is cut.

|- P,Q    ~Q, R |-
  ----------------------

         R |- P 

You need some moves.
  (~Q \/ ~P), (Q \/ R) |- bot

How to dignify tseitsein? Use excluded middle to pull definitions out of aehter? But I can pull definitions out of aehter intuitionsitcally too. Definitions are kind of fine.

excluded middle as time travel.
Proof of A \/ ~A using peirce.
I immeditaely apply callcc so that I can change whether I return left or right

```
theorem double_negation_exclude_middle : (forall a, ¬ ¬ a -> a) -> forall b, b ∨ ¬ b := by
  intro dn
  intro b
  apply dn
  intro p -- This p is the conntiuation of the original question.
  apply p -- now we're at the original question as goal, but I have a way to "undo" if I chose the wrong branch
  right  -- I say I'm going to give you `not b`
  intro r  -- If I were given a b, I could prove false
  apply p     -- but now I teleport back to the original question.
  left   -- give you the b you gave more
  exact r  -- and we're done.

#print double_negation_exclude_middle


def dn2 : (forall a, ¬ ¬ a -> a) -> forall b, b ∨ ¬ b :=
  fun dn b => dn _ (fun p => p (Or.inr (fun b1 => p (Or.inl b1))))
```

```python

def a_nota():
    # |- a \/ ~a
    # |- ~a \/ a, a \/ ~a





```

```python

# https://www.philipzucker.com/python_sat/
import itertools
#list(brute([[0],[1,2],[-1,-2]]))
# each of these is a partial evaluation of eval_clause(clause, m):

# We're raising the clause that is falsified
# m is the part of the context we got from excluded middle.

# maybe more in the evaluation feel, we should have very atomic statements.
# This is starting to feel like proplog.
# proplog is for horn (harrop) clauses, which are classical-like

def clause2(m):
    # this is a little mini expansion of left or rule applied to clause2
    try:
        # m[1] = True or m.add(1)
        assert m[1] # branch 1    `m , l1 |- ``
    except:
        try:
            assert m[2] # branch 2  `m, l2 |- false`
        except:
            raise Exception(1,2)


def clause1(m):
    if not (m[0]):
        raise Exception(0)
def clause2(m):
    if not (m[1] or m[2]):
        raise Exception(1,2) # one of 1,2 must be true
def clause3(m):
    if not (not m[1] or not m[2]):
        raise Exception(-1,-2)
for m in itertools.product([True,False], repeat=3):
    try:
        clause1(m)
        clause2(m)
        clause3(m)
        return "Invalid proof", m
    except Exception as e:
        pass
    return "Valid proof"

```

```python
# using lagerbaic effects style

def clause2(m):
    for 



```

```python
from typing import NamedTuple
import z3
import kdrag.smt as smt
#Proof = NamedTuple('Proof', )
class Proof(NamedTuple):
    thm : z3.BoolRef

def modus(pf1, pf2):
    assert smt.is_implies(pf1.thm) and pf1.thm.arg(0).eq(pf2.thm)
    return Proof(pf1.thm.arg(1))

```

```python
from typing import NamedTuple
import z3
import kdrag.smt as smt
#Proof = NamedTuple('Proof', )
class Proof(NamedTuple):
    ctx : list[z3.ExprRef]
    thm : z3.BoolRef

def ax(thm):
    return Proof([thm], thm)
def weaken(pf, thm):
    return Proof(pf.ctx + [thm], pf.thm)
def impE(pfab,pfa): # application
    assert smt.is_implies(pfab.thm) and pfa.thm.eq(pfab.thm.arg(1))
    return Proof(pfab.ctx, z3.Implies(pfab.thm, pfa.thm))
def impI(thm, pf):
    assert thm in pf.ctx
    return Proof(pf.ctx.remove(thm), z3.Implies(thm, pf.thm))
def andI(pf1, pf2):
    return Proof(pf1.ctx + pf2.ctx, z3.And(pf1.thm, pf2.thm))



```

# Bits and Bobbles

I would like to take the different variations of sat solving and show how to move between them via defunctionalization and the like

[The silent revolution of sat](https://news.ycombinator.com/item?id=36079115#36081904)

[creusat](https://sarsko.github.io/_pages/SarekSkot%C3%A5m_thesis.pdf) <https://github.com/sarsko/CreuSAT>

<https://fmv.jku.at/fleury/papers/Fleury-thesis.pdf>

<https://github.com/marijnheule/microsat>

<https://www-cs-faculty.stanford.edu/~knuth/programs.html> knuth sat solvers and others

- <https://www.youtube.com/watch?v=II2RhzwYszQ&t=14916s&ab_channel=SimonsInstitute>
- <https://github.com/arminbiere/satch>

3-sat solver. Requiring all clauses be in 3sat form may have certain conveniences.

CPS style backtracking ---> sequent proof objects

```python
from typing import NamedTuple

Literal = NamedTuple('Literal', [('idx', int), ('polarity', bool)])
Clause = NamedTuple('Clause', [('literals', list)])
Formula = NamedTuple('Formula', [('clauses', list[Clause]), ('num_vars', int)])

Assignment = NamedTuple('Assignment', [('values', list[bool])])
Pasn = NamedTuple('Pasn', [('assignment', Assignment), ('satisfiable', bool)])

```

# SMT

<https://homepage.cs.uiowa.edu/~tinelli/papers/NieOT-JACM-06.pdf> Solving SAT and SAT Modulo Theories: from an
Abstract Davis-Putnam-Logemann-Loveland
Procedure to DPLL(T)

<https://citeseerx.ist.psu.edu/document?repid=rep1&type=pdf&doi=45036ae8e05d71ea39253f863cfa270b6cdd9aa2> simplify paper

User theories. <https://microsoft.github.io/z3guide/programming/Example%20Programs/User%20Propagator/>

<https://cs.stanford.edu/~preiner/talks/Preiner-Shonan23.pdf> ipasir-up

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

- <https://github.com/cvc5/cvc5/blob/main/src/theory/theory.h>
- <https://github.com/cvc5/cvc5/blob/main/src/theory/output_channel.h>
- <https://ocamlpro.github.io/alt-ergo/latest/API/alt-ergo-lib/AltErgoLib/Theory/module-type-S/index.html>

### z3 as a theory

<https://z3prover.github.io/papers/programmingz3.html#sec-cdclt> Actually, Nikolaj has the same thing basically.
The dual solver. to get minimum assignement.
Also solver has a trail object?

One of the easiest ways of getting a theory solve is to just use z3 as one.
If you assert only theory atoms, basically it's a theory.
You can propagate via many queries.

We could also bolt z3 to cvc5 as an abomination.
Or bolt kissat to z3.
Or z3 that doesn't know what the other hand do-eth

It's an interesting approach to pedgagogy. We show z3 as a magic box, and then slowly start pulling it's pieces into the python metalayer until there isn't any z3 left. Kind of remindas me of the backwards approach to compiler education. At every phase you have something that works. Although ere we have a working entire smt solver at every phase.

Brute force SAT is truth table method by another name. They connote different feelings in me though. truth tables feels like I'm takin a logic course. Brute force sat feels like I'm programming the dumbest thing

```python
from z3 import *

boolmap = {}





```

```python
from z3 import *
import itertools
# using z3expr as my propositions
def negate(p : z3.BoolRef):
    if z3.is_not(p):
        return p.arg(0)
    return z3.Not(p)
def abs(p : z3.BoolRef):
    if z3.is_not(p):
        return p.arg(0)
    else:
        return p

CNF = list[list[BoolRef]]

def vars(cnf):
    return set(abs(l) for cls in cnf for l in cls)

def bits(i,n):
    """convert integer to list of bools"""
    return [bool(i & (1 << j)) for j in range(n)]

def satisfies(model,cnf):
    """ "model checking" of assignment. M |= C """
    return all(any(not model[abs(l)] if is_not(l) else model[l] for l in c) for c in cnf)
    
#class Theory(): ~~ Solver

def brute(cnf):
    vs = vars(cnf)
    s = Solver()
    for tvs in itertools.product([False, True], repeat=len(vs)):
        model = {v : t for v,t in zip(vs,tvs)}
        if satisfies(model, cnf):
            s.push()
            for v, m in zip(vs, tvs):
                s.add(v == m)
            res = s.check()
            if res == sat:
                yield s.model()
            elif res == unsat:
                learned = s.unsat_core()
            s.pop()
    return unsat

p,q,r = Bools('p q r')
list(brute([[p,q],[Not(p), r]]))

#def brute_sat(cnf):
#    return next(brute(cnf), None) is not None
```

    [[p = False, q = True, r = False],
     [p = False, q = True, r = True],
     [p = True, q = False, r = True],
     [p = True, q = True, r = True]]

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
    def validate_model(self, model):
        pass
    # model generate
    #def 
    # model check
    #def m
class Z3Theory(Theory):
    def __init__(self):
        self.s = Solver()
        self.vs = {}
    def push(self):
        self.s.push()
    def mk_var(self, ident):
        self.vs[ident] = FreshConst(BoolSort())
        
        return Bool(f"v{idx}") # FreshConst?
    def get_var(self, enode):
        return enode
    def propagate(self):
        pass # use tactics?
    def assign(self, bvar, sign):
        self.s.add(bvar == sign)
    def new_eq(self, v1, v2):
        self.s.add(v1 == v2)
    def new_diseq(self, v1,v2):
        self.s.add(v1 != v2)
    def validate_model(self, model):
        pass
    
    def pop(self, n):
        self.s.pop(n)
```

### Intercommunicating cvc5 and z3

### dreal = z3 + flint (?)

SMT modulo convex

Could I find piles of interesting little SMT theories to prototype up?
