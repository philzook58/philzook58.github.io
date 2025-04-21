---
title: The Inverse Method is a Good Fit for Datalog Theorem Proving
date: 2025-04-21
---

The inverse method on first glance feels like an oddball. But actually it is rather straightforward when viewed from a datalog lens. The inverse method is a bottom up theorem proving method (typically for a sequent calculus) that finds demand for judgements by inspecting the input formula and using the subformula property of the cut-free sequent calculus. It is very schematically similar / identical to datalog methods for demand or magic set. The main thing that is a little annoying is you probably want a first class set for storing contexts $\Gamma$

# Demand in Datalog

It is a common pattern in datalog that you need to explicitly model your demand. The core of datalog searches for facts and spews out new facts in a growing database. If you define a function-like relation in the most naive way, like fibonacci or factorial or append or what have you, the database will grow forever.

I'm using souffle <https://souffle-lang.github.io/> because it's fine and its what I had installed.

```python
%%file /tmp/fib.dl
.decl fib(n : number, res: number)
fib(0, 1).
fib(1, 1).
fib(N+1, M1 + M2) :- fib(N, M1), fib(N-1, M2).

// The limitsize directive is used to limit the size of the computation
.limitsize fib(n=11)
.output fib(IO=stdout)

```

    Overwriting /tmp/fib.dl

```python
! souffle /tmp/fib.dl
```

    ---------------
    fib
    ===============
    0 1
    1 1
    2 2
    3 3
    4 5
    5 8
    6 13
    7 21
    8 34
    9 55
    10 89
    ===============

This would've worked in prolog or in an ordinary functional programming language. The difference is that there is a stack which tracks which stuff you actually want on demand. These other languages are top down.

A simple method is to make a new "demand" or "need" predicate, tracking what arguments for which the result is needed. You can propagate need by looking at what arguments are needed in the body when you call the functions. For `fib(n) = fib(n-1) + fib(n-2)` you would need to add `fibneed(n-1)` and `fibneed(n-2)` to the demand predicate.

Then every forward call needs to be guarded by the need. `f(X, RES) :- fneed(X), the_body_of_f(X,Res)`.

```python
%%file /tmp/needfib.dl
.decl needfib(n : number)
.decl fib(n : number, res: number)

needfib(N-1) :- needfib(N), N > 0.
needfib(N-2) :- needfib(N), N > 1.


fib(0, 1) :- needfib(0).
fib(1, 1) :- needfib(1).
fib(N, M1 + M2) :- needfib(N), fib(N-1, M1), fib(N-2, M2).

needfib(4).
.output needfib(IO=stdout)
.output fib(IO=stdout)

```

    Overwriting /tmp/needfib.dl

```python
! souffle /tmp/needfib.dl --output-dir=-
```

    ---------------
    needfib
    n
    ===============
    0
    1
    2
    3
    4
    ===============
    ---------------
    fib
    n res
    ===============
    0 1
    1 1
    2 2
    3 3
    4 5
    ===============

The magic set transformation is a variation of this idea. I've been vaguely talking about modelling functional programming, but you also model prolog inside of datalog. Functional programming is a single `f(+, -)` mode <https://www.swi-prolog.org/pldoc/man?section=modes> of prolog. Mode is one of the cooler ideas of prolog. The neat trick of prolog is some programs can be run from input to output or output to input or output and input to bool or partially instantiated in both. This is not actually the case because depending on how you write it, you may want to use imperative constructs or oftentimes the computation will diverge in certain modes.

The magic set transformation is a way to make need predicates that create demand and answers for all the different modes possibilities. <https://souffle-lang.github.io/magicset> <https://users.informatik.uni-halle.de/~brass/lp07/c7_magic.pdf>

Both methods can be seen as a datalog style program analysis over a functional program or a prolog program. A "needed" or "ground" or "compile time constant" analysis are all reasonable analyses to ask for and would help you compile the programs better.

Another connection to note is that the demand and result predicates can be merged in extended datalogs with either lattices or egglog. Egglog produces abstract identifiers as the result when you call `(fib 10)`, which rewrite rules can eventually ground/union to concrete results. A lattice datalog using a Maybe lattice where None means "don't know result yet" can also work.

<https://drops.dagstuhl.de/storage/00lipics/lipics-vol222-ecoop2022/LIPIcs.ECOOP.2022.7/LIPIcs.ECOOP.2022.7.pdf> Functional Programming with Datalog

<https://inst.eecs.berkeley.edu/~cs294-260/sp24/2024-02-21-datalog-fp> Max has some good links in here

# The Inverse Method

It is actually quite confusing what the rules of logic should be once you start questioning them, but a place to start are natural deduction and sequent calculus.

Natural deduction <https://en.wikipedia.org/wiki/Natural_deduction> <https://plato.stanford.edu/entries/natural-deduction/> was designed to have moves that formalize how a human might search for a formal proof. The older Hilbert style systems are like programming in combinators and ND is a bit more like programming in a functional language by the Curry Howard correspondence. Natural deduction systems have introduction and elimination rules for each logical connective like `and` `or` `implies`. Introduction rules have the central connective below the line and elimination have it above

The sequent calculus <https://en.wikipedia.org/wiki/Sequent_calculus> instead has Left and Right rules depending on whether the central connective appears in the left or right side of the produced (below the inference line) sequent.

The act of transforming a sequent calculus proof into a natural deduction proof is quite interesting <https://www.cs.cmu.edu/~fp/courses/atp/handouts/ch3-seqcalc.pdf> . There is a story that the sequent represents the state of a partial natural deduction proof. The hypohteses represent the things we've got bottom up proofs of, and the conclusions are the things we have backwards processed the goals into.

A thing people like is the cut elimination theorem <https://en.wikipedia.org/wiki/Cut-elimination_theorem> which shows that you can take a proof that uses a cut rule and remove it in terms of the other rules. It is a proof transformation method. In some respects, it is similar to other more familiar operations like [negation normal form](https://en.wikipedia.org/wiki/Negation_normal_form) or [conjunctive normal form](https://en.wikipedia.org/wiki/Conjunctive_normal_form) which are used to eliminate classical connectives (cut is not a connective though). These are usually presented in a semantic satisfiability preserving way, but could be presented in a proof transformation style also.

Once you have cut removed, every inference rule of the propositional sequent calculus has only subformulas of the piece below the line go above the line. This is the subformula property and it lets you finitize the bottom up search space with demand. Doing so is the inverse method.

The intuitionistic sequent calculus has only one formula in the right hand side of the sequent. That's what I'll model. (Do I have these rules right? I have such a hard time finding a straightforward reference for this stuff.)

```
Γ ⊢ A      Γ ⊢ B
------------------------ (∧R)
   Γ ⊢ A ∧ B

Γ, A ⊢ C
------------------------ (∧L1)
Γ, A ∧ B ⊢ C

Γ, B ⊢ C
------------------------ (∧L2)
Γ, A ∧ B ⊢ C


Γ ⊢ A
------------------------ (∨R1)
Γ ⊢ A ∨ B

Γ ⊢ B
------------------------ (∨R2)
Γ ⊢ A ∨ B

Γ, A ⊢ C     Γ, B ⊢ C
------------------------ (∨L)
   Γ, A ∨ B ⊢ C


Γ, A ⊢ B
------------------------ (→R)
Γ ⊢ A → B

Γ ⊢ A       Δ, B ⊢ C
------------------------ (→L)
Γ, Δ, A → B ⊢ C

```

This can be made into a datalog program via something like the following

```prolog
% Inverse method datalog prover for intuitionistic propositional logic sequent calculus

goal(imp(a, imp(b, a))).

% can also separate demand into positive and negative polarity
demand(F) :- goal(F).
demand(A) :- demand(imp(A,B)).
demand(B) :- demand(imp(A,B)).
demand(A) :- demand(and(A,B)).
demand(B) :- demand(and(A,B)).
demand(A) :- demand(or(A,B)).
demand(B) :- demand(or(A,B)).
demand(A) :- demand(not(A)).

proven({A}, A) :- demand(A). % refl. sequent A |- A
proven(G, or(A,B)) :- demand(or(A,B)), proven(G, B). % R\/1        G |- A or B
proven(G, or(A,B)) :- demand(or(A,B)), proven(G, A). % R\/2        G |- A or B
proven(G1 | G2, and(A,B)) :- demand(and(A,B)), proven(G1, A), proven(G2, B). % R/\   G |- A and B
proven(G - {A}, imp(A,B)) :- demand(imp(A,B)), prove(G, B), A in G. % R->

proven(G | {or(A,B)} , P) :- demand(or(A,B)), proven(G1, P), proven(G2, P), A in G1, B in G2, G1 - {A} = G = G2 - {B}. % L\/
proven(G - {A} + {and(A,B)} , P) :- demand(and(A,B)), proven(G, P), A in G. % L/\1 
proven(G - {B} + {and(A,B)} , P) :- demand(and(A,B)), proven(G, P), B in G. % L/\2
proven(G1 + (G2 - {B}) + {imp(A,B)} , P) :- demand(imp(A,B)), proven(G1, A), proven(G2, P), B in G2. % L->

proven(G1 | {A}, P) :- demand(A), proven(G1, P) % Weaken left. Or make implicit


% subsumption. If a context is ever dominated, get rid of it.
proven(G1, P) <= proven(G2, P) :- G1 <= G2.
```

It is not that convenient to use souffle for this because of all the set operations. I could use clingo and the python api. I could also probably use egglog, which has Set containers. There are probably other datalogs that could support this program.

As is my usual strategy, I can implement this in python on the z3 ast.

We can compute the needed formula including sign (how many times did we need to travel under the left part of implication)

```python
from kdrag.all import *
def needed(p):
    seen = set()
    def dfs(fm, sign):
        if (fm, sign) in seen:
            return
        seen.add((fm, sign))
        if smt.is_implies(fm):
            a,b = fm.children()
            dfs(a, -sign)
            dfs(b, sign)
        else:
            for c in fm.children():
                dfs(c, sign)
    dfs(p, 1)
    return seen

A,B,C =  smt.Bools("A B C")
needed(smt.Implies(A,B))

```

    {(A, -1), (B, 1), (Implies(A, B), 1)}

A shallow embedding of seminaive datalog can be done by maintaining a loop of new, delta, and old facts. Here for example is a transitive closure query

```
path(X, Y) :- edge(X, Y).
path(X, Y) :- path(X, Z), edge(Z, Y).
```

```python
def trans(edge):
    path = set(edge)
    delta = set(edge)
    while delta:
        print("delta", delta)
        new = set()
        for a,b in delta:
            for c,d in edge:
                if b == c and (a,d) not in path:
                    new.add((a,d))
        delta = new - path

        path |= delta
    return path

edge = {(1,2), (2,3), (3,4)}
trans(edge)
```

    delta {(2, 3), (1, 2), (3, 4)}
    delta {(2, 4), (1, 3)}
    delta {(1, 4)}





    {(1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)}

It is clunkier than the above datalog, but at least I can do the set manipulations I need to.

```python
from kdrag.all import *
def subformula(fm):
    seen = set()
    # pos , neg position

    todo = [fm]
    while todo:
        fm = todo.pop()
        if fm in seen:
            continue
        seen.add(fm)
        for subfm in fm.children():
            todo.append(subfm)
    return seen

def inverse(goal):
    needed = subformula(goal)
    seqs = set((frozenset([A]), A) for A in needed) # proofs. dict[seq, reasons]
    delta = seqs.copy() 
    while delta:
        new = set()

        # rules with two sequents above line. seminaive makes two copies.
        # R/\
        for G1, A in delta:
            for G2, B in seqs:
                if G1 == G2:
                    if (G1, A & B) not in seqs and A & B in needed: new.add((G1, A & B)) # R/\
                    if (G1, B & A) not in seqs and B & A in needed: new.add((G1, B & A)) # R/\

        # proven(G, A | B) :- needed(A | B), proven(G, A).
        # R\/
        for G, A in delta:
            for B in needed: 
                if (G, A | B) not in seqs and A | B in needed: new.add((G, A | B)) #R\/1
                if (G, B | A) not in seqs and B | A in needed: new.add((G, B | A)) #R\/2

        # R->
        for G1, A in delta:
            for B in G1: # R implies
                G = G1 - {B}
                BA = smt.Implies(B, A)
                if (G, BA) not in seqs and BA in needed: new.add((G, BA))
        
        # L/\
        for G1, P in delta:
            for B in G1:
                G = G1 - {B}
                for A in needed:
                    G2 = G | {A & B} # L/\1
                    if (G2, P) not in seqs and A & B in needed: new.add((G2, P))
                    G2 = G | {B & A} # L/\2
                    if (G2, P) not in seqs and B & A in needed: new.add((G2, P))
        
        # L\/. two copies for seminaive.
        for G1, P in delta:
            for G2, P2 in seqs:
                if P.eq(P2):
                    for A in G1:
                        for B in G2:
                            G = (G1 - {A}) | (G2 - {B}) | {A | B}
                            if (G, P) not in seqs and A | B in needed: new.add((G, P))
                            G = (G1 - {A}) | (G2 - {B}) | {B | A}
                            if (G, P) not in seqs and B | A in needed: new.add((G, P))

        # L->  Again two copies for seminaive.
        for G1, A in delta:
            for G2, P in seqs:
                for B in G2:
                    if smt.Implies(A,B) in needed:
                        G = (G2 - {B}) | {smt.Implies(A,B)} | G1
                        if (G, P) not in seqs: new.add((G, P))
        for G2, P in delta:
            for G1, A in seqs:
                for B in G2:
                    if smt.Implies(A,B) in needed:
                        G = (G2 - {B}) | {smt.Implies(A,B)} | G1
                        if (G, P) not in seqs: new.add((G, P))

        # WL weaken left rule.
        # We could remove this by magicking up context pieces out of needed when we need them.
        for G, P in delta:
            for A in needed:
                G1 = G | {A}
                new.add((G1, P))

        # do subsumption check here?

        delta = new - seqs
        seqs |= delta
        if (frozenset(), goal) in seqs: # early stopping
            return True, seqs
    return False, seqs
    
A,B,C = smt.Bools("A B C")

assert inverse(smt.Implies(A, A))[0]
assert inverse(smt.Implies(A & A, A))[0]
assert inverse(smt.Implies(A, smt.Implies(B, A)))[0]
assert not inverse(smt.Implies(A | B, A))[0]
assert inverse(smt.Implies(A | B, A | B))[0]
assert not inverse(smt.Implies(A | B, A & B))[0]
# https://en.wikipedia.org/wiki/Peirce%27s_law Pierce's law is a classical tautology, but not provable intuitionistically.
assert not inverse(smt.Implies(smt.Implies(smt.Implies(A,B), A),A))[0]

```

    {A, Implies(A, A)}
    {Implies(And(A, A), A), A, And(A, A)}
    {A, Implies(A, Implies(B, A)), B, Implies(B, A)}
    {A, Or(A, B), B, Implies(Or(A, B), A)}
    {A, Or(A, B), Implies(Or(A, B), Or(A, B)), B}
    {Implies(Or(A, B), And(A, B)), A, And(A, B), B, Or(A, B)}
    {Implies(A, B), Implies(Implies(Implies(A, B), A), A), A, B, Implies(Implies(A, B), A)}

# Bits and Bobbles

The inverse method extends to other logics such as modal. I'm not sure how you add forall and exists? You need to enumerate terms too?

You can add proofs by making the `seq` set a `dict` that has a value stating which rule and what subproofs it needed.
rather than `new.add((G,A & B))` make it `new[(G, A & B)] = ("R/\", (A, B, G1, G2))`. That's enough given the seq table to reconstruct the proof at the end. This is an example of datalog provenance. Record a tag for which rules was used, and the data bound in the rule and attach it to the fact. <https://souffle-lang.github.io/provenance> <https://www.philipzucker.com/metamath-datalog-provenenance/>

A fun idea: Use Z3 to prune? Classical logic let's you prove strictly more things / collapses distinctions. Anything with a SAT countermodel will not be provable. Kind of seems more fitting of a backwards search method though. Let's you prune bad branches of search space.

This one is an old idea. I've wanted to do something about `inverse method ~ magic set` for a while. It's good to get it out there.

<https://www.philipzucker.com/ljt/> The ljt system is a good one for top down proving of intuitionsitc logic

<https://jens-otten.de/tutorial_cade19/> build your own first order prover

Frank Pfenning's notes are an incredible and unique resource.

- <https://www.cs.cmu.edu/~fp/courses/15317-s23/lectures/22-invmethod.pdf>
- <https://www.cs.cmu.edu/~fp/courses/99-atp/handouts/fwdseq.pdf>

- <https://link.springer.com/chapter/10.1007/3-540-55602-8_198>  Theorem proving in non-standard logics based on the inverse method
- <https://link.springer.com/chapter/10.1007/978-3-642-02959-2_19>  Efficient Intuitionistic Theorem Proving with the Polarized Inverse Method

Handbook of automated reasoniing

Removing weakening. Anything that has Gamma,A |- B, the A can come out of nowhere now for implicit wekaening.

Replace `for B in G2` with `for B in needed`. Hmm about the same.

```python
from kdrag.all import *
def subformula(fm):
    seen = set()
    # pos , neg position

    todo = [fm]
    while todo:
        fm = todo.pop()
        if fm in seen:
            continue
        seen.add(fm)
        for subfm in fm.children():
            todo.append(subfm)
    return seen

def inverse(goal):
    needed = subformula(goal)
    print(needed)
    seqs = set((frozenset([A]), A) for A in needed) # proofs. dict[seq, reasons]
    delta = seqs.copy() 
    while delta:
        new = set()

        # rules with two sequents above line. seminaive makes two copies.
        # R/\
        for G1, A in delta:
            for G2, B in seqs:
                G = G1 | G2 
                if (G, A & B) not in seqs and A & B in needed: new.add((G, A & B)) # R/\
                if (G, B & A) not in seqs and B & A in needed: new.add((G, B & A)) # R/\

        # proven(G, A | B) :- needed(A | B), proven(G, A).
        # R\/
        for G, A in delta:
            for B in needed: 
                if (G, A | B) not in seqs and A | B in needed: new.add((G, A | B)) #R\/1
                if (G, B | A) not in seqs and B | A in needed: new.add((G, B | A)) #R\/2

        # R->
        for G1, A in delta:
            for B in needed: # R implies
                G = G1 - {B}
                BA = smt.Implies(B, A)
                if (G, BA) not in seqs and BA in needed: new.add((G, BA))
        
        # L/\
        for G1, P in delta:
            for B in needed:
                G = G1 - {B}
                for A in needed:
                    G2 = G | {A & B} # L/\1
                    if (G2, P) not in seqs and A & B in needed: new.add((G2, P))
                    G2 = G | {B & A} # L/\2
                    if (G2, P) not in seqs and B & A in needed: new.add((G2, P))
        
        # L\/. two copies for seminaive.
        for G1, P in delta:
            for G2, P2 in seqs:
                if P.eq(P2):
                    for A in G1:
                        for B in G2:
                            G = (G1 - {A}) | (G2 - {B}) | {A | B}
                            if (G, P) not in seqs and A | B in needed: new.add((G, P))
                            G = (G1 - {A}) | (G2 - {B}) | {B | A}
                            if (G, P) not in seqs and B | A in needed: new.add((G, P))

        # L->  Again two copies for seminaive.
        for G1, A in delta:
            for G2, P in seqs:
                for B in needed:
                    if smt.Implies(A,B) in needed:
                        G = (G2 - {B}) | {smt.Implies(A,B)} | G1
                        if (G, P) not in seqs: new.add((G, P))
        for G2, P in delta:
            for G1, A in seqs:
                for B in needed:
                    if smt.Implies(A,B) in needed:
                        G = (G2 - {B}) | {smt.Implies(A,B)} | G1
                        if (G, P) not in seqs: new.add((G, P))


        # do subsumption check here?

        delta = new - seqs
        seqs |= delta
        if (frozenset(), goal) in seqs: # early stopping
            return True, seqs
    return False, seqs
    
A,B,C = smt.Bools("A B C")

assert inverse(smt.Implies(A, A))[0]
assert inverse(smt.Implies(A & A, A))[0]
assert inverse(smt.Implies(A, smt.Implies(B, A)))[0]
assert not inverse(smt.Implies(A | B, A))[0]
assert inverse(smt.Implies(A | B, A | B))[0]
assert not inverse(smt.Implies(A | B, A & B))[0]
# https://en.wikipedia.org/wiki/Peirce%27s_law
assert not inverse(smt.Implies(smt.Implies(smt.Implies(A,B), A),A))[0]
```

    {A, Implies(A, A)}
    {Implies(And(A, A), A), A, And(A, A)}
    {A, Implies(A, Implies(B, A)), B, Implies(B, A)}
    {A, Or(A, B), B, Implies(Or(A, B), A)}
    {A, Or(A, B), Implies(Or(A, B), Or(A, B)), B}
    {Implies(Or(A, B), And(A, B)), A, And(A, B), B, Or(A, B)}
    {Implies(A, B), Implies(Implies(Implies(A, B), A), A), A, B, Implies(Implies(A, B), A)}

Not much faster. Hmm.

Clingo has nice python interop. Could use it to implement my sets. But whatev. Seminaive isn't that complicated on a single program.

```python
import clingo
ctl = clingo.Control()
ctl.add("base", [],
"""
needfib(N-1) :- needfib(N), N > 0.
needfib(N-2) :- needfib(N), N > 1.

fib(N, M1 + M2) :- needfib(N), fib(N-1, M1), fib(N-2, M2).
""")
ctl.ground([("base", [])])
ctl.
```

    []

```python

```

# Bits and Bobbles

I associate the world "Datalog" with bottom-up logic programming.

To other people, datalog is logic programming with only atoms allowed as entries in rules. It can be perfomed bottom up or top down.

```python
if [] or []:
    print("True")
```

<https://www.cs.cmu.edu/~fp/courses/15317-s23/lectures/22-invmethod.pdf>
<https://www.cs.cmu.edu/~fp/courses/99-atp/handouts/fwdseq.pdf>
foreward sequent claculus. Gamma |- A   means we needed Gamma

Should I do a non seminaive version. Would it be cleaner?
Given clause vs seminaive vs full naive
Split needed into positive and negative

```python

```

```python

    

```

    {(A, -1), (B, 1), (Implies(A, B), 1)}

```python
from kdrag.all import *
def subformula(fm):
    seen = set()
    # pos , neg position

    todo = [fm]
    while todo:
        fm = todo.pop()
        if fm in seen:
            continue
        seen.add(fm)
        for subfm in fm.children():
            todo.append(subfm)
    return seen

def inverse(goal):
    needed = subformula(goal)
    print(needed)
    seqs = set((frozenset([A]), A) for A in needed) # proofs. dict[seq, reasons]
    delta = seqs.copy() 
    while delta:
        if (frozenset(), goal) in seqs:
            return True, seqs
        new = set()
        for G1, A in delta:
            # two sequent rules
            for G2, B in seqs:
                G = G1 | G2
                AandB = A & B 
                if (G, AandB) not in seqs and AandB in needed: new.add((G, AandB))
                AandB = B & A # Do we have this by symmettry?
                if (G, AandB) not in seqs and AandB in needed: new.add((G, AandB))
                # TODO: L implies

            for B in needed: #Ror
                AorB = A | B
                if (G, AorB) not in seqs and AorB in needed: new.add((G, AorB))
                AorB = B | A
                if (G, AorB) not in seqs and AorB in needed: new.add((G, AorB))

            # select out of left sequent
            for B in G1: # R implies
                G = G1 - {B}

                BA = smt.Implies(B, A)
                if (G, BA) not in seqs and BA in needed: new.add((G, BA))
                for C in needed:
                    G2 = G | {B & C} #  # Land1
                    if (G2, A) not in seqs and B & C in needed: new.add((G2, A))
                    G2 = G | {C & B} # Land2
                    if (G2, A) not in seqs and C & B in needed: new.add((G2, A))
        delta = new - seqs
        seqs |= delta

    return False, seqs
    
A,B,C = smt.Bools("A B C")
inverse(smt.Implies(A, A))
inverse(smt.Implies(A & A, A))

```

    {A, Implies(A, A)}
    {Implies(And(A, A), A), A, And(A, A)}





    (True,
     {(frozenset(), Implies(And(A, A), A)),
      (frozenset({A, And(A, A)}), And(A, A)),
      (frozenset({And(A, A)}), A),
      (frozenset({And(A, A)}), And(A, A)),
      (frozenset({A}), A),
      (frozenset({A}), And(A, A)),
      (frozenset({Implies(And(A, A), A)}), Implies(And(A, A), A))})

```python
            
                #AandB = A & B
                #G = G1.remove(B)
                #if (G, AandB) not in seqs and AandB in needed:
                #    seqs.add((G, AandB))
                #    todo.append((G, AandB))
            

        """
            #notA = ~A
            #if (G1, )
        for B in G1:
            notB = ~B
            if (G1, A) not in seqs and A in needed:
                todo.append((G1, A & notB))
                seqs.add((G1, A & notB))
        """
        """            
        for B in needed:
            AorB = A | B
            if (G1, AorB) not in seqs and AorB in needed: 
                todo.append((G1 | G2, AorB))
                seqs.add((G1 | G2, AorB))
        """
```

```python
frozenset([1,2,3]) | {2}
```

    frozenset({1, 2, 3})

Sequent calculus is natural deduction where we are buildin trees at top and bottom.

We need zipper continuations to build final tree.

Prolog conitnuation passing style.
We always ave just one thing on the other side.
Maybe it's nice to always have K as first parameter? Or factored out somehow.

Triska had a lovely generic zipper.

```python
path(X,Z) :- edge(X,Y), path(Y,Z).

edge(1,2,K) :- K.
edge(2,3,K) :- K.

path(X,Y,K) :- edge(X,Y,K).
path(X,Z,K) :- edge(X,Y, path(Y,Z,K)).


% intro
prove(Gam, and(X,Y)) :- !, prove(Gam, X), prove(Gam,Y).
prove(Gam, or(X,Y)) :- prove(Gam,X) ;  prove(Gam,Y).
prove(Gam, X) :- elim(Gam, X).


elim([ | Gam],X) :- member(X, Gam).
elim([or(A,B) | Gam], X) :- prove({A | Gam|, X), prove([B | Gam], X).
elim([and(a,d)  | Gam], X) :- prove([A,B | Gam], X).
elim([A|Gam], X) :- prove([Gam, A], X). % somehow move through the context and do it all


% cps
% Gam = Env ?
prove(Gam, and(X,Y), K) :- prove(Gam,  X,  prove(Gam, Y, K)).


 % tabling via cps?

% chr for forward inference.
:- chr ctx/1

ctx(A), ctx(A) => ctx(A).
ctx(and(A,B))==> ctx(A), ctx(B).
ctx(impl(A,B)) => { ctx(A), prove(B), del(A) }, ctx(B). % but only delete if it isn't in context. This is why linearity might be nice,
ctx(A) | getctx(B) => A = B. 


% multiset rewriting semantics of SNAX


% SAT prolog using two watched literal scheme and delayed wakeup like King et all

```

Sequent calculus
What is it?

The subformula property

```
goalsubform(A) :- goalsubform(and(A,B))


seq({A}, {A}) :- goalsub(A)

% natrual deduction has isngle right hand consequent
% a natrual guess to
{seq(A,B) :- subgoal(A), subgoal(B)

:- 

:- goal(P), not seq( ,P)

```

Can I drectly use magic set in souffle.

Gam |-
--------------------

The inverse method is a magic set / demand transformation

Voronkov
Maslov
Pfenning

```python
"""
need() :- need(Ctx, and(A,B)).
need() :- need(Ctx, or(A,B)).
need() :- need(Ctx, not(A)).


"""
```

A little bit longer. We got up through the intuitive interpretation of lambda-mu terms that Parigot suggests, how the term for Peirce's law should work, and my attempts to make sense of multiple-conclusion sequents as typing judgements. Didn't get to the proof-normalization procedure he sketches.

The subformula property is important to the inverse method, which is a way of pruning what formulas one may need to consider in a bottom up automated method
I think it's related to the idea of a magic set transformation in datalog
But I've sort of been too confused to go further (edited)

frank pfenning also has some notes on inverse method
I'm not strictly sure what magic set is. But I do get the idea of emulating "demand". I think the motivation is to emulate prolog (a top down / backwards system) with datalog (a bottom up / forward system). You can do this by making "demand" or "magic-set" predicates that track an overapproximation of the possible prolog queries
Kind of it's like doing some kind of statc analyss / abstract interpretation over prolog programs using datalog

This comes up for example if you want to compute a function
fact(0,1). fact(n+1,n*m) :- fact(n, m).

This is a good prolog program
But a non terminating datalog one

demand_fact(n-1) :- demand_fact(n), n > 0.
fact(n+1,n*m) :- fact(n, m), demand_fact(n+1).

This guards the rule by demand so it stops eventually.

If you want to calculate fact(7,?) you seed the database with demand_fact(7).

Demand rules basically propagates what subfunction calls you need answered in order to answer the current demand.
o
So they tend to push demand to decreasing arguments.

Magic set is a slightly more subtle thing that pushes around which variabes are ground or not.

<https://souffle-lang.github.io/magicset>

It is a generalization of the above, which is a functional picture with obvious inputs and outputs. Which param in prolog is output vs input depends on which things are grounded
Presumably demand here would be breaking up the formula to be proven into it's subformula
Whose subproofs you desire
And then a straight translation of the rules of inference to datalog rules ought to actualy do the forward part.
I suspect the rub is that there are many possible subformula context to the left of the sequent to ask for
But maybe answer set programming can offer something there
It lets you sprinkle in a little SAT like search into your datalog
Is it obvious when a calculus has the subformula property?
<https://www.cs.cmu.edu/~fp/courses/99-atp/lectures/lecture19.html>

Can be highly non-obvious. It entails consistency, so there's a sense in which the proofs are intrinsically hard, or at least they require something strong in the background.
<https://en.wikipedia.org/wiki/Takeuti%27s_conjecture>

but a cut free system its obvious?

Yep, without cuts (in a sequent calculus), it's immediate from inspecting the rules. (edited)
OK, I'm trying to understand the demand thing, without much logic programming fluency. The idea is that you can by adding demand(7), you can infer demand(n) for n<7, and by mixing demand into the rules for factorial, you prevent divergence caused by endless generation of factorial relation facts?
