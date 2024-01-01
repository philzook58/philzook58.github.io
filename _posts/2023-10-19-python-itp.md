---
date: 2024-01-01
layout: post
title: "Knuckledragger: Experimenting with a Python Proof Assistant"
---

Something that I'm tinkering with is making a proof assistant in python.

It's very preliminary, but I've place some ideas [here](https://github.com/philzook58/knuckledragger). I call it Knuckledragger (thanks Zach!). I have already done too much without writing about it. Write early, write often.

There are a few reasons to do this in python:

- Huge amounts of tooling (Jupyter, documentation, editors etc)
- Huge numbers of packages (z3py, sympy, cvxpy, numpy, scipy, networkx, sage stuff, etc)
- Huge userbase and familiarity
- It is huge burden for a new user to learn formal mathematical proof, _and_ a new language.

It is relatively unattempted (or at least wildly successful?) to make a proof assistant in a standard language (Let's say >1% TIOBE index). It is not unknown however. Here are some examples of attempting a python based ITP are [HolPy](https://arxiv.org/abs/1905.05970), [Boole](https://github.com/avigad/boole/tree/master/examples), [Prove-It](https://www.osti.gov/servlets/purl/1761359).

It is possible that I will be driven into agreeing using one of the existing systems (in python or otherwise) is the right thing to do. I'd consider that a success. I'm enjoying the process very much irregardless.

Something I've experienced in using automated logic solvers ([z3](https://microsoft.github.io/z3guide/), [eprover](https://github.com/eprover/eprover), [egglog](https://github.com/egraphs-good/egglog)) is that one can perform nice big steps in a proof like rearranging expressions or facts about linear arithmetic, but that there are not facilities for chaining these results together. You also can't express axiom schema (like induction!) or definitional mechanisms. You can only bring the edges close together in file and wave your hands. I think his semi-automated corner of the design space is interesting. One puts all the meat in the solvers (and trusting that z3, eprover, etc are basically correct, de bruijn be damned) and has a light layer of trustable chaining and metaprogramming on top. This is not an unknown idea. It has been around since the very first solvers in the 50s and is similar to the approaches of [F*](https://www.fstar-lang.org/), [Liquid Haskell](https://ucsd-progsys.github.io/liquidhaskell/), and [Dafny](https://dafny.org/).

A traditional inference chaining design can be seen in LCF style kernels, where inference rules are implemented as functions taking in an abstract datatype `theorem` and outputting a new `theorem`. I found it a revelation to read [chapter 6](https://www.cl.cam.ac.uk/~jrh13/atp/OCaml/lcf.ml) of John Harrison's book on this topic. You can look inside `theorem` to see the `formula`  `formula_of_proof : theorem -> formula` but there is not explicit function to do the opposite (except an `unsafe_axiom : formula -> theorem` primitive.). In a language like Ocaml, the immutability and type system give comfort that you can't make bad deductions through accidentaly mutating something you shouldn't have.

Python is extremely dynamic, mutable, and it is hard to protect your theorems. There are a few approaches to this chaining mechanism amenable to python.

- Hidden constructors and `frozen`. This is most like the LCF approach. It's fine.
- A central authority that stores the known theorems. Proofs are keys into this database. The keys may be names or just indices into some list
- Crypto signing. If the proof authority maintains a secret key it uses to sign theorems from inferences it permits, it can check these crypto signatures when the theorem comes back in.
- Explicit checkable proof objects that you hand back to the user. Propositions as types is one choice of how to do this. A simpler perhaps clunkier choice is to just have a tree recording what theorems depended on which theorems. These proof objects could be seen as traces of the interactions above between the authority and the user. The proof database of the authority with some annotations can also be seen as this data structure. You then have to also write a checker (which is in a sense a replay of the interaction).

## Commutativity of Addition

As a toy example to demonstrate some ideas, here I prove the commutativity of peano addition using an induction axiom schema. This is not possible for Z3 on it's own.

Of course, this is very easy using built in arithmetic.

```python
from z3 import *
x,y = Ints("x y")
prove(x + y == y + x)
```

This uses the "crypto" form I was referring to above which signs theorem via a secret key. `check` confirms the hash, `trust` is a primitive to make axioms. `infer` is a mega inferrance rule that admits anything that z3 can prove.

In order to describe Natural number induction, we have some choices. We could either use a higher order axioms (since Z3 does support simply typed higher order functions called "Arrays") or we can use an axiom _schema_. An axiom schema is a family of axioms. We can implement such a family as an axiom  producing function (another interesting option not explored here is as a generator of axioms, which would enable a brute force automation technique).

The commutativity of addition is a little funky to prove because it depends on the structure of hw you defined addition, which feels odd to naive mathematics. Indeed it feels odd from a certain perspective to say you "prover" commutativty. Isn't that part of the definition of addition? Well, here we define addition only be using structural recursion on the first argument, so no it is not. This is a formal and technical point sadly. You can compare what is done here to Coq for example <https://softwarefoundations.cis.upenn.edu/lf-current/Induction.html>.

First we prove that `0 + x = x + 0` which again isn't quite obvious. Then we use that as a lemma in the full proof.

```python
from typing import Any, Tuple, List
from z3 import *

Form = Any
Thm = Tuple[int, Form]

# Helpful Boolean Syntax
BoolRef.__and__ = lambda self, other: And(self, other)
BoolRef.__or__ = lambda self, other: Or(self, other)
BoolRef.__invert__ = lambda self: Not(self)
def QForAll(vars, hyp, conc):
    """Quantified ForAll helper"""
    return ForAll(vars, Implies(hyp, conc))

#########################
### Kernel
#########################
def check(thm: Thm):
    """Check that a theorem hashes against secret key"""
    hsh, form = thm
    assert hsh == hash(("secret", form))


def trust(form: Form) -> Thm:
    """Trust a formula as a theorem by adding a hash"""
    return hash(("secret", form)), form


def infer(hyps: List[Thm], conc: Form, timeout=1000) -> Thm:
    """Use Z3 as giant inference step"""
    s = Solver()
    for hyp in hyps:
        check(hyp)
        s.add(hyp[1])
    s.add(Not(conc))
    s.set("timeout", timeout)
    res = s.check()
    if res != z3.unsat:
        print(s.sexpr())
        if res == z3.sat:
            print(s.model())
        assert False, res
    return trust(conc)

################################
### Peano Arithmetic
################################

# Z3py algebraic datatype of natural numbers
Nat = Datatype("Nat")
Nat.declare("zero")
Nat.declare("succ", ("pred", Nat))
Nat = Nat.create()
print(Nat.succ(Nat.zero))

# Peano induction axiom schema
def induct(P : Form) -> Thm:
    print(P.sort())
    assert P.sort().name() == "Array"
    assert P.sort().domain() == Nat
    assert P.sort().range() == BoolSort()
    n = FreshConst(Nat)
    hyp = P[Nat.zero] & QForAll([n], P[n], P[Nat.succ(n)])
    #------------------------------------------
    conc =  ForAll([n], P[n])
    return trust(Implies(hyp, conc))

x,y = Consts("x y", Nat)
# We just admit the definition of add, but really we need a termination checking mechanism.
add = Function("add", Nat, Nat, Nat)
zero_add = trust(ForAll([x], add(Nat.zero, x) == x))
succ_add = trust(ForAll([x,y], add(Nat.succ(x), y) == Nat.succ(add(x, y))))

P = Lambda([x], add(x,Nat.zero) == add(Nat.zero,x))

base = infer([], P[Nat.zero])
ind = infer([zero_add, succ_add], QForAll([x], P[x], P[Nat.succ(x)]))
add_zero = infer([base,ind,induct(P)], ForAll([x], P[x]))
# Alternative proof letting it figure out base and ind
add_zero_prime = infer([zero_add, succ_add, induct(P)], ForAll([x], P[x]))


P = Lambda([x], ForAll([y], add(x,Nat.succ(y)) == Nat.succ(add(x,y))))

add_succ = infer([zero_add,succ_add, induct(P)], ForAll([x],P[x]))
comm_add = infer([zero_add, succ_add, add_zero, add_succ, induct(Lambda([x], ForAll([y], add(x,y) == add(y,x))))] ,
                  ForAll([x,y], add(x, y) == add(y, x)))

print(comm_add)

```

# Bits and Bobbles

Thanks to Zach Tatlock for inspiration on the name!

I would love for knuckledragger to target relatively mundane engineering mathematics and computer science. I think the high falutin mathematical community is better served by higher powered systems. Type theory and set theory are too high a bar for most. I want things that a former physicist could appreciated, and I think I have the context for that.

Metaprogramming in most systems is a janky mess, because building a metaprgramming system is a huge engineering undertaking. HOL Light seems like it has it right by directly just working in OCaml. That may be part of it's secret sauce (beside just being Harrison) to getting so much distance. Using a well supported existing language s the right call. Maybe Lean can pull off using itself as it's metaprogramming system. That'd be great. There's a lot of momentum there and Leo de Moura is a monster.

I fear using Z3 will fail complex quantifier reasoning. But I then may cash out to eprover/vampire which have good quantifier reasoning. Z3 is super useful, the python bindings are fantastic.

A Tactic system can be orchestrated around the raw capablities above without sacrificaing the soundness of the kernel. Isar style, backwards goal, and calc tactics all seem fun. At what point of complexity of tactics is the kernel kind of irrelevant?

 I'm a weirdo that really likes funky programming languages and paradigms (functional, logic, depedently typed, etc). I have a lot of difficulty bringing my non PL friends on board anything that isn't python. It is a lost cause in my opinion. Do not expect the world at large to start using functional programming languages. Maybe we don't even actually want that.  [Mathematical Logic through Python](https://www.logicthrupython.org/)

ACL2 is a good place to look for inspiration. I don't want the fanciest most expressive logic in the world. Python and lisp do have a certain kinship (see for example)

It's interesting to compare what I'm doing here with [myself in 2019](https://www.philipzucker.com/programming-and-interactive-proving-with-z3py/). On one hand, I feel like I've made no progress at all. On the other,  think I'm just cargo culting the experience of using coq tactics in this post without a strong mental model of what it means to have a proof. On the other hand, to have the tactic system be the kernel is an interesting design that may not occur to me today because I'm too indoctrinated at this point.

Exporting proof certificates from different solvers is a of course interesting and would be preferable to just trusting them. The situation has not settled there though. There's dedukti, [alethe](https://www.youtube.com/watch?v=ygsY2LlWyQI&ab_channel=InstituteforPure%26AppliedMathematics%28IPAM%29), z3's current format, [it's in progress format](https://github.com/Z3Prover/z3/discussions/4881), datalog provenance, egg/egglog proof data, twee proofs, metamath, and TPTP proof output. None of these are dominant or play that nice with each other. Maybe recording whatever proof output in the proof db is ok. DRAT for SAT is fairly standard.

Sometimes solvers output objects that are very useful. Sympy can output an antiderivative, checking it is indeed an antiderivatve is relatively easy. Likewise for SAT solutions, dual vectors in linear programming and some others.

CPressey also has some very interesting python assistants <https://github.com/catseye/Eqthy> and others. <https://codeberg.org/catseye/Philomath#philomath> philomath is a C based one! That's an amusing idea.

It amuses me that chaining together automated theorem provers + a proof db / certificate system is also buildable in bash. Why not? It'd be kind of nice even. Bash is the nicest language to call other programs in / has god support for splicing.

A blog post a week this year? No matter how raw and uneditted? That'd be cool.

# Blah Blah Blah

## A little propositional logic without usig z3

```python
from typing import Any, Tuple
Fm = Any #typing.Union[tuple("->", Fm, Fm), tuple("-", Fm), str]
Thm = Tuple[int, Fm]

def trust(a : Fm) -> Thm:
  return hash(("secret",a)), a # Use a crypto hash function here

def check(a : Thm):
  hsh, form = a
  assert hsh == hash(("secret",form)) 

def modus(a : Thm, ab : Thm) -> Thm:
  check(ab)
  check(a)
  _, a = a
  _, (arr, a1, b) = ab
  assert arr == "->"
  assert a1 == a
  return trust(b)

# axiom schema of propositional logic
def axiom1(A : Fm, B : Fm) -> Thm:
    return trust(("->", A, ("->", B, A)))

def axiom2(A : Fm, B : Fm, C : Fm) -> Thm:
    return trust(("->", ("->", A, ("->", B, C)), ("->", ("->", A, B), ("->", A, C))))

def axiom3(A, B):
    return trust(("->", ("->", ("-", A), ("-", B)), ("->", B, A)))


def pprint_fm(a):
    if a[0] == "->":
        return f"( {pprint_fm(a[1])} -> {pprint_fm(a[2])})"
    if a[0] == "-":
        return f"(- {pprint_fm(a[1])})"
    else:
        return a

def pprint_pf(a):
    print(pprint_fm(a[1]))

A = "A"
pf = []
pf.append(axiom1(A, A))
pf.append(axiom1(A, ("->", A, A)))
pf.append(axiom2(A, ("->", A, A), A))
pf.append(modus(pf[-2], pf[-1]))
pf.append(modus(pf[0], pf[-1]))

import pprint
pprint.pprint(pf)
for x in pf:
    pprint_fm(x)

# A super simple "tactic"
rev_modus = lambda ab, a: modus(a, ab)
def a_to_a(A):
    pf = []
    pf.append(axiom1(A, A))
    pf.append(axiom1(A, ("->", A, A)))
    pf.append(axiom2(A, ("->", A, A), A))
    pf.append(modus(pf[-2], pf[-1]))
    pf.append(modus(pf[0], pf[-1]))
    return pf[-1]

# not having variable really stinks.
```

<https://us.metamath.org/mpeuni/idALT.html> Metamath is a good example of this stuff.

## Proof server

An amusing idea related to the crypto signing is to have a proof server that anyway could access over an api. Python of course makes making an http server easy. This makes it more clear where the kernel is since it is in an entirely separate computer rather than being in process.

It also could make a for a fun game.

This opens up the question of how you could make a proof system hardened against cyber security attacks like buffer overflows, etc etc. A truly antagonistic adversary. There are always layers of trust even beneath the most trusted axiomatic foundations. Can you defend a proof kernel against a trusting trust attack?

```python
import hashlib


SECRET = "no_underwear"
def validate(th):
    hsh = th[0]
    formula = th[1]
    return hash(self.SECRET, formula) == hsh
def modus(self, th1, th2): # A => B and A gives B
    if not validate(th1) or not validate(th2):
        return None
    match th1[1], th2[1]:
        case ("=>", A,  B), A1:
            if A == A1:
                return (hash(self.SECRET, B), B)

# server receivers a theorem and checks it's validity
from flask import Flask, request, jsonify

app = Flask(__name__)
@app.route('/modus', methods=['POST'])
def modus_api():
    received_object = request.json
    return jsonify(modus(request.A, request.B))

if __name__ == "__main__":
    app.run(debug=True, port=9999)

```

```python
import requests

def send_object_to_server(obj):
    response = requests.post("http://127.0.0.1:9999/send", json=obj)
    return response.json()


def proof_script():

obj_to_send = {"hello": "world"}
response = send_object_to_server(obj_to_send)
print("Received response:", response)

```

## Blah Blah

Attempting to use chatgpt to write this post. Not that useful <https://chat.openai.com/share/1bf6bb1a-e224-4d53-a748-b2291994fbe6>

Building an interactive proof kernel is one of those things that mayb you don't realize you can do. Like an operating system or a browser, it's just another kind of program.

Most resources out there describe how to do this in a functional language (OCaml, Haskell, etc), but I think it's useful to do it in a language like python. The extra impedance mismatch of bumbling through a language that is unfamiliar and a topic that is also unfamiliar can be too intimidating.

The basic approach of many proof systems is to try and build a small trusted kernel through which all your steps pass through. Then a much larger body of untrusted helper functionality can exist around this without compromising the integrity of the system.

Properties/features of the underlying language can help achieve this separation of concerns. In the LCF approach, the mechanism of abstract types is used to control valid proofs. `Theorem` is an abstract type, probably basically a wrapper around a formula abstract syntax tree. Just like how you can't screw with the internals of some dictiontary data structure, you can't screw around with the inside of `Theorem`. You can however request a copy of the information inside to play around with.

Python is a pretty uncontrolled language. It is hard to _really really_ enforce any kind of discipline because there is mutability and introspection everywhere. This distinction is however a matter of degree. Every language has some kind of escape hatch. OCaml has `Obj.magic` and Haskell has `unsafeCoerce`. The point is to protect you from accidental unsoundness, not antagonistic attacks. That requires a different design.

John Harrison's Handbook of Practical Logic and Automated Reasoning has some excellent examples of the LCF approach

# Hidden Constructor

```python
from dataclasses import dataclass

Formula = str
Formula = set[set[int]] #cnf
Proof = list[str]

@dataclass(frozen=True)
class Theorem():
    formula: Formula
    proof: Proof

def resolve(t1,t2, i):
    assert i in t1
    assert -i in t2
    return Theorem(t1.union(t2))
```

# Central Authority

# Crypto Signing

# Proof Objects

We so far have counted on trustability in the process. We can also just record a trace of the proof process (the sequence of calls with what parameters). We can then check this trace if we record it at a later time.

It is this method where the famed Curry Howard correspondence comes into play. These traces/proof trees can be naturally represented as lambda calculus terms for some logics.
