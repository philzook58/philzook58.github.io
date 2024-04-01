---
data: 2024-04-01
title: Resolution Proving I
---

Not an april fools post.

One of my favorite projects is [PyRes](https://github.com/eprover/PyRes). It's a pedagogical first order prover in python. This blog post is mostly a compression and repetition of some of what is found there.

[Resolution](https://en.wikipedia.org/wiki/Resolution_(logic)) theorem proving is an old and popular style of theorem prover.

It basically takes in a pile of syntactic facts and smashes them together producing new facts. That sentence also describe the entirety of "logic".

First we need a basic term datatype. I kind of like using python dataclasses. This is the analog of a algebraic datatype `type term = Var of string | Fn of string * term list`. Variables can be used to represent an implicit "forall" character of a proven or asserted fact/clause.
They sometimes play a dual role as the things searched for in a query (when inside a prolog query for example). These are quite different uses/modalities and it can be good to be aware of this.

```python
from dataclasses import dataclass
from typing import Any
@dataclass(frozen=True)
class Term():
    pass
@dataclass(frozen=True)
class Fn(Term):
    name: str
    args: tuple[Any, ...] = ()
    def __repr__(self):
        if len(self.args) == 0:
            return self.name
        return f"{self.name}({', '.join(map(repr, self.args))})"
    
@dataclass(frozen=True)
class Var(Term):
    name: str
    def __repr__(self):
        return "?" + self.name
```

We may want to substitute in terms for variables. A substitution dictionary is a mapping from variable names to terms.

```python
def subst(t : Term, s : dict[str,Term]):
    match t:
        case Var(name):
            return s.get(name, t)
        case Fn(name, args):
            return Fn(name, [subst(arg, s) for arg in args])
        case _:
            raise ValueError("Invalid term")
```

[Unification](https://en.wikipedia.org/wiki/Unification_(computer_science)) is like two way pattern matching. It can also be thought of as a most basic form of equation solving.

Unification is tricky, as are many things having to do with variables so I try to follow some reference pretty closely.

The basic idea is pretty simple. You take two terms. If they are concrete constants, they better match. If so, recurse on the arguments.
If one is a variable, you have sort of solved that equation. Substitute that expression for that variable everywhere.
The [occurs check](https://en.wikipedia.org/wiki/Occurs_check) is an interesting subtlety. It is sort of making sure you don't allow equations like `X = cons(1, X)` to be solvable. Unless you realize you're up to something weird, it is probably what you want.

```python
def occurs_check(x : Var, t : Term):
    if isinstance(t, Var):
        return x.name == t.name
    elif isinstance(t, Fn):
        return any(occurs_check(x, arg) for arg in t.args)
    else:
        raise ValueError("Invalid term")

# https://github.com/eprover/PyRes/blob/master/unification.py
def mgu(t1:Term, t2:Term):
    l1 = [t1]
    l2 = [t2]
    s = {}
    while len(l1) != 0:
        t1 = l1.pop()
        t2 = l2.pop()
        if isinstance(t1, Var):
            if t1 == t2:
                continue
            if occurs_check(t1, t2):
                return None
            l1 = [subst(t, {t1.name:t2}) for t in l1]
            l2 = [subst(t, {t1.name:t2}) for t in l2]
            s[t1.name] = t2
        elif isinstance(t2, Var):
            if occurs_check(t2, t1):
                return None
            l1 = [subst(t, {t2.name:t1}) for t in l1]
            l2 = [subst(t, {t2.name:t1}) for t in l2]
            s[t2.name] = t1
        elif isinstance(t1, Fn) and isinstance(t2, Fn):
            if t1.name != t2.name or len(t1.args) != len(t2.args):
                return None
            l1.extend(t1.args)
            l2.extend(t2.args)
        else:
            raise ValueError("Invalid term")
    return s

def test():
    x,y = Var("x"), Var("y")
    def f(x):
        return Fn("f", (x,))
    def g(x):
        return Fn("g", (x,))
    print(f"{mgu(f(x), g(x))=}")
    print(f"{mgu(f(x), f(y))=}")
    print(f"{mgu(f(x), f(x))=}")
    print(f"{mgu(f(x), f(f(x)))=}")
    print(f"{mgu(f(x), f(f(y)))=}")
test()
```

    mgu(f(x), g(x))=None
    mgu(f(x), f(y))={'x': ?y}
    mgu(f(x), f(x))={}
    mgu(f(x), f(f(x)))=None
    mgu(f(x), f(f(y)))={'x': f(?y)}

A clause is a set of negative and positive literals. Negative literals are hypotheses and positive literals are the possible conclusions.
A clause is the statement that `not neg[0] or not neg[1] or ... or pos[0] or pos[1] or pos[2] or ...` is true. It can also be thought of as `(neg[0] and neg[1] and neg[2] ...) => (pos[0] or pos[1] or ...)` or `{neg_i} |- {pos_i}`

```python
@dataclass(frozen=True)
class Clause(): # Sequent
    neg: tuple[Term, ...] # frozenset? # hyps
    pos: tuple[Term, ...] # concs
    def __repr__(self):
        return f"{self.neg} ⊢ {self.pos}"
```

```python
def edge(x,y):
    return Fn("edge", (x,y))
def path(x,y):
    return Fn("path", (x,y))
a,b,c,d = Fn("a"), Fn("b"), Fn("c"), Fn("d")
facts = [Clause((), (edge(a,b),)), Clause((), (edge(b,c),)), Clause((), (edge(c,d),))]


X,Y,Z = Var("X"), Var("Y"), Var("Z")
path_base = Clause([edge(X,Y)], [path(X,Y)])
path_trans = Clause([path(X,Y), edge(Y,Z)], [path(X,Z)])
clauses = [path_base,path_trans]
```

[Resolution](https://en.wikipedia.org/wiki/Resolution_(logic)) is the analog of modus ponens or the cut rule. We take two clauses and see if we can make a positive literal from one to match (unify) a negative from the second.

```python
def computeResolvents(clause1: Clause, clause2: Clause):
    res = []
    # freshen vars?
    #fv = freevars(clause2)
    #clause1 = freshen_clause(clause1)
    for lit1 in clause1.pos:
        for lit2 in clause2.neg:
            s = mgu(lit1,lit2)
            if s == None:
                continue
            new_clause = Clause(tuple(subst(lit,s) for lit in clause1.neg) + tuple(subst(lit,s) for lit in clause2.neg if lit != lit2), tuple(subst(lit,s) for lit in clause1.pos if lit != lit1) + tuple(subst(lit,s) for lit in clause2.pos))
            res.append(new_clause)
    return res

def test():
    # this is a datalog-esque loop
    for fact in facts:
        for clause in clauses:
            resolvents = computeResolvents(fact, clause)
            print(f"{fact=}, {clause=}, {resolvents=}") 
test()

```

    fact=() ⊢ (edge(a, b),), clause=[edge(?X, ?Y)] ⊢ [path(?X, ?Y)], resolvents=[() ⊢ (path(a, b),)]
    fact=() ⊢ (edge(a, b),), clause=[path(?X, ?Y), edge(?Y, ?Z)] ⊢ [path(?X, ?Z)], resolvents=[(path(?X, a),) ⊢ (path(?X, b),)]
    fact=() ⊢ (edge(b, c),), clause=[edge(?X, ?Y)] ⊢ [path(?X, ?Y)], resolvents=[() ⊢ (path(b, c),)]
    fact=() ⊢ (edge(b, c),), clause=[path(?X, ?Y), edge(?Y, ?Z)] ⊢ [path(?X, ?Z)], resolvents=[(path(?X, b),) ⊢ (path(?X, c),)]
    fact=() ⊢ (edge(c, d),), clause=[edge(?X, ?Y)] ⊢ [path(?X, ?Y)], resolvents=[() ⊢ (path(c, d),)]
    fact=() ⊢ (edge(c, d),), clause=[path(?X, ?Y), edge(?Y, ?Z)] ⊢ [path(?X, ?Z)], resolvents=[(path(?X, c),) ⊢ (path(?X, d),)]

Fully naive inference is taking all your clauses and just smashing them together to infer new clauses. For the `path` clauses, we get new multi edge step theorems. I freshen the variables in one part of the pair in kind of a hacky way. It isn't _wrong_ to insufficiently freshen, you just won't get the most general possible resolution. You have accidental equality constraints between the variables of the two clauses.

```python
def freshen(t):
    # this is both ugly and wrong. Whatever
    if isinstance(t, Var):
        return Var(t.name + "_")
    elif isinstance(t, Fn):
        return Fn(t.name, tuple(freshen(arg) for arg in t.args))
    else:
        raise ValueError("Invalid term")
def freshen_clause(c):
    return Clause(tuple(map(freshen,c.neg)), tuple(map(freshen, c.pos)))

def naive_infer(clauses):
    res = []
    for c1 in clauses:
        for c2 in clauses:
            c2 = freshen_clause(c2)
            print(c2)
            # if c1 != c2: # an optimization
            resolvents = computeResolvents(c1, c2)
            res.extend(computeResolvents(c1, c2))
    return res

naive_infer(clauses)
```

    (edge(?X_, ?Y_),) ⊢ (path(?X_, ?Y_),)
    (path(?X_, ?Y_), edge(?Y_, ?Z_)) ⊢ (path(?X_, ?Z_),)
    (edge(?X_, ?Y_),) ⊢ (path(?X_, ?Y_),)
    (path(?X_, ?Y_), edge(?Y_, ?Z_)) ⊢ (path(?X_, ?Z_),)





    [(edge(?X_, ?Y_), edge(?Y_, ?Z_)) ⊢ (path(?X_, ?Z_),),
     (path(?X_, ?Y), edge(?Y, ?Y_), edge(?Y_, ?Z_)) ⊢ (path(?X_, ?Z_),)]

# Bits and Bobbles

I ran out of steam before getting to anything too juicy today. But some comments

- The given clause algorithm is a semi naive strategy for expanding your inferences.
- Particular strategies of using resolution can give you datalog or prolog. Hypothetical/contextual datalog is implementable as a strategy. Other named strategies: hyper resolution . UR / unit resolution. set of support
- The factoring rule is necessary to get a complete resolution prover. It compresses the literals inside a single clause.
- I don't really think of resolution as a first order logic method.
- Alpha renaming / variants. Variable names don't really matter and everything should be invariant to changing them.
- term indexing. Discrimination tries, path indexes, fingerprinting
- Subsumption. If you have `foo(X)` as a fact (implicitly `forall x, foo(x)`), it is stronger than any `foo(a)`. The `foo(a)` fact is redundant. When you derive a new fact, you should check if it is redundant with respect to already processed facts.
- Paramodulation. Treat equality special. Use positive equalityt facts to rewrite inside other clauses. Superposition is taking term orderings into account. A contextual generalization of knuth bendix completion.
- queries. We can make a special term that the prover loop is looking for stuff that unifies with. I am interetsed in non refutation theorem proving applications
- the occurs check. On the other hand, note that `X = sin(X)` is not intuitively a problem (`X = pi n`).
- nominal unification / lambda / miller
- How do you implement unification efficiently? Interesting stuff on wiki page.

Good reading: Handbook of automated reasoning. Harrison's automated reasoning Handbook. PyRes paper

I'll start chucking snippets of functionality from blog posts into knuckledragger

Natural notion of  <= isa subsumes. == is "alpha equiv to".
hash of every var should be the same.
Term orderings also have a natural <=

alpha equiv is basically mgu with var permutations instead of substitution
nominal

If everything was ground it's a bit simpler. This is the case for propositional logic

```
{A} |- {B}   {B} |- {C}
-------------------------
        {A} |- {C}
```

When we have variables, we figure out if two literals are "equal" by seeing if they unify. Then we need to apply that unification everywhere.

```python


def freevars(t):
    if isinstance(t, Var):
        return {t.name}
    elif isinstance(t, Fn):
        return set().union(*map(freevars, t.args))
    else:
        raise ValueError("Invalid term")

def freshen(t):
    # this is both ugly and wrong.
    if isinstance(t, Var):
        return Var(t.name + "_")
    elif isinstance(t, Fn):
        return Fn(t.name, tuple(freshen(arg) for arg in t.args))
    else:
        raise ValueError("Invalid term")
def freshen_clause(c):
    return Clause(map(freshen,c.neg), map(freshen, c.pos))
```

Factoring feels kind of like a structural rule like weakening.

```python
#https://github.com/eprover/PyRes/blob/master/resolution.py
def computePosFactors(clause):
    res = []
    for lit1 in clause.pos:
        for lit2 in clause.pos: # redundant.
            s = mgu(lit1,lit2)
            if s == None:
                continue
            new_clause = Clause(tuple(subst(lit,s) for lit in clause.neg), tuple(subst(lit,s) for lit in clause.pos if lit != lit1))
            res.append(new_clause)
    return res

def computeNegFactors(clause):
    res = []
    for lit1 in clause.neg:
        for lit2 in clause.neg: # redundant.
            s = mgu(lit1,lit2)
            if s == None:
                continue
            new_clause = Clause(tuple(subst(lit,s) for lit in clause.neg if lit != lit1), tuple(subst(lit,s) for lit in clause.pos))
            res.append(new_clause)
    return res
```

The given clause algorithm is similar to semi naive evaluation.
If starts with a set of unprocessed clauses and processes them one by one by finding all possible resolutions against the processed clauses. One tries to prune away redundancies.

```python

def prove(clauses):
    unprocessed = set(clauses)
    processed = set()
    while len(unprocessed) >= 0:
        new = []
        clause = unprocessed.pop()
        new.extend(computeFactors(clause))
        for clause2 in processed:
            new.extend(computeResolvents(clause, clause2))
        processed.add(clause)
        delta = processed.difference(new)
        unprocessed.update(delta)
```

```python
def alpha_eq(self, other, perm):
    match self:
        case Var(x), Var(y):
            if x in perm:
                return perm[x] == y
            elif y in perm_inv:
                return perm_inv[y] == x
            else:
                perm.add(x, y)

def __eq__(self,other, perm={}):
    alpha_eq(self, other, {})
```

## First order logic

Resolution is presented as a classical first order logic prover, but I don't think it really is. I think it can be thought of as fairly generic principles of what it means to have inference rules.
A clause is quite a bit / identical to a [sequent](https://en.wikipedia.org/wiki/Sequent). The negative literals are the things before the turnstile `|-` and the positive literals are the things after. Resolution is then seen as an instance of the famed [cut rule](https://en.wikipedia.org/wiki/Cut_rule) which is in turn something like [modus ponens](https://en.wikipedia.org/wiki/Modus_ponens)
Logic programming has a similar confusion. `:-` is best thought of as the horizontal inference line rather than $\rightarrow$. See The Logic of Logic Programming <https://arxiv.org/abs/2304.13430> and Nadathur and Miller <https://www.amazon.com/Programming-Higher-Order-Logic-Dale-Miller/dp/052187940X>

[First order logic](https://en.wikipedia.org/wiki/First-order_logic) has `and or implies not` but also predicates/relationships like `parent(adam, abel)` or `border(us, canada)`  and `forall` $\forall$  `exists` $\exists$ quantifiers. It's a pretty rich system capable of expressing lots of logical ideas about graphs, geometry, groups, sets, and is fairly amenable to automation (more so seemingly than sophisticated systems). It is conversely seen as fairly inexpressive. You may need to bolt on some pretty alarming axioms (like the axiom of specification) to get FOL to actually work for you as a foundation of mathematics.

So the story goes, you can convert a pile of first order logic statements to [conjunctive normal form](https://en.wikipedia.org/wiki/Conjunctive_normal_form) (a giant AND of ORs). `A -> B` is turned into `~A \/ B` and etc. Probably most interestingly, quantifiers are removed via [skolemization](https://en.wikipedia.org/wiki/Skolem_normal_form). A statement `\forall x \exists y, parent(y,x)` kind of is saying a similar thing to `forall x, parent(father(x), x)`. Note that similarly I could have done `forall x, parent(mother(x), x)` or `forall x, parent(someparent(x), x)` (really I should make a fresh function symbol and then prove that the fresh function symbvol is the same as some other defined notion). Operationally, you can push existentials through universals if you turn them into function symbols  depending on the thingsy ou pushed them though. Often these functions have some reasonable interpretation in terms of the things you're trying to model.

Skolemization producers new formula that are equisatisfiable to the old ones. They are logically equivalent in the sense of being able to prove the skolemized formula from the old one, because the old one doesn't say that specifically your new invented symbols are the ones with the right properties. This all may be intertwinerd with axiom of choice.

Becauswe we've pushed all the existentials to the front, now the formula only has top level quantifiers instead of nested complicated ones. We can strip off the explicit quantifier symbol  and replace it with a notion of variables vs constants/function symbols.

This was all quite hand wavy. See The handbook of automated reasoning or harrison's handbook for more.

Anyway, eventually you get to CNF. Now the basic inference steps are resolution and factoring (which is sort of resolving a clause on itself). These are complete

It's kind of curious the distinction we make between FOL and other things. We think of FOL as a kind of logical framework in which we can talk about different mathematical ideas in a common infrastructure. But also FOL is kind of a very abstracted set theory on it's own. In metamath for example, first order logic is not that special compared to other things. Predicates are sort of like the sets of things they are provable on. Set theory comes about when we enable ourselves to reflect (comprehension) predicates into objects that we can manipulate and talk about.

To start a mini pyres

idea: what about an isabelle style [] => []

```python
# fingerprinting https://link.springer.com/chapter/10.1007/978-3-642-31365-3_37

def symcount(t:Term):
    pass
def varcount():
    pass

```

```python
# The proof recording system
proof_db = []
def axiom(s):
    proof_db.append((s, "axiom"))
    return len(proof_db)
def formula(s):
    return proof_db[s][0]
def factor(c):
    f = compute_factor(formula(c))
    proof_db.append((f, ("factor",c)))
    return len(proof_db)
def resolve(c1,c2):
    r = compute_resolvent(formula(c1), formula(c2))
    proof_db.append((r, ("resolve",c1,c2)))
    return len(proof_db)






```

```python
# prolog using these pieces
class Goal():
    def __init__(self, goal_clause):
        self.goal = goal_clause
        self.goal = infer([goal], goal)  # we can start with refl.

    def rule(self, clause):
        # hmm. I do need to record?
        compute_resolvent(self.goal, clause)

    def erule(self, clause):
        pass
```

```python
    for i, lit1 in enumerate(clause.literals):
        for lit2 in clause.literals[i:]:
            if lit1.neg == lit2.neg:
                continue
            s = mgu(lit1,lit2)
            if s == None:
                continue
            new_clause = [Literal(lit.neg, subst(lit.term,s)) for lit in clause.literals if lit != lit1 and lit != lit2]
            res.append(Clause(new_clause))
```

    ---------------------------------------------------------------------------

    NameError                                 Traceback (most recent call last)

    Cell In[15], line 1
    ----> 1 for i, lit1 in enumerate(clause.literals):
          2     for lit2 in clause.literals[i:]:
          3         if lit1.neg == lit2.neg:


    NameError: name 'clause' is not defined

metitarski. What if I included arb

```python
@dataclass(frozen=True)
class Fact():
    ctx : tuple[Term, ...]
    fact: Term
class Rule():


def hypo_datalog():
    rules = []
    facts = []
    while True:
        for rule in rules:
            for fact in facts:
                compute_resolvent(rule,fact)
```

```python
@dataclass(frozen=True)
class Rule():
    head: Term
    body: tuple[Term, ...]

def prolog():
    rules = []
    for rule in rules:
        s = compute_resolvent(rule.head, goal[-1])
        goal.extend[subst(rule.body, s)]

# but how do I make the "strategy" nature self manifest

```

```python
import re
toks = [
    (":-", "IMPLIES"),
    ("\\.", "DOT"),
    ("\\(", "LPAREN"),
    ("\\)", "RPAREN"),
    ("[a-zA-Z]+", "FN"),
    ("[A-Z][a-zA-Z]*", "VAR"),
    (",", "COMMA"),
    ("\\s+", "SPACE")
]
tokpat = re.compile("|".join(f"(?P<{name}>{pat})" for pat, name in toks))
def parse_rule():

def parse_term(s):
    match s.lastgroup:
        case "COMMA":
        
        

        case "RPAREN":
            return Fn(name, args)




lark_grammar = """
prog : rule*
rule : term ":-" term ("," term )* "." | term "."
term = var | fn
fn = IDENT "(" term ("," term)* ")"
var = VAR

hyprule : "{" term* "}" "|-" term :- 

"""



```

      Cell In[1], line 15
        case "COMMA"
                    ^
    SyntaxError: expected ':'

```python
def datalog():
    rules = []
    facts = []
```

Literal selection
Ordered resolution

```python
"""
@dataclass
class Literal():
    neg: bool
    term:Term

@dataclass
class Clause():
    literals: list[Literal]
"""
```

```python
! source ~/.bashrc
```

```python
import os
from openai import OpenAI

client = OpenAI(
    # This is the default and can be omitted
    api_key=os.environ.get("OPENAI_API_KEY"),
)

chat_completion = client.chat.completions.create(
    messages=[
        {
            "role": "user",
            "content": "Say this is a test",
        }
    ],
    model="gpt-3.5-turbo",
)
chat_completion
```

```python
dir(chat_completion)
```

```python
chat_completion.choices[0].message.content
chat_completion.json()

```
