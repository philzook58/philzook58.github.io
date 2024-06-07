---
title: Ground Knuth Bendix Ordering is Basically Size with Tie Breaking
date: 2024-05-27
---

A natural and interesting topic is the idea of a Term ordering.

[Terms](https://en.wikipedia.org/wiki/Term_(logic)) are syntax trees that we can throw different features into. An example of a term may be an arithmetic expression like

```python
# (2 * 42) + 3
("+", [("*", [("lit", 2), ("lit",42)]), ("lit", 3)])
```

    ('+', [('*', [('lit', 2), ('lit', 42)]), ('lit', 3)])

Why do we want to compare terms? Well, having an ordering on terms enables the use of datastructures like balanced search trees.

But also perhaps more crucially, it is a mathematical way of describing the notion of "simpler".

The most basic and obvious notion of simpler is to count the number of nodes in the term. Its size.

For some term rewriting simplifiers we may write, we can know thew thing isn't going to loop (not terminate) if it always makes a little progress into a strictly simpler term. Presumably any reasonable order does not an infinite chain of simpler terms, so the rewriter has to stop eventually. We get rid of extra `0`, constant propagate, fuse out things like `-(-x) -> x` or `x - x -> 0`. All of these rules make smaller terms so we can't loop forever.

If we want to show that a particular term rewriting system has this nontermination property, we need to find a term ordering. This term ordering has to comply with the fact that the left and right hand side of rules contain pattern variables, which may stand in for any term. This puts pretty strong and complicated constraints on the term ordering.

I find the definition of the knuth bendix ordering pretty confusing. And yet, when you consider the ground case, it all becomes much simpler and more obvious. This is a general rule of thumb for understanding many techniques in automated reasoning. The ground stuff is a subcase and much easer. Here is the definition from "Term Rewriting and All That"

![knuth bendix ordering](/assets/traat/kbo.png)

1. KBO1 says that if the term sizes are different, the bigger one is larger.
2. KBO2 is the tiebreaking rules for equal sized terms. 2a is not relevant to the ground case. 2b says to break ties using the head symbol. 2c says if the heads are equal to recurse lexicographically (compare in order) into the arguments.

Pretty straightforward actually. Compare by size. Tie break by head symbol and then recurse into arguments.

Here I implement this over z3 asts.

```python
from enum import Enum
from z3 import *
Order = Enum("Order", ["LT", "EQ", "NGE", "GT"])
def kbo(t, r):
    pass

def size(t:ExprRef):
    return 1 + sum(size(x) for x in t.children())
def ground_kbo(t1, t2):
    if t1.eq(t2): # optimization
        return Order.EQ
    s1 = size(t1)
    s2 = size(t2)
    if s1 < s2:
        return Order.LT
    elif s1 > s2:
        return Order.GT
    else:
        if t1.num_args() < t1.num_args():
            return Order.LT
        elif t2.num_args() > t2.num_args():
            return Order.GT
        n1, n2 = t1.decl().name(), t2.decl().name()
        if n1 < n2:
            return Order.LT
        elif n1 > n2:
            return Order.GT
        else:
            for x,y in zip(t1.children(), t2.children()):
                o = ground_kbo(x,y)
                if o != Order.EQ:
                    return o
            assert False, "unreachable"


x,y,z = Ints("x y z")
assert ground_kbo(x,x) == Order.EQ
assert ground_kbo(x,y) == Order.LT
assert ground_kbo(y,y) == Order.EQ
assert ground_kbo(x + z, x + y) == Order.GT
assert ground_kbo((x + x) + x, x + (x + x)) == Order.GT
assert ground_kbo((z + z) + z, x * x) == Order.GT
```

Why is this interesting? Well, one reason is that it let's you build an egraph. Completion over ground equations is the same thing as congruence closure. I think this road leads to extensions of the egraph that include lambdas (using ground versions of higher order kbo) and principled built in destructive rewriting (under what conditions does adding ground equations to a "good" non ground rewrite system retain the good properties?). I'm coming back around to these ideas. I got stumped and side tracked last time, but they still seem good.

- <https://www.philipzucker.com/egraph-ground-rewrite/>
- <https://www.philipzucker.com/ground-rewrite-2/>
<https://pldi24.sigplan.org/details/egraphs-2024-papers/13/E-graphs-and-Automated-Reasoning-Looking-back-to-look-forward> Giving a talk next month.

# Bits and Bobbles

Completion for ground equations is guaranteed to terminate because you only produce terms smaller than the largest one you started with. Eventually you run out of terms.
Critical pairs for ground terms is merely finding a one term as a subterm in another.

Working over z3 asts I think is a good idea. It let's me bop in and out of z3 and complies with thew current direction I'm going in knuckledragger. Z3 is a vast raft of functionality.

<https://www.cs.miami.edu/home/geoff/Courses/TPTPSYS/FirstOrder/SyntacticRefinements.shtml> knuht bendix is not ground completable?
<https://www.cs.unm.edu/~mccune/prover9/manual/2009-11A/term-order.html> prover 9 term orderings

 <https://www.ncbi.nlm.nih.gov/pmc/articles/PMC7324232/> A Knuth-Bendix-Like Ordering for Orienting Combinator Equations

 lambda free kbo <https://www.isa-afp.org/browser_info/current/AFP/Lambda_Free_KBOs/document.pdf>
 <https://arxiv.org/abs/2005.02094>

## The default "tuple" ordering on terms

Python's default for tuples is to compare them lexicographically. This corresponds to first comparing head symbols, then recursively comparing the arguments.
This ordering is total.
It isn't great in that it isn't a simplification ordering. A subterm can be larger than the term itself. Ok, why is that a problem?
Well, it's more obviously a problem if terms have variables in them, since to stay consistent we need to be able to substitute in any possible term. If we stick to ground terms though, this is not such a problem.
It does run contrary to the idea that "size" is a good measure of simplicity.

An arbitrary (well founded) ordering is basically ok on ground terms because you don't care as much about things like substitution. The typical union find exploits this to find an arbitrary online ordering that keeps the union find kind of flat.

## Path Ordering

Harrison points out that LPO is basically constructed to have the substitution property. That is why we do a recursive check first.

<https://en.wikipedia.org/wiki/Path_ordering_(term_rewriting)>

```python
def ground_lpo(s,t, vars=[]):
    if t in vars: #LPO1
        return t in s
    
    f = s.decl().name()
    g = t.decl().name()
    return any(ground_lpo(si, t) for si in s.children()) or \ #LPO2a
    all(ground_lpo(s, ti) for ti in t.children()) and \ #
    (f > g or # LPO2b no. I need to use Order.EQ Order.LT. This is close though. Oh well.
    f == g and any(ground_lpo(si,ti) for si, ti in zip(s.children(), t.children()))) #LPO2c
```

Ordering modulo theories. Like Hashing modulo theories, if you want to use an AVL tree to store some things that respect some equations, how do you do it? Set orderings and multiset orderings. Again can basically sort them and then use a lexicographic ordering.

How do you order alpha equiv terms? trvaversal order labelling or "tree maps" a la co de bruijn / hash cons modulo alpha.

In this direction lies alpha egraphs. nominal matching.

<https://link.springer.com/content/pdf/10.1007/3-540-17220-3_4.pdf> How to choose the weights in the Knuth Bendix ordering -- ursula martin

<https://academic.oup.com/comjnl/article/34/1/2/427931> An Introduction to Knuth–Bendix Completion Ajj dick

<https://link.springer.com/article/10.1007/s10817-006-9031-4>  Things to Know when Implementing KBO

We have a notion that simplifiers must terminate because terms get simpler until they can't

"size" is a basic notion of complexity.

In order to guarantee a rule with variables gets smaller, we can count the number of symbols in it. The number of pattern variables has to be getting smaller, or else the thing is getting bigger.

`(X + 0) -> X` makes the term simpler

`foo(bar(1,2,3,4,5,6,X)) -> biz(X,X)` is not definitely a simplification, because X might be huge. In a realistic situation, we might want to guard this rule by `size(X) < 3` or something.

A slight extension is to give the symbols in the term weight.

Another example is associating to the right. X + (Y + Z) -> (X + Y) + Z. This also obviously terminates. We can give lexicographic preference to left subtrees.

Another example is getting flatter. The height is descreasing.

distrbutivity is another common case. x*(y + z) -> x*y + x*z. This is getting bigger *and* duplicating x. That's a big nono for most term orderings. But clearly foiling is terminating.

A different system that is obviously terminating is stratified macro expansion. Macros can refer to previously defined macros. The terms however, may get very large and be increasing in size.
f(X) -> bar(X,X) is not an issue.
Cycles in the dependency graph

We don't expect to be able to have a total ordering on terms with variables in them. But we do want our definition to have a well defined

A primitive system that is obviously terminating are systems of the form `f(x,y,z,...) -> z` This is a view on the homeomorphic embedding relation.

right ground systems

Many functional programs are "obviously" terminating even if we don't think of them in these terms

Negation normal form pushing

What about naive breadth first search:
Separate into confluent terminating rules
and naughty rules. (maude makes this disctinction but do so dynamically)

Hash cons only things that are normalized with respect to current rules.
run twee for a bit, extract oriented rules, confluence them (?)
Use the others for search.

TRS/SK90 Joachim Steinbach, Ulrich Kühler: Check your Ordering - termination proofs and open Problems, Technical Report SR-90-25, Universität Kaiserslautern, 1990.
TRS/D33 Nachum Dershowitz: 33 Examples of Termination, 1995 Proc. French Spring School of Theoretical Computer Science, LNCS 909, <http://www.math.tau.ac.il/~nachumd/papers/printemp-print.pdf>
TRS/AG01 Thomas Arts, Jürgen Giesl: Termination of term rewriting using dependency pairs, 2000, <http://dblp.uni-trier.de/rec/bibtex/journals/tcs/ArtsG00> <http://verify.rwth-aachen.de/giesl/papers/ibn-97-46.ps>
SRS/Zantema 128 string rewriting termination problems collected by Hans Zantema (2004?). They include (as z027 .. z064) a set of one-rule termination problems by Alfons Geser (Habilitationsschrift, Tübingen, 2001) and possibly Winfried Kurth (Dissertation, Clausthal, 1990)

disjunctive normal form example. Makes term bigger.

Extraction Cost is Knuth Bendix Ordering Weights

consider ground extraction

elpi knuth bendix
<https://www.cl.cam.ac.uk/~jrh13/atp/> harrison's code

Knuth bendix + grobner
Can we do it? It'd be cool <https://www3.risc.jku.at/publications/download/risc_3528/paper_48.pdf> Knuth-bendix procedure and buchbergher - a synthesis

naive rewriting search engine. Keep score.
Greedy.
Then
Expansive

import swipy
import requests
r = requests.get('<https://www.metalevel.at/trs/trs.pl>')

swipy.load_module(r.body)

`pip install janus_swi`

```python
%%file /tmp/trs.pl
% based on markus triska's trs
:- op(800, xfx, ==>).
step([L==>R|Rs], T0, T) :-
        (   subsumes_term(L, T0) ->
            copy_term(L-R, T0-T)
        ;   step(Rs, T0, T)
        ).

normal_form(Rs, T0, T) :-
        (   var(T0) -> T = T0
        ;   T0 =.. [F|Args0],
            maplist(normal_form(Rs), Args0, Args1),
            T1 =.. [F|Args1],
            (   step(Rs, T1, T2) ->
                normal_form(Rs, T2, T)
            ;   T = T1
            )
        ).

term_to_list(T, L) :-
        (   var(T) -> L = [T]
        ;   T =.. [F|Args],
            maplist(term_to_list, Args, ArgsL),
            L = [F|ArgsL]
        ).
```

    Overwriting /tmp/trs.pl

% convert prolog term to lists of lists

```python
# https://www.swi-prolog.org/pldoc/doc_for?object=section(%27packages/janus.html%27)
import janus_swi as janus
janus.consult("/tmp/trs.pl")
ans = janus.query_once("normal_form([f(x) ==> g(x)], f(x), _Res), term_to_list(_Res,Res).")
ans['Res']
```

    ['g', ['x']]

```python

```

<https://lpcic.github.io/coq-elpi/tutorial_elpi_lang.html>
<https://github.com/LPCIC/elpi/blob/master/src/builtin.elpi>

```python
%%file /tmp/trs.elpi
kind term type.

%infixr ==> 50.
%type (==>)   tye -> tye -> tye.
type fn string -> list term -> term.
type lam : (term -> term) -> term.

kind rule type.
type rule : term -> term -> rule.

pred normal : list rule,  term, term.

```

    Writing /tmp/trs.elpi

```python
! elpi -exec 'normal (fn "a" []) Ans' /tmp/trs.elpi
```

```python
class Fn():
    cost: int
    hash: int
    head: str
    args: List['Fn']


def ground_kbo(t1,t2):
    if t1.cost < t2.cost:
        return True
    elif t1.cost > t2.cost:
        return False
    elif t1.head < t2.head:
        return True
    elif t1.head > t2.head:
        return False
    else:
        for arg1, arg2 in zip(t1.args ,t2.args):
            if arg1 == arg2:
                continue
            return ground_kbo(arg1, arg2)
            
```

```python

import requests
res = requests.get("https://www.metalevel.at/trs/trs.pl")
with open("/tmp/trs.pl", "w") as f:
    f.write(res.text)
```

```python


```

    ERROR: /tmp/trs.pl:67:
    ERROR:    source_sink `library(clpz)' does not exist
    Warning: /tmp/trs.pl:67:
    Warning:    Goal (directive) failed: user:use_module(library(clpz))
    ERROR: /tmp/trs.pl:69:
    ERROR:    source_sink `library(dcgs)' does not exist
    Warning: /tmp/trs.pl:69:
    Warning:    Goal (directive) failed: user:use_module(library(dcgs))
    ERROR: /tmp/trs.pl:71:
    ERROR:    source_sink `library(iso_ext)' does not exist
    Warning: /tmp/trs.pl:71:
    Warning:    Goal (directive) failed: user:use_module(library(iso_ext))
    ERROR: /tmp/trs.pl:72:
    ERROR:    source_sink `library(format)' does not exist
    Warning: /tmp/trs.pl:72:
    Warning:    Goal (directive) failed: user:use_module(library(format))
    ERROR: /tmp/trs.pl:261:23: Syntax error: Operator expected
    ERROR: /tmp/trs.pl:269:9: Syntax error: Operator expected

```python
"""
let rec termsize tm =
  match tm with
  | Fn(f,args) -> itlist (fun t n -> termsize t + n) args 1;;
    Var x -> 1
"""
def termsize(tm):
    match tm:
        case ("Var", x):
            return 1
        case ("Fn", f, args):
            return sum(map(termsize, args)) + 1

```

```python
from dataclasses import dataclass
from typing import Tuple
class Term:
    pass
@dataclass
class Fn(Term):
    f: str
    args: Tuple[Term]

@dataclass
class Var(Term):
    name: str

def Function(fn):
    def res(*args):
        return Fn(fn, args)
    return res
def Vars(xs):
    return [Var(x) for x in xs.split()]
def Functions(fns):
    return [Function(fn) for fn in fns.split()]

import enum

# traat
# harrison
# norvig
# eli bendersky

def unify(x, y, subst):
    """Unifies term x and y with initial subst.

    Returns a subst (map of name->term) that unifies x and y, or None if
    they can't be unified. Pass subst={} if no subst are initially
    known. Note that {} means valid (but empty) subst.
    """
    if subst is None:
        return None
    elif x == y:
        return subst
    elif isinstance(x, Var):
        return unify_variable(x, y, subst)
    elif isinstance(y, Var):
        return unify_variable(y, x, subst)
    elif isinstance(x, Fn) and isinstance(y, Fn):
        if x.f != y.f or len(x.args) != len(y.args):
            return None
        else:
            for i in range(len(x.args)):
                subst = unify(x.args[i], y.args[i], subst)
            return subst
    else:
        return None

def unify_variable(v, x, subst):
    """Unifies variable v with term x, using subst.

    Returns updated subst or None on failure.
    """
    assert isinstance(v, Var)
    if v.name in subst:
        return unify(subst[v.name], x, subst)
    elif isinstance(x, Var) and x.name in subst:
        return unify(v, subst[x.name], subst)
    elif occurs_check(v, x, subst):
        return None
    else:
        # v is not yet in subst and can't simplify x. Extend subst.
        return {**subst, v.name: x}

def occurs_check(v, term, subst):
    """Does the variable v occur anywhere inside term?

    Variables in term are looked up in subst and the check is applied
    recursively.
    """
    assert isinstance(v, Var)
    if v == term:
        return True
    elif isinstance(term, Var) and term.name in subst:
        return occurs_check(v, subst[term.name], subst)
    elif isinstance(term, Fn):
        return any(occurs_check(v, arg, subst) for arg in term.args)
    else:
        return False

```

```python
assert unify(Var("x"), Var("y"), {}) == {"x": Var("y")}
assert unify(Var("x"), Var("x"), {}) == {}
assert unify(Var("x"), Fn("f", [Var("y")]), {}) == {"x": Fn("f", [Var("y")])}
assert unify(Fn("f", [Var("x")]), Fn("f", [Var("y")]), {}) == {"x": Var("y")}
assert unify(Fn("f", [Var("x")]), Fn("g", [Var("y")]), {}) == None

# hmm. This is assuming "x" and "x" in the lhs rhs are the same thing.

```

```python
def critical_pairs(f,g):
    if isinstance(f, Var) or isinstance(g, Var):
        return
    elif f.f == g.f:
        subst = unify(f,g,{})
        if subst is not None:
            yield subst, f, g
    # This is double counting
    for arg in f.args:
        yield from critical_pairs(arg, g)
    for arg in g.args:
        yield from critical_pairs(f, arg)


```

```python
list(critical_pairs(Fn("f", [Var("x")]), Fn("f", [Var("y")])))
list(critical_pairs(Fn("f", [Var("x")]), Fn("g", [Var("y")])))

```

    []

```python
def _match(e,pat,subst):
    match pat, e:
        case (Var(name), _):
            if pat.name in subst:
                if subst[pat.name] == e:
                    return subst
                else:
                    return None
            else:
                return {**subst, pat.name: e}
        case (Fn(f,args), Fn(f1,args1)):
            if f != f1 or len(args) != len(args1):
                return None
            else:
                for a1,a2 in zip(args,args1):
                    subst = _match(a1,a2,subst)
                    if subst == None:
                        return None
                return subst
        case _:
            raise ValueError(f"Can't match {pat} with {e}")

```

```python

```

```python
recexpr

```

```python
"""
let rec lexord ord l1 l2 =
  match (l1,l2) with
    (h1::t1,h2::t2) -> if ord h1 h2 then length t1 = length t2
                       else h1 = h2 & lexord ord t1 t2
  | _ -> false;;
"""
def lexord(ord, l1, l2):
    match (l1, l2):
        case ([h1,*t1], [h2, *t2]):
            if ord(h1, h2): # yeah I dunno about this. Is this a faithful rep of ord
                return len(t1) == len(t2)
            else:
                return h1 == h2 and lexord(ord,t1, t2)
        case _:
            return False

lexord([1,5], [1,4])
```

    False

```python
"""
let rec lpo_gt w s t =
  match (s,t) with
    (_,Var x) ->
        not(s = t) & mem x (fvt s)
  | (Fn(f,fargs),Fn(g,gargs)) ->
        exists (fun si -> lpo_ge w si t) fargs or
        forall (lpo_gt w s) gargs &
        (f = g & lexord (lpo_gt w) fargs gargs or
         w (f,length fargs) (g,length gargs))
  | _ -> false
"""
def lpo_gt(w,s,t):
    match (s,t):
        case (_, ("Var", x)):
            return s != t and x in fvt(s)
        case (("Fn", f, fargs), ("Fn", g, gargs)):
            return any(lpo_ge(w, si, t) for si in fargs) or \
                all(lpo_gt(w, s, si) for si in gargs) and \
                (f == g and lexord(lambda s,t: lpo_gt(w,s,t), fargs, gargs) or \
                 w(f, len(fargs), g, len(gargs)))
        case _:
            return False
```

```python
def size(t):
    match t:
        case Var(x):
            return 1
        case Fn(f, args):
            return 1 + sum(map(size, args))

def vars(t):
    match t:
        case Var(x):
            yield x
        case Fn(f, args):
            for arg in args:
                yield from vars(arg)
from collections import Counter # a multiset type

def var_comp_lte(t1,t2):
    # We don't want to have more vars on lhs than rhs
    c1 = Counter(vars(t1))
    c2 = Counter(vars(t2))
    for k in c2:
        if c1[k] < c2[k]:
            return False
    return True




    
```

```python
def kbo2a(t1,t2):
    if not isinstance(t2, Var):
        return False
    # check if t1 is iteerated functions symbol f over variable t2
    if not isinstance(t1, Fn):
        return False
    fn = t1.f
    def check(t):
        if isinstance(t, Var):
            return t == t2
        elif isinstance(t, Fn):
            return t.f == fn and len(t.args) == 1 and check(arg[0])
        else:
            raise ValueError("Not a term")
    return check(t1)

```

```python
%%file /tmp/kbo_test.p
cnf(test, axiom, f = g).
cnf(false, conjecture, true = false).

```

    Overwriting /tmp/kbo_test.p

```python
!twee /tmp/kbo_test.p --precedence g,f
```

    Here is the input problem:
      Axiom 1 (test): f = g.
      Goal 1 (false): true = false.
    
    1. g -> f
    
    Ran out of critical pairs. This means the conjecture is not true.
    Here is the final rewrite system:
      g -> f
    
    RESULT: CounterSatisfiable (the conjecture is false).

```python
!twee /tmp/kbo_test.p --precedence f,g
```

    Here is the input problem:
      Axiom 1 (test): f = g.
      Goal 1 (false): true = false.
    
    1. f -> g
    
    Ran out of critical pairs. This means the conjecture is not true.
    Here is the final rewrite system:
      f -> g
    
    RESULT: CounterSatisfiable (the conjecture is false).

```python

def kbo(t1,t2):
    if not var_comp_lte(t1,t2):
        return True
    w1 = size(t1)
    w2 = size(t2)
    if w1 > w2:
        return True
    elif w1 < w2:
        return False
    else:
         if kbo2a(t1,t2):
             return True
         elif t2.f < t1.f:   #kbo2b
            return True
        elif: #kbo2c
            
        else:
            return None
```

```bash
%%bash

dedu
```

```python
# naive

def rw(t):
    match t:
        case ("+", 0, x):
            return x
        case x: 
            return ("+", 0, x)
        case ("+", x, 0):
            return x
        case x:
            return ("+", x, 0)
        case ("+", ("-", x), x):
            return 0
        
        


def expand(t):
    for (lhs,rhs) in rules:
        yield from apply(lhs,rhs,t)
        yield from apply(rhs,lhs,t)

def prove(lhs,rhs):
    lhsseen = set(lhs)
    rhsseen = set(rhs)
    while lhsseen & rhsseen == set():
        for t in expand(lhsseen):
            if t in rhsseen:
                return True
        for t in expand(rhsseen):
            if t in lhsseen:
                return True
    



```

```python
%%file /tmp/eq.p
cnf(axiom1, axiom, a = b).
cnf(axiom2, axiom, b = c).
cnf(axiom3, axiom, c = d).
thf(p_decl, type, p : $i > $i).
thf(qdecl, type, q : $i > $i).
thf(axiom4, axiom, (^[X: $i] : X) = p).

```

    Overwriting /tmp/eq.p

can turn decl = rewrite rule.
maybe the special syntax is kind of nice. I don't like thf that much

<https://github.com/sneeuwballen/zipperposition/blob/master/examples/ind/list.zf>
<https://github.com/sneeuwballen/zipperposition/blob/master/examples/ind/tree.zf>

`val[AC] plus : term -> term -> term.`
val to declare
assert for axioms
rewrite
data definitions

```python
!zipperposition /tmp/eq.p #--dot /tmp/eq.dot --debug 10
```

    # done 4 iterations in 0.002s
    % Final clauses: 4
    Clauses:
    [a = b*]/id:0/depth:0/penalty:1/red:false
    
    [b = c*]/id:1/depth:0/penalty:1/red:false
    
    forall X0. [X0 = p X0*]/id:3/depth:0/penalty:1/red:false
    
    [b = d*]/id:4/depth:0/penalty:1/red:false
    # SZS status Satisfiable for '/tmp/eq.p'

```python
%%file /tmp/test.zf
val term : type.

data nat :=
  | z
  | s nat.

def[infix "+"] plus : nat -> nat -> nat where
  forall (X:nat). ((plus z X) = X);
  forall (X:nat). (forall (Y:nat). ((plus (s X) Y) = (s (plus X Y)))).

def[infix "-"] minus : nat -> nat -> nat where
  forall (X:nat). ((minus X z) = X);
  forall X. minus z X = z;
  forall (X:nat). (forall (Y:nat). ((minus (s X) (s Y)) = (minus X Y))).

def[infix "<"] less : nat -> nat -> prop where
  forall (X:nat). (less z (s X));
  forall X. ~ (less (s X) z);
  forall (X:nat). (forall (Y:nat). ((less (s X) (s Y)) <=> (less X Y))).

def[infix "≤"] leq : nat -> nat -> prop where
  forall (X:nat). (leq z X);
  forall X. ~ (leq (s X) z);
  forall (X:nat). (forall (Y:nat). ((leq (s X) (s Y)) <=> (leq X Y))).

```

    Overwriting /tmp/test.zf

```python
!zipperposition /tmp/test.zf
```

    # done 0 iterations in 0.003s
    % Final clauses: 0
    # SZS status GaveUp for '/tmp/test.zf'

```python
%%file /tmp/one.zf
data unit := One.

goal forall (x y: unit). x = y.
```

    Writing /tmp/one.zf

```python
!zipperposition /tmp/one.zf
```

    # done 2 iterations in 0.003s
    # SZS status Theorem for '/tmp/one.zf'
    # SZS output start Refutation
    [32;1m*[0m sk__1 = One(1) by trivial
    [32;1m*[0m sk_ = One(2) by trivial
    [32;1m*[0m sk__1 = sk_(3) by simp 'demod' with sk__1 = One(1), sk_ = One(2)
    [32;1m*[0m goal [file "/tmp/one.zf" "zf_stmt_1"]
        ∀ x/45:unit y/46:unit. (x/45 = y/46). by
      goal 'zf_stmt_1' in '/tmp/one.zf'
    [32;1m*[0m negated_goal ¬ (∀ x/45:unit y/46:unit. (x/45 = y/46)) # skolems: []. by
      esa 'cnf.neg'
        with goal [file "/tmp/one.zf" "zf_stmt_1"]
               ∀ x/45:unit y/46:unit. (x/45 = y/46).
    [32;1m*[0m sk_ ≠ sk__1(0) by
      esa 'cnf'
        with negated_goal
               ¬ (∀ x/45:unit y/46:unit. (x/45 = y/46))
               # skolems: [].
    [32;1m*[0m ⊥(4) by simp 'simplify_reflect-' with sk__1 = sk_(3), sk_ ≠ sk__1(0)
    
    # SZS output end Refutation

```python
!cat /tmp/eq.dot | dot -Tsvg > /tmp/eq.svg
```

    cat: /tmp/eq.dot: No such file or directory
