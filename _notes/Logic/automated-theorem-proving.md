---
layout: post
title: Automated Theorem Proving
---

- [TPTP](#tptp)
  - [Puzzles](#puzzles)
  - [Math](#math)
- [Systems](#systems)
  - [Vampire](#vampire)
  - [E prover](#e-prover)
  - [Prover9](#prover9)
  - [Otter](#otter)
  - [LeanTAP and ilk](#leantap-and-ilk)
  - [PyRes](#pyres)
  - [Zipperposition](#zipperposition)
  - [Datalog vs ATP](#datalog-vs-atp)
  - [Prolog vs ATP](#prolog-vs-atp)
- [Strategies](#strategies)
- [Methodology](#methodology)
  - [Unification](#unification)
  - [Resolution](#resolution)
  - [Subsumption](#subsumption)
  - [Narrowing](#narrowing)
  - [Paramodulation](#paramodulation)
  - [Demodulation](#demodulation)
  - [Superposition](#superposition)
- [Literal Selection](#literal-selection)
- [Term Indexing](#term-indexing)
  - [Path Indexing](#path-indexing)
  - [Discrimination Trees](#discrimination-trees)
  - [Substitution trees](#substitution-trees)
  - [Feature Vectors](#feature-vectors)
- [Theories](#theories)
- [Higher Order](#higher-order)
- [Misc](#misc)


See also notes on:
- SMT
- prolog
- datalog

# TPTP
[TPTP](https://www.tptp.org/) Thousands of Problems for Theorem Provers is an incredible resource
[Quick Guide](https://www.tptp.org/TPTP/QuickGuide/)

A couple different input formats. As a human, tff is probably the best. Typed first order formula.
cnf is painful, fof is untyped and you're likely to screw it up imo.
tff offers built in ints, which is cool.

[TPTP in latex](https://math.chapman.edu/~jipsen/tptp/tptpPDF/)
[Axiom List](https://www.tptp.org/cgi-bin/SeeTPTP?Category=Documents&File=AxiomList) Highlights:
- PUZ - puzzles
- GEO - geometry
- GRP - group theory
- CAT - category theory
- SET - set theory
- NUM - number stuff [robinson arithmetic](https://www.tptp.org/cgi-bin/SeeTPTP?Category=Axioms&File=NUM008+0.ax)
- TOP [](https://www.tptp.org/cgi-bin/SeeTPTP?Category=Axioms&File=TOP001-0.ax)
- DAT - datatypes


Automated reasoning book
- puzzles
- circuit design (other sythesis problems?)
- program verification

Using for higher order or typed systems

## Puzzles

## Math

Groups
Lattices
kleene algebra, kat

Categories
Set theory https://en.wikipedia.org/wiki/List_of_set_identities_and_relation
Geometry

antiderivatives





# Systems
- Vampire
- E Prover https://wwwlehre.dhbw-stuttgart.de/~sschulz/E/E.html
- Zipperposition
- https://github.com/tammet/gkc on an in memory database
- [Twee: An Equational Theorem Prover](https://smallbone.se/papers/twee.pdf)

## Vampire
[First-Order Theorem Proving and VAMPIRE](https://publik.tuwien.ac.at/files/PubDat_225994.pdf)
[vampire tutorial](https://github.com/vprover/ase17tutorial)

```vampire
% https://www.tptp.org/TPTP/QuickGuide/Problems.html
%------------------------------------------------------------------------ 
%----All (hu)men are created equal. John is a human. John got an F grade. 
%----There is someone (a human) who got an A grade. An A grade is not 
%----equal to an F grade. Grades are not human. Therefore there is a 
%----human other than John. 
fof(all_created_equal,axiom,( 
    ! [H1,H2] : 
      ( ( human(H1) 
         & human(H2) ) 
     => created_equal(H1,H2) ) )). 

fof(john,axiom,( 
    human(john) )). 

fof(john_failed,axiom,( 
    grade(john) = f )). 

fof(someone_got_an_a,axiom,( 
    ? [H] : 
      ( human(H) 
      & grade(H) = a ) )). 

fof(distinct_grades,axiom,( 
    a != f )). 

fof(grades_not_human,axiom,( 
    ! [G] : ~ human(grade(G)) )). 

fof(someone_not_john,conjecture,( 
    ? [H] : 
      ( human(H) 
      & H != john ) )). 
%-------------------------------------------------------------------- 
```

```vampire
% a silly axiomatization of add and theorem.
% using typed formula

tff(num_type,type,
    num: $tType ).
tff(add_type,type,
    add: ( num * num ) > num ).
tff(zero_type,type,
    zero: num ).
tff(add_zero_axiom,axiom,
    ! [X: num] : add(X, zero) = X ).
tff(add_comm_axiom,axiom,
    ! [X: num, Y : num] : add(X, Y) = add(Y,X) ).
tff(mytheorem, conjecture, ? [X : num] : add(zero, X) = X).

```


```vampire
% https://www.tptp.org/cgi-bin/SeeTPTP?Category=Problems&Domain=DAT&File=DAT001=1.p
tff(list_type,type,
    list: $tType ).

tff(nil_type,type,
    nil: list ).

tff(mycons_type,type,
    mycons: ( $int * list ) > list ).

tff(sorted_type,type,
    sorted: list > $o ).

tff(empty_is_sorted,axiom,
    sorted(nil) ).

tff(single_is_sorted,axiom,
    ! [X: $int] : sorted(mycons(X,nil)) ).

tff(recursive_sort,axiom,
    ! [X: $int,Y: $int,R: list] :
      ( ( $less(X,Y)
        & sorted(mycons(Y,R)) )
     => sorted(mycons(X,mycons(Y,R))) ) ).

tff(check_list,conjecture,
    sorted(mycons(1,mycons(2,mycons(4,mycons(7,mycons(100,nil)))))) ).
```

Array axioms. Also axioms for int collections, int map, heaps. They all boil to pretty similar stuff though
```vampire
% https://www.tptp.org/cgi-bin/SeeTPTP?Category=Axioms&File=DAT001=0.ax
tff(array_type,type,
    array: $tType ).

tff(read_type,type,
    read: ( array * $int ) > $int ).

tff(write_type,type,
    write: ( array * $int * $int ) > array ).

tff(ax1,axiom,
    ! [U: array,V: $int,W: $int] : ( read(write(U,V,W),V) = W ) ).

tff(ax2,axiom,
    ! [X: array,Y: $int,Z: $int,X1: $int] :
      ( ( Y = Z )
      | ( read(write(X,Y,X1),Z) = read(X,Z) ) ) ).
```

```vampire
% https://www.tptp.org/cgi-bin/SeeTPTP?Category=Axioms&File=DAT001=0.ax
tff(array_type,type,
    array: $tType ).

tff(read_type,type,
    read: ( array * $int ) > $int ).

tff(write_type,type,
    write: ( array * $int * $int ) > array ).

tff(ax1,axiom,
    ! [U: array,V: $int,W: $int] : ( read(write(U,V,W),V) = W ) ).

tff(ax2,axiom,
    ! [X: array,Y: $int,Z: $int,X1: $int] :
      ( ( Y = Z )
      | ( read(write(X,Y,X1),Z) = read(X,Z) ) ) ).
```




```vampire
fof(ground, axiom,
    edge(1,2) & edge(2,3)
).
%fof(path1, axiom,
%    ![X,Y]: (edge(X,Y) => path(X,Y))
%).
%fof(path2, axiom,
%    ![X,Y,Z]:  ((edge(X,Y) & path(Y,Z)) => path(X,Z))
%).
fof(clark, axiom,
    ![X,Z]: (((?[Y]: (edge(X,Y) & path(Y,Z))) | edge(X,Z)) <=> path(X,Z))
).

fof(myquery, conjecture,
    ?[X,Y]: path(X,Y)
   %path(1,2)
).

```
vampire -av off --question_answering answer_literal

```vampire
fof(a,axiom,prover(vampire)).
fof(a,axiom,prover(e)).
fof(a,axiom,tutorial(vampire)).
fof(a,axiom,tutorial(probabilistic)).
fof(a,conjecture,?[X]: (prover(X) & tutorial(X))).
```

`--sos` 

inference restrictions
`--unit_resulting_resolution`

```bash
echo "
fof(ground, axiom,
    edge(a,b) & edge(b,c)
).
fof(path1, axiom,
    ![X,Y]: (edge(X,Y) => path(X,Y))
).
fof(path2, axiom,
    ![X,Y,Z]:  ((edge(X,Y) & path(Y,Z)) => path(X,Z))
).
" |  vampire  --unit_resulting_resolution on
```
Hmm. Vampire with the option or not. Not really sure what to take away from that. It might be recogzninig a datalog fragment
If I wanted to use this like an egraph, I can't look inside the equality. It's entirely unobseravle. Maybe I could use the reflection trick.

## E prover
enormalizer is an interesting sounding program. Give it a pile of unit equalities and it will normalize with respect to thm
EPR grounder to DIMACS
The e calculus is a bit puzzling. I haven't seen the analog for vampire

[2.6 manual](http://wwwlehre.dhbw-stuttgart.de/~sschulz/WORK/E_DOWNLOAD/V_2.6/eprover.pdf) It's also in the github repo if you `make doc`

I like how --answer mode works a little better for e.

Database printing feature -S. Doesn't print stuff I would expect though?
Kind of prints everything by default right?
Early stopping conditions
clause size


```bash
eprover --help | less
```

`--watchlist` - "constructive" proofs that aren't seeded by refuation
training - you can train it if you have a database of indicative theorems. This might be useful if you have a sequence of increasingly hard theorems, or if you are making a tool that spits out formula.
`-S` print saturated clause set
`-W` literaeelection stretagory NoGeneration will inhibit all generating instances "Each of the strategies that do actually select negative literals has a corresponding counterpart starting with P that additionally allows paramodulation into maximal positive literals"

```bash
echo "
fof(ground, axiom,
    edge(a,b) & edge(b,c)
).
fof(path1, axiom,
    ![X,Y]: (edge(X,Y) => path(X,Y))
).
fof(path2, axiom,
    ![X,Y,Z]:  ((edge(X,Y) & path(Y,Z)) => path(X,Z))
).
" | eprover  --literal-selection-strategy=SelectNegativeLiterals
```

`--generated-limit=100`
Ok this basically did what i wanted. I'm not sure what it is though?


"The most natural clause representation for E is probably a literal disjunction: a=$true;b!=$true;c!=$true."

```bash

```
## Prover9
[Prover9 and Mace4](https://www.cs.unm.edu/~mccune/prover9/)
Prover9 is intriguing. It seems to have interaction modalities that other provers don't
Mace
[proverx](http://proverx.com/doc/) a web gui variant

Some examples I didn't write:
```bash
echo "% Prove that a group in which all elements have order 2 is commutative.

assign(max_seconds, 60).

formulas(assumptions).

  % group axioms
  (x * y) * z = x * (y * z).   % associativity
  1 * x = x.                   % left identity
  x * 1 = x.                   % right identity
  x' * x = 1.                  % lef inverse
  x * x' = 1.                  % right inverse
  
  % special assumption
  x * x = 1.                  % all elements have order 2

end_of_list.

formulas(goals).
  x * y = y * x.
end_of_list.
" | prover9
```

```prover9
if(Prover9).
    assign(order, kbo).
    assign(max_weight, 25).
end_if.

formulas(sos).

% lattice theory

x v y = y v x.
(x v y) v z = x v (y v z).
x ^ y = y ^ x.
(x ^ y) ^ z = x^ (y ^ z).
x ^ (x v y) = x.
x v (x ^ y) = x.

end_of_list.

formulas(sos).
(x ^ y) v (x ^ z) = x ^ ((y ^ (x v z)) v (z ^ (x v y))) # label(H82).
end_of_list.

formulas(goals).
x ^ (y v (x ^ z)) = x ^ (y v (z ^ ((x ^ (y v z)) v (y ^ z)))) # label(H2).
end_of_list.
```

```prover9

assign(order, kbo).  % The default (lpo) al works, but it takes longer.

formulas(assumptions).

% Prover9 should produce a proof in a few seconds.

% combinators B and W

  a(a(a(B,x),y),z) = a(x,a(y,z))   # label(B).
  a(a(W,x),y) = a(a(x,y),y)        # label(W).

end_of_list.

formulas(goals).

  % existence of a fixed point combinator

  exists Q all x (a(Q,x) = a(x,a(Q,x))) # label(fixed_point_combinator).

end_of_list.

% Here is a different way of specifying the goal, which tells us
% what the fixed point combinator is.  We use an answer attribute.
% Unfortunately, answer attributes are not allowed on non-clausal
% (e.g., goal) formulas, so we deny the goal and state it as an assumption.
% Note that this introduces the Skolem function f.
%
% formulas(assumptions).
% a(x,f(x)) != a(f(x),a(x,f(x))) # answer(x).
% end_of_list.
```

## Otter
https://www.cs.unm.edu/~mccune/otter/
otter lambda - dumping lambda terms in otter? http://www.michaelbeeson.com/research/otter-lambda/
Otter seemed to offer more control over the resolution process
Prover9 is the succssor to otter

[otter manual](https://www.mcs.anl.gov/research/projects/AR/otter/otter33.pdf)
"Although OTTER has an autonomous mode, most work with OTTER involves interaction
with the user"
## LeanTAP and ilk
See prolog some
[Build Your Own First-Order Prover](http://jens-otten.de/tutorial_cade19/)
https://www.philipzucker.com/javascript-automated-proving/

## PyRes
- <https://www.ncbi.nlm.nih.gov/pmc/articles/PMC7324010/> Teaching Automated Theorem Proving by Example: PyRes 1.2
- pyres-simple is a minimal system for clausal logic, pyres-cnf adds heuristics, indexing, and subsumption, and pyres-fof


```python
# atomic formula first. Ground is basically the same.

# sets are unhashable, so are lists
#print({[], []})

# One canonical form is sorted, deduped pos,neg lists for clauses
def clause(pos,neg):
    return (tuple(sorted(set(pos))), tuple(sorted(set(neg))))

print(clause(["a","a"], ["c"]))
print(clause(["foo(a)","bar(a)"], ["c"]))

# we could also put a wrapper around set that does have a hash defined

def resolve(C1,C2):
    C1[0].diff(C2[1])
    C2[0].diff(C1[1])

    if len(C1[0].intersect(C2[1])) > 0:


processed = set()
unprocessed = []
while len(unprocessed) > 0:
    C = unprocessed.pop()
    for C1 in processed:
        resolve(C1,C)

```

```python
# terms are sexp style lists
# ["f", ["a"], ["g", "b"]]

```

A sqlized given-clause loop
```python
unproc = []
proc = sqlite3.connect(":memory:") # store processed clauses in DB.
while len(unproc) > 0:
    C.pop(unproc)
    sql = query(C)
    unproc.append(filter(cur.fetchall(), lambda: do_some_filtering))
    cur.execute("INSERT INTO", C)
```


Ground Subsumption queyr on clauses. Find all sets that have C as subset
```sql
CREATE Table lit (clause INTEGER, lit STRING); -- UNIQUE (clause, lit) gives redundant lit deletion
-- find all clauses c such it contains literal a,b,c.
SELECT DISTINCT clause from lit a, lit b, lit c where a.clause = b.clause and a.clause = c.clause and a.lit = ? and b.lit = ? and c.lit = ?
```

Find all sets that have C as superset

```
SELECT DISTINCT clause from lit a 
    group by a.clause 
    HAVING COUNT(CASE WHEN lit = ? THEN 1 END) +  COUNT(CASE WHEN lit = ? THEN 1 END) +  COUNT(CASE WHEN lit = ? THEN 1 END) = count(*);
    
    count(case when lit != ? or lit != ? or lit != ? then 1 end) = 0
    count(*) <= 3 -- would this help or hurt? redundant info 
    and 
    min(case when lit = ? then 1 when lit = ? when else 0 ) = 1

```




```python
t1 = "fah0"
t2 = "f01"
i1 = 0
i2 = 0
while i1 < len(t1) and i2 < len(t2):
    c1 = t1[i1] 
    c2 = t2[i2]
    if t2 


grammar = '''
E : F | G | Var | A
F : "f" E E
A : "a"
Var : NUMBER
'''

grammar = '''
Term : CNAME | CNAME "("  ("," Term)* ")" | Var
'''

class Unify(Transformer):
    env = {}
    def Var(self, v):
        if v in env:
    def term
```

Big question is, what is the representation of formulas, literals, clauses.
- Strings
- Json
- Relational Terms / hashconsed
- Feature vectors.
## Zipperposition

[logtk](https://hal.inria.fr/hal-01101057). Huh. LPO as a constraint solving problem https://sneeuwballen.github.io/zipperposition/2.0/logtk/Logtk_solving/index.html

[demo resolution prover](https://github.com/sneeuwballen/zipperposition/tree/master/src/demo/resolution)

```ocaml
#use "topfind";;
#require "logtk";;
print_endline "hello world";;
open Logtk
(* https://github.com/sneeuwballen/zipperposition/blob/master/tests/testTerm.ml *)
module T = Term
let f_ = ID.make "f"
let g_ = ID.make "g"
let ty = Type.term
let ty_t = Term.of_ty ty 
let prop = Type.prop
let f_fun = (T.const ~ty:Type.([ty;ty] ==> ty) f_)
let f x y = T.app f_fun [x; y]

let prec = Precedence.default [f_;g_]
(*let ord = Logtk.Ordering.lambda_kbo prec *)
let names = Ordering.names ()

let () = List.iter (fun name -> print_endline name) names

```

## Datalog vs ATP
What makes an ATP that different from a datalog? Both are saturating. If I could limit of prune clauses of size > N, that might emulate a datalog. Or perhaps protect rule-rule resolution from happening.

The given clause algorithm has some flavor of seminaive.
Datalog focuss on unit clauses
Not at all clear how to do extraction on a paramodulated database.

Given that ATP subsumes in some sense both prolog and datalog, what does it say about Magic Set?

Extraction from ATP. The equality is invisible. The copying trick?
## Prolog vs ATP
Set of support strategy with horn clauses in passive set, goal in active set, hyperresolution as only inference rule behaves akin to prolog.

[What is the difference between E and a PROLOG system?](https://wwwlehre.dhbw-stuttgart.de/~sschulz/E/FAQ.html)

Prolog `=` is unification. ATP `=` is rewrite/semantical.

# Strategies
Relationship to focusing http://web4.ensiie.fr/~guillaume.burel/download/LFAT.pdf

-Set of Support - Only infer on clauses that trace provenance to user specified set of support.

https://www.doc.ic.ac.uk/~kb/MACTHINGS/SLIDES/2013Notes/7LControl4up13.pdf
The Predicate Ordering Syntactic Refinement - order predicates. Only resolve on lowest
Locking Refinement - mark each literal in clause and resolve only on lowest one
atom ordering

- Resonance Strategy
- Weighting
- 
# Methodology 
Given clause 
Discount loop

## Unification
- see note on unification
Two way matching.
Is there a substitution for variables that solves an equation. Yes

Anti-unification is an interesting topic. Generalization.

```python
# https://github.com/pythological/unification
from unification import var, unify
x = var("x")
y = var("y")
y1 = var("y") # same y.
print(unify((x,y), (y1,1))) # returns subst dict
```
Or can use Maude's unification. Or prolog's. Or just write it.

## Resolution
Put clauses in cnf. Each clause is an `\/` of positive and negative atoms.
Take two clauses that have matching (unifiable) positive and negative pieces 

Hyperresolution https://www.doc.ic.ac.uk/~kb/MACTHINGS/SLIDES/8LHyper4up.pdf You are seeking clauses of only positive literals. Only use a "nuecleii" if it covers all of the negative literals.

UR-resolution - unit-resulting resolution. Only perform resultion if it results in nw unit literal (all other chunks line up). UR is essentially datalog stye resolution. It does however allow universals in the unit facts.


SLD resolution is ATP view of prolog.

Factoring


## Subsumption
Cleaning out the database.

given C(X) ,  C(a) is redundant (subsumed). You can remove it from clause database. A question is how to do this quickly. See Term indexing.

https://www.doc.ic.ac.uk/~kb/MACTHINGS/SLIDES/2013Notes/6LSub4up13.pdf
https://www.cs.cmu.edu/~fp/courses/99-atp/lectures/lecture20.html

encoding subusmption to SAT
https://fmcad.org/FMCAD22/presentations/08%20-%20SAT%20and%20SMT%202/01_rath.pdf
## Narrowing
see term rewriting

## Paramodulation
paramodulation is unification based equational substitution

https://math.stackexchange.com/questions/865562/a-simple-yet-non-superficial-explanation-of-what-paramodulation-means-in-the

Paramodulation is dealing with equality pieces in clauses.
http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.34.9958&rep=rep1&type=pdf

## Demodulation
rewrite rules basically? destructively simplify terms using them
Positive literals can be marked or inferred as demodulators (what we ordinary think of as rewrite rules)
By having both paramodulation and demodulation exist, the system has both destructive and conservative rules.

## Superposition
https://en.wikipedia.org/wiki/Superposition_calculus

[ntroduction to Superposition calculus - Cruanes](https://www.youtube.com/watch?v=zja691VwfSA&ab_channel=JetBrainsResearch) [slides](https://simon.cedeela.fr/assets/jetbrains_2021.pdf)

[New results on rewrite-based satisfiability procedures](https://arxiv.org/abs/cs/0604054)

Term orderings - see term rewriting

[Implementation of Saturating Theorem Provers](http://wwwlehre.dhbw-stuttgart.de/~sschulz/PAPERS/Schulz-SSA-2018ImpSat.pdf)

[Superposition 25](https://eprover.org/EVENTS/Superposition-25.html) http://www.eprover.org/EVENTS/Superposition-25/TutorialSP_ho.pdf

[backmair and ganzinger 1994](https://pure.mpg.de/rest/items/item_1834970/component/file_1857487/content)

superposition can be used instead of resolution by encoding predicates as functions to true

If I run superposition on unit positive clauses, is it performing completion? Completion of guarded rewrite systems?

[E a brainiac theorem prover](https://dl.acm.org/doi/10.5555/1218615.1218621)

The discussion of the encoding of t = s is a bit goofy. Yes, `=` is commutative. In that sense in is reasoonable to use sets. Could the opposite convention be used? This is kind of like the set-theoretic convention of `(a,b) === {{a}, {a,b}}` which is pretty bizarre too

`t = s  === {{t}, {s}}`
`t != s === {{t,s}}`
Multiset orderings
# Literal Selection
Ordered resolution - order on literals, only resolve on biggest one (you want to get rid of big stuff)
# Term Indexing
[Triemaps that match](https://arxiv.org/pdf/2302.08775.pdf) SPJ and Graf https://www.youtube.com/watch?v=cT8G6FS2v94&ab_channel=Konfy

```ocaml
type expr = Var of string | App of expr * expr
type 'a exprmap = {var : 'a String.Map.t; app : 'a exprmap exprmap } (* I thing if we play that nested data structure stuff we're gonna have a bad time  in ocaml*)

```

See Automated reasoning handbook chapter 18
https://www.cs.cmu.edu/~fp/courses/atp/lectures/22-indexing.html
[towards efficient subsumption - Tammet](https://www.cs.cmu.edu/~fp/courses/atp/cmuonly/T98.pdf)
[Give reasoning a trie](https://www.en.pms.ifi.lmu.de/publications/PMS-FB/PMS-FB-2020-2/PMS-FB-2020-2-paper.pdf)
Indexes are pretty good for serialized structures. You can serialize a term/tree by .
Perfect indexing vs approximate indexing. You don't necessarily need to index only the terms you need. YOu can iterate over the returned bits and just toss out the stuff you didn't want. Depends how expensive perfect vs imperfect is

Indexing has different kinds of queries. Is the database ground or not?
- Variants
- Unifiers
- Forward Subsumption
- Backwards subsumption
You may want multi-term indexing

## Path Indexing
most suitable for backward subsumption)
Consider paths from root to leaf of tree. Can put this in a trie.
Look at all paths in a query term of interest and take set intersection from path index trie.

Generalization? Consider just paths through a graph? f(a,b,c), g(a,d,c), ... . Up down and around. Kind of reminds me of code2vec

## Discrimination Trees
most suitable for unit forward subsumption

A depth first traversal of the whole term

## Substitution trees

## Feature Vectors
[Simple and Efficient Clause Subsumption with Feature Vector Indexing](http://wwwlehre.dhbw-stuttgart.de/~sschulz/PAPERS/Schulz2013-FVI.pdf)

[Fingerprint Indexing for Paramodulation and Rewriting](https://citeseerx.ist.psu.edu/document?repid=rep1&type=pdf&doi=b63b68cfbfb5636dc298f808e108e7ca513b68d3#page=490)

You can make summary data on terms that is monotonic with respect to instantation.

count and max depth appearance of symbols.
A generalization of seperating terms out by their head symbol
Imperfect indexing is useful. It does mean you may have to implement algorithms more than once.

# Theories
Inductiion [Superposition with Structural Induction](https://simon.cedeela.fr/assets/frocos_17_paper.pdf)
Datatypes [Superposition with Datatypes and Codatatypes](https://hal.science/hal-01904588)
Arrays
Arith [Beagle – A Hierarchic Superposition Theorem Prover](https://www.trustworthy.systems/publications/nicta_full_text/8726.pdf)

# Higher Order
Applicative encoding. Turn `f(x,y)` into `app(app(f,x),y)`. Wasteful and inefficint but it can work. Built in appreciation of higher order structure (currying basically?) is better
Higher order lambda free.
HORPO - term orderings that appreciate the applicative structure
[superposition for lambda free higher order](https://arxiv.org/pdf/2005.02094.pdf)
[Mechanical Mathematicians A new generation of automatic theorem provers eliminate bugs in software and mathematics](https://matryoshka-project.github.io/pubs/mechanical.pdf)

Differentiation? antiderivative search

Inside higher order systems
Meson
hammers
[](https://www.cl.cam.ac.uk/~lp15/papers/Notes/Herbrand.pdf) blast
[First-Order Proof Tactics in Higher-Order Logic Theorem Provers - Hurd](https://www.gilith.com/papers/metis.pdf) Metis


# Misc
[Uwe Waldemann - automated reasoning courses](https://people.mpi-inf.mpg.de/~uwe/lehre/)

[Ordering-Based Strategies for Hor n Clauses* - Dershowitz](https://www.ijcai.org/Proceedings/91-1/Papers/020.pdf) Equational horn clause. positive is larger than negative in literal selection

[33 Basic Test Problems: A Practical Evaluation of Some Paramodulation Strategies](https://www.cs.unm.edu/~mccune/papers/33-basic-test-problems/)

[Set of Support, Demodulation, Paramodulation: A Historical Perspective](https://link.springer.com/article/10.1007/s10817-022-09628-0)
[pfenning book](https://www.cs.cmu.edu/~fp/courses/atp/handouts/atp.pdf)

loveland book
fitting book
theorem proving in otter

wos summary https://ininet.org/automated-reasoning-and-resolution.html

http://wp.doc.ic.ac.uk/kb/teaching/ autmated reasoning course krysia 

Set of Support
prio


- <https://logictools.org/> neat online ATP interface
- TPTP


- Sledgehammer



Resolution is bottom up, tableau is top down?

[Automated Deduction in Equational Logic and Cubic Curves](https://ftp.mcs.anl.gov/pub/Otter/RP/monograph-8.ps.gz)


- Idea: Convert resolution proof to bus proofs tree. Is this even possible or desirable?

[Pelletier Problems](https://carlosareces.github.io/cordoba08/Bib/75ATPproblems86.pdf)


[Schulz teaching automated theorem proving](https://www.youtube.com/watch?v=j9Dyz5xXVrk)
[polymorphic vampire](https://www.youtube.com/watch?v=WTrzv1dSrTg)

[An Impossible Asylum](https://arxiv.org/abs/2112.02142) - ATP checking of Smullyan puzzle found hypotheses inconsistent

 Phillips & Stanovsky https://www2.karlin.mff.cuni.cz/~stanovsk/math/slides_esarm.pdf loop theory and non associative lagerbas
  https://www2.karlin.mff.cuni.cz/~stanovsk/math/slides_lpar08.pdf

  Searching for a Fixed Point Combinators by Using Automated
                    Theorem Proving: A Preliminary Report

Challenge Problems Focusing on Equality and Combinatory
                    Logic: Evaluating Automated Theorem-Proving Programs

tptp bibiography. It's insane how much work is here

[geometric database](http://www.mmrc.iss.ac.cn/~xgao/paper/jar-gdbase.pdf) horn clauses.

Waldmeister and Twee - UEQ

[REDUCING HIGHER-ORDER THEOREM PROVING
TO A SEQUENCE OF SAT PROBLEMS](https://www.ps.uni-saarland.de/Publications/documents/Brown2012a.pdf)

[vampire and the fool](https://arxiv.org/pdf/1510.04821.pdf)

Dedam: A Kernel of Data Structures and Algorithms for
                    Automated Deduction with Equality Clauses

[efficient full higher order unification](https://arxiv.org/abs/2011.09507) zipperposition

[Thesis on Implementation of Higher-Order Superposition](https://research.vu.nl/en/publications/implementation-of-higher-order-superposition)

[auto2](https://arxiv.org/pdf/1605.07577.pdf) interesting system that combines egraphs and sturation proving https://github.com/bzhan/auto2 he alos mentions gowers as influence
[Coming to Terms with Quantified Reasoning](https://arxiv.org/abs/1611.02908)
algerbaic datatypes require an infinite number of acyclicity axioms.

https://www.ps.uni-saarland.de/Publications/documents/Treinen_tacs91.pdf FOL + datatypes is more powerful than just FOL.


```python
from pysmt.shortcuts import get_env
from pysmt.logics import LOGICS
from pysmt.shortcuts import Symbol, get_env, Solver
env = get_env().factory.add_generic_solver("vampire", ["/home/philip/.local/bin/vampire", "--input_syntax", "smtlib2"], LOGICS)
print("opening")
with Solver(name="vampire", logic="QF_UFLRA") as s:
  print("starting")
  print(s.is_sat(Symbol("x"))) # True
```

```python
from z3 import *
s = Solver()
x = Bool("x")
s.add(And(x, Not(x)))
#s.add(x)
s.check()
print(s.to_smt2())
import tempfile
import subprocess
with tempfile.NamedTemporaryFile(suffix=".smt2") as fp:
    fp.write(s.to_smt2().encode() + b"(get-model)")
    fp.flush()
    res = subprocess.run(["/home/philip/.local/bin/vampire", fp.name],  capture_output=True)
    print(res.stdout.decode())

```
