---
layout: post
title: Term Rewriting
---

- [Abstract Rewrite Systems](#abstract-rewrite-systems)
- [Completion](#completion)
  - [unfailing completion](#unfailing-completion)
- [Ground Rewriting](#ground-rewriting)
- [Term Orderings](#term-orderings)
  - [KBO](#kbo)
- [Termination](#termination)
- [Implementation](#implementation)
- [Narrowing](#narrowing)
- [AC](#ac)
- [Higher order rewriting](#higher-order-rewriting)
- [Egraph](#egraph)
- [String rewriting systems](#string-rewriting-systems)
- [Graph Rewriting](#graph-rewriting)
  - [Groove](#groove)
  - [CHR](#chr)
  - [Term Indexing](#term-indexing)
  - [Order Sorted Logic](#order-sorted-logic)
- [Systems](#systems)
  - [Maude](#maude)
    - [Unification](#unification)
    - [Equation Search](#equation-search)
    - [Built ins](#built-ins)
    - [Category](#category)
  - [Eqlog](#eqlog)
  - [K](#k)
  - [spoofax](#spoofax)
- [Other Systems](#other-systems)
- [TRaaT Rust](#traat-rust)
- [2020 Term rewritng notes](#2020-term-rewritng-notes)
- [Misc](#misc)

<https://www.stephendiehl.com/posts/exotic02.html>

Term rewriting and all that
Term rewriting - Terese

# Abstract Rewrite Systems

<https://en.wikipedia.org/wiki/Abstract_rewriting_system>
This is sort of a study of relations and transitvitym, symmettry.

confluence
church rosser

If the reduction relation is a subset of a well founded relation, it is terminating. This is kind of a definition of termination

# Completion

Knuth bendix

Naive completion

```python
# Fig 7.1 in TRAAT

# rewrites as tuples
R = {("a", "b")}

while not Rnew.issubset(R):
  R = R.union(Rnew)
  Rnew = {}
  for (lhs,rhs) in R:
    lhs1 = reduce(lhs)
    rhs1 = reduce(rhs)
    if lhs1 < rhs1:
      Rnew.add((lhs1, rhs1))
    else:
      Rnew.add((rhs1, lhs1))

# Could use maude to actuall perform reduction.
```

```python
def init_eqs(E):
  R = set()
  return (E, R)

def deduce(ER, u, s, t):
  (E,R) = ER
  # confirm u -> s, u -> t
  return (E.union({(s,t)}), R)

def delete(ER,s):
  (E,R) = ER
  assert s in E:
  return (E.diff((s,s)), R)

def 


```

Newman's lemma weak conlfuence + termination => strong confluence

critical pair for terms - 1 is unifiable with the other.

Similarity to grobner basis
similarity to gaussian elimination

Knuth Bendix asks a lot though. The more obvious approahc is to heuristically aspply rewrite to your actual problem rather than try to completely solve all possible problems up front. Why not do this fro grobner? It sounds stupid for gaussian though. Maybe. Just sort of greedily try to write your query polynomial in terms of the ones you have? This might be the analog of some iteraitve scheme like gauss jacobi.

Finite state machines are rewrite systems with each state being a single simple constant

<https://github.com/bytekid/mkbtt> - does knuth bendix completion. There is a web interface
<https://github.com/bytekid/maedmax> ?
<http://cime.lri.fr/> cime

## unfailing completion

# Ground Rewriting

A Ground rewriting system is an egraph in a loose sense. Both are pile of ground equations.
Completion is canonicalization.

```
def size(t):
  return 1 + sum(map(size, t[1:]))
def term_order(t1,t2):
  s1 = size(t1)
  s2 = size(t2)
  if s1 < s2:
    return True
  elif s1 == s2:
    if t1[0] < t2[0]:
      return True
    elif t1[0] == t2[0]:
      for t,s in zip(t1[1:], t2[1:]):
        if term_order(t,s):
          return True
  return False



def groundrewrite(lhs, rhs, t):
  if lhs == t:
    return rhs
  return [t[0]] + [map(groundrewrite(lhs,rhs) , t[1:]

```

Hmm. Interesting. Term orderings on ground terms are a good hting to consider first. A bit less complicated than terms with variables.

```python
if str_order(t,s):
  if len(t) < len(s):
    return True
  elif len(t) == len(s):
    return t < s
  else:
    return False 
```

No this is a bad ordering. It doesn't obey subterm properties?

Term ordering Mod E. Term Ordering mode beta

The egraph implements a fast on the fly defind term ordering.
But we can probably define an easy to compute ahead of time ground ordering. Memoize fingerprints, etc.

As compared to string rwriting, I don't want to (or don't have to) consider non-complete overlap pairs? That's what really makes this process terminating perhaps.

# Term Orderings

[Things to Know when Implementing KBO](https://link.springer.com/article/10.1007/s10817-006-9031-4)
[Things to Know when Implementing LPO](https://www.worldscientific.com/doi/10.1142/S0218213006002564)
rewrite ordering
reduction ordering

Interpretations
f(x) -> a + x
a counts occurrances of f basically
f(f(f(X))) = 3a + x

Simplification orderings
homomorphism

KBO
RPO
LPO

stable under subsitition
stable under contect
terminating

weighted path order WPO

kbo - maps all variables to number that is less than all actual symbols
Then upon subsitution, the cost can only increase
first check variabnle count is ok
complicated tie breaking
<https://www.cs.miami.edu/home/geoff/Courses/TPTPSYS/FirstOrder/SyntacticRefinements.shtml>

[Empirical Properties of Term Orderings for Superposition - Schulz](http://wwwlehre.dhbw-stuttgart.de/~sschulz/PAPERS/Schulz-PAAR-2022.pdf)

Basically term size is a good idea for a termination ordering

But also obviously definitional systems are obviously terminating. Systems that do not have recursive definitions. However, these unfolder systems clearly grow term sizes. So we need an intuition for these. THe lexicographic order works. THe ordering on symbols is the definition order
No `let rec`

```
let f x = x
let g x y = f f f f f f f x 
let h x = g (f x) (f x)
```

Any program in this system is obviously terminating.
Non recursive Macro expansions

But maybe you need some mix of "called on smaller arguments" + definition unpacking

Hmm. But weighted size is more or less KBO. And if we made the weight very high for the lower definitions, that might work too.

You can remove extra ways from some algortihmic description of an ordering and it stays a partial ordering, just a weaker one.

[REST: Integrating Term Rewriting with Program Verification](https://malyzajko.github.io/papers/ecoop2022b.pdf)
So I think they are doing ordered rewriting but they maintain an abstraction over which term order they are using.And then they have a search procesdure that branches when they can't make progress to try and specialize the order.

[Computability path ordering](https://arxiv.org/abs/1506.03943v2)

## KBO

1. s > var_X if var_X is in s. Base case for variables.
2. All number of occurances of variables must be equal or reduced.
3. weighting function must be reduced
4. to tie break some weighting function equivalnces, we can start a. check ordering on head symbols b. recursing into subterms

Weighting function

1. weight for all variables must be the same
2. zero weights is fishy

Otherwise it's the obvious add up the number of occurances of symbols weighted

Going ground is smart for understanding

```ocaml
#use "topfind";;
#require "ppx_jane sexplib";;

open Sexplib.Std

type term = 
| Const of string
| App of term * term [@@deriving sexp]

(* Apply term * term  ?? *)

let app (f : term) (args : term list) : term = List.fold_left (fun f x -> App (f,x)) f args

let rec size = function
| Const _ -> 1
| App (f,x) -> size f + size x
(* List.fold_left (fun acc a -> acc + size a) (size a) args *)


let rec ground_kbo t1 t2 =
    let s1 = size t1 in (* obviously silly to be recomputing thi a bunch *)
    let s2 = size t2 in
    if Int.equal s1 s2 then
        match t1, t2 with
        | Const x1, Const x2 -> String.compare x1 x2 (* could compare weights first *)
        | Const x1, App (f,args) -> -1
        | App (f,args), Const x1 -> 1
        | App (f1,args1), App (f2,args2) -> 
            let cf =  ground_kbo f1 f2 in
            if Int.equal cf 0 then
              ground_kbo args1 args2 else
              cf
    else Int.compare s2 s2

let f = fun x -> App ((Const "f"), x)
let a = Const "a"
let () = print_int (compare (f (f a)) (f a))
let () = print_int (compare (f a) (f a))
let () = print_int (compare (app (Const "f") [a;a]) (f a))


(* 
type memo_term =
 | Const of string
 | Apply of {size : int; head : memo_term, memo_term term array}
and data = 
  {size : int; id : int; hash : int; feature : int array ; sym : memo_term }
*)

```

[KBO for combinators](https://www.ncbi.nlm.nih.gov/pmc/articles/PMC7324232/)

[A unified ordering for termination proving - WPO weighted path order](https://www.sciencedirect.com/science/article/pii/S0167642314003335?via%3Dihub)
But also interesting survey

dependency pairs
matrix interpretations
POLO

# Termination

aprove is pretty domainantn. C, llvm, haskell, java, prolog, trs,some integer transition stuff

<https://aprove.informatik.rwth-aachen.de/download>

AProve [http://aprove.informatik.rwth-aachen.de/index.asp?subform=home.html](http://aprove.informatik.rwth-aachen.de/index.asp?subform=home.html) aachen
<https://github.com/aprove-developers/aprove-releases/releases> releases

ecipse plugin. Huh

```bash


echo "
[x,y]
plus(0,y) -> y
plus(s(x),y) -> s(plus(x,y))
" > /tmp/plus.tes
java -ea -jar ~/Downloads/aprove.jar  -m wst /tmp/plus.tes
echo "
(VAR x y)
(RULES
    plus(0,y) -> y
    plus(s(x),y) -> s(plus(x,y))
)
" > /tmp/plus.trs
java -ea -jar ~/Downloads/aprove.jar -p plain  -m wst /tmp/plus.trs
# help for prolog https://aprove.informatik.rwth-aachen.de/help_new/logic.html
echo "
%query: append(b,f,f)
append([],L,L).
append([X|Xs],Ys,[X|Zs]) :- append(Xs,Ys,Zs).
" > /tmp/append.pl
java -ea -jar ~/Downloads/aprove.jar -p plain  -m wst /tmp/append.pl
#java -ea -cp ~/Downloads/aprove.jar aprove.CommandLineInterface.PrologFrontendMain
```

```bash
echo "
{-# htermination (mysum :: (List a) -> (List a))) #-}
import qualified Prelude
data MyBool = MyTrue | MyFalse
data List a = Cons a (List a) | Nil
mysum Nil = Nil
mysum (Cons x xs) = mysum xs
"
> /tmp/mysum.hs
java -ea -jar ~/Downloads/aprove.jar  -m wst /tmp/mysum.hs 

```

```bash
echo "
{-# htermination (foldr1 :: (a -> a -> a) -> (List a) -> a) #-}
import qualified Prelude
-- import List
data MyBool = MyTrue | MyFalse
data List a = Cons a (List a) | Nil

foldr1 :: (a -> a -> a) -> (List a) -> a
foldr1 f (Cons x Nil) = x
foldr1 f (Cons x xs) = f x (foldr1 f xs)
" > /tmp/fold.hs
java -ea -jar ~/Downloads/aprove.jar  -m wst /tmp/fold.hs

```

Installed yices 1 so it would stop complainging.

startTerm?
-q QUERY is used to specify a query, e.g., to analyze arbitrary methods or to provide information about the method's arguments.
The flag -b

```
#java -ea -cp ~/Downloads/aprove.jar aprove.CommandLineInterface.HaskellFrontendMain

"
sage: java -cp aprove.jar aprove.CommandLineInterface.HaskellFrontendMain [OPTION] HSFILE

Haskell to QDP/Graph dump export from AProVE 2014.

 -h, --help             print this help
 -o, --outputDir DIR    directory in which TRSs will be dumped (default '.')
 -t, --timeout SECONDS  timeout, in seconds (default 60)
 -p, --proof            print proof for steps from input to TRSs
 -g, --graph yes|no     export to Graph (default no)
 -q, --query QUERY      a query which tells AProVE what to analyze
 -s, --startTerm TERM   analyze termination starting with term TERM
 -j, --json yes|no      export JSON (default no), conflicts with other output
"
```

TTT innsbruck [http://eptcs.web.cse.unsw.edu.au/paper.cgi?ThEdu19.4](http://eptcs.web.cse.unsw.edu.au/paper.cgi?ThEdu19.4)

<http://cl-informatik.uibk.ac.at/software/ttt2/>

```bash
ttt2  /tmp/plus.trs
```

<http://cl-informatik.uibk.ac.at/software/ceta/> ceta. Certified termination

<http://zenon.dsic.upv.es/muterm/> muterm

```bash
ceta 
#usage: ceta [(parameters) certificate | --version]
#  
#  A "certificate" is an XML file in the certification problem format (CPF 3.x).
#  (manually setting a parameter overwrites information in CPF):
##  --allow-assumptions    Allow (axiomatic) assumptions in the certificate.
 # --inputf fname         Read input from separate file.
 # --propertyf fname      Read property from separate file.
 # --property p           Read property from string p.
 # --answerf fname        Read answer from separate file.
 # --answer a             Read answer from string a.
 # --version              Print the version number (+ mercurial id).
```

koat
loat
cofloco

Nontermination checking
Online termination checking

<https://link.springer.com/chapter/10.1007/978-3-642-32347-8_17> stop when you're almost full. Adventures in constructive termination

<https://github.com/TermCOMP/TPDB> termination problem database

<https://termination-portal.org/wiki/Termination_Portal>
Termcomp 2022 <https://termination-portal.org/wiki/Termination_Competition_2022>
<https://termcomp.github.io/Y2023/> 2023 results

Dumping into a constraint solver. For a parametrzied family, conceivably one can build a constraint problem over the parameters that requires a rewrite system follows a term order. For an equational system, one could have the "or" of the two directions as part of the constraints.

The dummiest version of this is a MIP for weights of symbols and uses a < inequality of the weight of the two sides.
It's the tie breaking that is a real pain.

2021- 02

Coq and termination
Accessibility relations, Sam's paper
Bove-Capretta method - a Defunctionalization of the Acc method?
Adding an accessibility parameter - delays the requirement of proof to when it receives this

2020-12-07

Polynomial interpetations - each function symbol goes to some polynomial. variable stay variables.
f(g(x,y)) ->   yada yada
If you bound you coefficents to integers and small, the nonlinearity of the coefficients from f and g aren't persay a problem

RPO. recsurive path orderings.

String rewriting termination. The simpler model.
abc -> cdf
assign each guy to an nonegative integer.
a + b + c > c + d + f.

This one is actually an ILP.

This is polynomial interpetation where concat/cons symbol has intepretation of plus and each constant symbol has interpetation of a number.

<http://www.cs.tau.ac.il/~nachumd/papers/termination.pdf> dershowitz termination review 1987

The obviously terminating stuff always decreases
Doesn't always decrease, but clearly we lose 3 aaa to make a c but only gain 2 a from a c. We're losing net a every time we make a step.
c -> aa
aaa -> c

strategy : build string model of finite depth term rewriting system. See if it works.
build ground terms instantiation on term rewrite system. Constrain somehow
Possibly try to encode "good" thing in objective function.
Find failure. iterate.
This is a cegis.

2020-03-09

A Harmonic Oscillator. Prove that it is stable. Build lyapunov function. Can do with SDP. V >= 0, st. $latex \frac{d}{dt} xVx <= 0$. Or better yet $latex \frac{d}{dt} xVx <= \eps$ or $latex \frac{d}{dt} xVx <= eps (x V x)$.

Also could consider breaking up space into polyhedral regions (quadrants for example. Find a piecewise linear lyapunov function.

Another interesting problem is to prove escape from a region. Prove that osciallator eventually escapes x>=1. No prob. We also get a bound on the time it takes.  V(x) = cx. dot V = c xdt = c A x <= eps forall x >= 1.

min eps,   forall x. c A x - eps <= lam (x - 1)  ... this is not possible. lam needs to become a positive polynomial. No, it is possible if lam = cA xhat  and eps <= lam.

An interesting discrete analog of this system would be a swapper. x0 >= 1 implies x0' = x1, x1' = x2, x2' = x3, x3' = x0-1. The minus 1 gives us a small decay term.

For a string rewriting system, the simplest thing is just look at some kind of count on the symbols. Maybe with some weighting. It may be that you are always decreasing. If just count doesn't work, you can try 2-grams or other features/combos. This feels something like a sherali-adams

For term rewriting, we could try to ignore the parse structure and use the count as string rewrite as above. Polynomial interpetation appears to want to interpret a term that is applied as a polynomial. This seems like it would create difficult nonlinear constraints for both verification and synthesis. Although if you constrain each polynomial to be bounded integers, it may make sense to pound them into a sat solver. Ok if each intepretation is only linear, then the combined would still be linear for verification.

Integer and Polynomial Programs. This means something rather different from integer programming. The idea is that all variables are integer, but you still have a notion of time. Guarded transitions. It seems likely I could compile this into an integer program. Reify inequality conditions.

Cegar loop. Can run program to get a bunch of traces. Use traces and find a decreasing function on all traces.

[https://link.springer.com/chapter/10.1007/978-3-540-72788-0_33](https://link.springer.com/chapter/10.1007/978-3-540-72788-0_33) SAT solving for temrination checking. It does appear they slam nonlinear arithmetic problems into sat solver.s

Dependency pair? What is this. People seem to think it is very important

The control community has similar questions and similar yet different appproaches. They often want continuous state.

[https://github.com/blegat/SwitchOnSafety.jl](https://github.com/blegat/SwitchOnSafety.jl)

[https://github.com/blegat/HybridSystems.jl](https://github.com/blegat/HybridSystems.jl)

SpaceEx. Platzer's stuff.  JuliaReach

Barrier functions. I think the idea is the you put a function that is diverging at the region you're worried about. If you can guarantee that this function is not diverging.

Sum of Squares certificates. Describing sets as sublevel sets.

The S-Procedure. I think this is that you can relax all inequalities using your assumptions $latex  f(x) >=0 implies g(x) >=0$ then $latex g(x) >= \lambda f(x)$ and $latex \lambda >= 0 $ is sufficient. Sometimes it is necessary I think.

Hybrid Systems. Piecewise affine systems.

Reachability. We want to figure out how to rewrite one equation into another. Building an A* style lower bound distance could be quite helpful. A lower bound cost to get to some position. In terms of a control objective function S(x,x'), V(x,x'). In a small finite graph this could be computed. But suppose we didn't have enough flexibility. Finite graph, linear function of the features.

Ok. Some things. My concern about nonlinearity for multiply composed functions. 1. you might interpet some things differently (as fixed polynomial interpretation). Makes sense for constructors and data structures, where we have some reasonable suggestions. Looking at HEADs seems to matter a lot / give important over approximations of the behavior of the system. integer transition system. We can pattern match on fixed integers. f(x, 1) = yada.   f(x,y) -> f(y+1,x).  This we can do with guards.  f(x) | x > 7 -> g(x + 7).  f ~ 1 + a x + bx^2 + ... and so for g. Then f(x) >= g(x) + lam guard is lyapunov condition. We want struct inequality, that is the point of the integer nature of the system.  f(x) | x < 7 -> f(x**2 -  )

sum(n, acc) -> sum(n - 1, acc+n)

# Implementation

[Terms for Efficient Proof Checking and Parsing](https://www.youtube.com/watch?v=SdB2hVIZ2nI&ab_channel=ACMSIGPLAN)
Two different types for terms that are expected to live different amounts of time. Differ only in rust pointer type. short terms have borrowed reference to long terms. Kontroli

# Narrowing

<https://maude.lcc.uma.es/manual271/maude-manualch16.html>
Narrowing is like prolog resolition
Instead of rewriting ground terms, we cna rewrite terms with variables. Nondeterminsically we might unify and "narrow" the variables in there.

[functional logic programming in maude](http://personales.upv.es/sanesro/papers/futatsugi-fest.pdf)

# AC

- [flat and orderless patterns in mathematica](https://reference.wolfram.com/language/tutorial/Patterns.html#28368)
- [Associative-Commutative Rewriting on Large Terms - Eker](https://link.springer.com/chapter/10.1007/3-540-44881-0_3) [ac slides](http://maude.cs.uiuc.edu/papers/pdf/acSlides.pdf) Interesting, they use term in indexing to try and prune the explosion faster. Fingerprints / etc. They need AC if they want to represent Maps equationally in maude with the right asymptotic properties. S. M. Eker. Associative-commutative matching via bipartite graph matching. Oh snap. Some AC patterns can be fast
- []()
- [Non-linear Associative-Commutative Many-to-One Pattern Matching with Sequence Variables](https://arxiv.org/abs/1705.00907)
- [Compilation of Pattern Matching with Associative-Commutative Functions](https://link.springer.com/content/pdf/10.1007/3-540-53982-4_4.pdf)
- [matchpy docs](https://matchpy.readthedocs.io/en/latest/)
- [Commutative unification](https://matthewrocklin.com/blog/work/2013/01/25/Commutative-Unification)
- [Equational Unification and Matching, and Symbolic Reachability Analysis in Maude 3.2 (System Description)](https://link.springer.com/chapter/10.1007/978-3-031-10769-6_31)
- [associative commutative rules Symbolics.jl](https://github.com/JuliaSymbolics/SymbolicUtils.jl/pull/12)
- [Variadic Equational Matching in Associative and Commutative Theories](https://www3.risc.jku.at/publications/download/risc_6260/variadic-equational-matching-jsc-final-with-mma-versions.pdf) comparing with mathemticas closed source solution. Systems of equations perspective like unification is interesting angle. Matching is solution of system of equations.
- [asscaitve unification in maude](https://www.sciencedirect.com/science/article/abs/pii/S2352220821001103?via%3Dihub)

Even if you have a confluent terminating system, E-matching (in this other sense?) requires search. Interesting. So that's probably what the variant stuff is about.
If you do narrowing rewriting on the patterns (only interesting non critical pair overlap), eventually the pattern is so instantiated it can't possibly match the term (?). That could help. This is back to the idea of treating AC as a macro on patterns. This is limitting in many ways. But maybe limitting is what you want. Pre resolution on datalog rules.

# Higher order rewriting

# Egraph

See

- egraphs
- egglog

A form of nondestructive term rewriting

# String rewriting systems

[Semi-Thue systems](https://en.wikipedia.org/wiki/Semi-Thue_system)
[Word problem](https://en.wikipedia.org/wiki/Word_problem_(mathematics))
Monoid presentation

converting to term rewriting system fff ---> f(f(f(X)))

Term Rewriting using linux command line tools

The string search and manipulation tools are very powerful and efficient. They compile queries like grep into simple machines and such I think.

There's a big difference between ground and non ground terms. They appear subtly different when latexed, but the are way different beats
Ground terms equation proving can be done through the e graph efficiently.

Ground term rewriting seems to be identical to string rewriting. Just layout serially a traversal of the term.

The implicit prefix and suffix are the context of the term

```python

rules = [
  ("aa", "b"),
  ("b", "c")
]

def run_rules(s,rules):
  old_s = None
  while s != old_s:
    old_s = s
    for lhs,rhs in rules:
      s = s.replace(lhs,rhs)
  return s

print(run_rules("ababaaaaccaaa", rules))

def naive_completion(rules):  
  old_rules = None
  while rules != old_rules:
    old_rules = rules.copy()
    for (lhs,rhs) in old_rules:
        a = run_rules(lhs, rules)
        b = run_rules(rhs, rules)
        if a == b:
          break
        if a < b:
          rules.add((b,a))
        if a > b:
          rules.add((a,b))
  return rules

# an incomplete reduction routine?
# Triangular rewrite rules in some sense.
# Is this right at all? This is like a chunk of Huet's. I think just moving R -> E might be ok even if not one of listed rules. No, if I could do that ths move + simplfy would give me a more powerful R-simplify.
# I might be weakening my rules. That's not so bad imo.
def reduce_rules(E):  
  # worklist style
  R = set()
  # Sort E so smallest last probably. Most reduction power.
  E = sorted(E, key=lambda k: len(k[0]), reverse=True)
  while len(E) > 0:
    (a,b) = E.pop()
    a = run_rules(a, R) # simplify
    b = run_rules(b, R)
    print(a,b)
    if a == b: #delete
      continue
    if (len(b), b) > (len(a), a): # len then lex ordering
      R.add((b,a))
    if (len(a), a) > (len(b), b):
      R.add((a,b))
  return R



rules = {
  ("aaa", "a"),
  ("aaa", "c")
}

print(naive_completion(rules))


rules = [
  ("ffa", "a"),
  ("fa", "a")
]

print(run_rules("ffffffffffffa", rules))

print(reduce_rules(rules))

rules = [
  ("12+", "21+"), # an application of comm
  ("23+1+", "2+31+") # an application of assoc
]
# I am really going to want a notion of indirection or compression here.
# Intern strings

class RPN():
  def __init__(self, s):
    self.s = str(s)
  def __add__(self,b):
    return RPN(self.s + b.s + "+")
  def __repr__(self):
    return self.s

b0 = RPN(0)
b1 = RPN(1)
b2 = RPN(2)
b3 = RPN(3)


E = [
  (b1 + b0, b0 + b1),
  (b0 + b1, b1),
  (b1 + b2, b3),
  (b2, b1 + b1) 
]
E = [
  ("10+", "01+"),
  ("01+", "1"),
  ("12+", "3"),
  ("2", "11+"),
  ("00+", "0"),
  ("00+1+1+1+", "3"),
]

print(reduce_rules(E))
E = reduce_rules(E)
print(run_rules("00+1+0+1+0+2+",E))

E = [( str(i) + str(j) + "+" , str(i + j)) for i in range(4) for j in range(10) if i + j <= 9]
print(E)
print(reduce_rules(E))
print(run_rules("00+1+0+1+0+2+",E))

```

Ropes

We can of course compile a rule set to do better than this. In some sense every string represents a possibly infinite class of strings posible by running rules in reverse

String rewriting systems are a bit easier to think about and find good stock library functionality for.

string rewriting is unary term rewriting. A variable string pattern "aaaXbbbb" is a curious object from that perspective. While simple, it is a higher order pattern. `a(a(a(X(b(b(b(Y)))))))`. You can also finitize a bit. `foo(a)` can be made an atomic character. Or you can partially normalize a term rewriting system to string rewriting form

String orderings
Lexicographic comparison
Length
shortlex - first length, then lex
symbol counts

```python
def critical_pairs(a,b):
  assert len(a) > 0 and len(b) > 0
  if len(b) <= len(a):
    a,b = b,a # a is shorter
  cps = []
  if b.find(a) != -1: # b contains a
   cps.append(b)
  for n in range(1,len(a)): # check if overlapping concat is possible
    if b[-n:] == a[:n]:
      cps.append(b + a[n:])
    if b[:n] == a[-n:]:
      cps.append(a + b[n:])
  return cps

print(critical_pairs("aba", "ac"))
print(critical_pairs("aba", "ca"))
print(critical_pairs("abab", "ba"))
  
'''
def reduce_rules(rules): # a very simple reduction, reducing rhs, and removing duplicate rules
  rules1 = set()
  for (lhs,rhs) in rules:
    rhs = run_rules(rhs,rules)
    rules1.add((lhs,rhs))
  return rules1
'''

  #run_rules
  #reduce_rules
```

Building a suffix tree might be a good way to find critical pairs.

Lempel Ziv / Lzw is the analog of hash consing? Some kind of string compression is. That's fun.

<http://haskellformaths.blogspot.com/2010/05/string-rewriting-and-knuth-bendix.html>

It seems like named pattern string rewriting and variable term rewriting might be close enough

You could imagine

((x + 0) + 0 + 0) laid out as + + + x 0 0 0. and the found ground rewite rule + x 0 -> x being applied iteratively.

Labelling shifts:
f(g(a), b) ->   f +0 g +1 a -1 b -0

the pattern
f(?x)  -> ?x
 becoming
 f +0 <x> -0 -> <x>
 f +1 <x> -1 -> <x>
 f +2 <x> -2 -> <x>
and so on to some upper limit
We could occasionally renormalize maybe if there are no +n -n pairs remaining.
then shuffle all the above ones down.
Ok but what about something that increases the depth
x -> f(x)
... hmmm.

And if we number from the bottom?

f +2 <X> -2 -> <X>

and
<X> -> ??? Well a raw pattern is pretty shitty
f(x) -> f(f(x)) becomes
f +n <X> -n -> f +(n+1) f +n <x>
Yeah. Numbering from the bottom is better. We don't have to

f(stuff,stuff)
f +n <X> -n +n <Y> -n

even without enumerating
plus +<n1> <X> -<n1> +<n2> <Y> -<n2>

Oooh. We have to enumerate every combo of possible subterm depths.

Hmm. This adjust levels

<http://matt.might.net/articles/sculpting-text/>

A unique terminator for the subexpression is the point.
f +2 (^ -2)* -2

could have a counter per symbol. per symbol depth.
f1 ( yadayada) \f1

fa1 <X> fb1 <Y> fc1

huh. What about the CPP? Won't that basically work?

This is horribly inefficent because it'll expand out huge terms.
And big backtracking jumps. Or rather big seeks while it tries to find the next spot to go to. The next argument of f.

For ground term rewriting it seems actually reasonable and faster than having indirections. We can't have sharing though. That is a bummer.Maybe with zip.
Unless our goal is simplifcation.

using the rule

We could try to use the e-matching strategy where we iteratively instantiate fixed ground rewrite rules into the sed file itself?

Instead of using parenthesis, one could use numbered enter level exit level. And then bound the number of levels.
Each term rewriting becomes a string rewriting (with named regex holes ) replicated by the number of supported levels.

using sed on itself we might be able to implement knuth bendix

One could compile into a human unreadable huffman encoded like thing

<https://superuser.com/questions/1366825/how-to-recursively-replace-characters-with-sed> looping in sed
You can gnu parallel into chunks
grep is much faster. If terms are rare, maybe find using grep first?

Suffix trees can store every subterm of ground term with efficient query.

<https://spencermortensen.com/articles/serialize-a-binary-tree-in-minimal-space/> an interesting perspective on tree serialization
catalan numbers. We know size of tree if we give elements.
<https://www.educative.io/edpresso/what-is-morris-traversal> woah. Bizarre. It mutates the true as it goes down it and store
Kind of reminscent of dancing links in a way

f 20 90 190 yada yada yada could desribe links to the approprate spots.
This would be the analog of flatterms.

There is something like encoding lambda terms with de bruijn. vs unique signifiers.
If we could encode the unique signifiers in a way such that they never collide.

There is something to that we're kind of converting to rpn.
<https://github.com/GillesArcas/numsed>
<https://github.com/shinh/sedlisp>

# Graph Rewriting

See also note on Graph theory.

"graph transformation" is also a keyword.
<https://en.wikipedia.org/wiki/Graph_rewriting>
Handbook <https://www.worldscientific.com/worldscibooks/10.1142/3303#t=aboutBook>
Graph rewriting is a mad old field
Termgraph <http://www.termgraph.org.uk/>

AGG, GROOVE, GP, PORGY, PROGRES,

Compiling to Graph combinators
CHR is a ready to go (destructive) graph rewriting system

Terms are graphs. So are DAGs
Graphs may come in ported vs non ported forms. Are edges equivalent?

### Groove

Pretty cool video
ideas:
Ski rewriting
optimal lambda graphs
hash consing
bisimular reduction?
egraph rewriting

### CHR

```prolog
%re
:- use_module(library(chr)).
:- initialization(main,main).
%:- chr_constraint s/0, s/1, s/2, i/0, i/1, k/0, k/1, k/2.

:- chr_constraint ap/3.

%flat(A + B,AB) <=> plus(A,B,C), flat(A), flat(B).
%flat(s(I,J)) <=> {gensym(X), s(I,J,)

main() :- print("hello"), term(s(i)).

term(ap(X,Y), Id) :- gensym(Id), term(X, XId), term(Y,YId), ap(XId, YId, Id).

ap(i, X, Id) <=> X = Id. %?
ap(k, X, KX), ap(KX, Y, KXY) <=> ?


/*
term(i, Id) :- gensym(Id), i(Id).
term(i(X), Id) :- gensym(Id), term(X, XId), i(XId, Id).
term(k, Id) :- gensym(Id), k(Id).
term(k(X), Id) :- gensym(Id), term(X, XId), k(XId, Id), 
term(k(X,Y), Id) :- gensym(Id), term(X, XId), term(Y, YId), k(XId, YId, Id). 
term(s, Id) :- gensym(Id), s(Id).
term(s(X), Id) :- gensym(Id), term(X, XId), s(XId, Id), 
term(s(X,Y), Id) :- gensym(Id), term(X, XId), term(Y, YId), s(XId, YId, Id). 



ite()
proj()
proj()
add(x,y,z)
*/
```

```

region(Id). % ~ blocks
cfg_edge(Id1,Id2). %  edges between blocks.
add(X,Y,Z) % dataflow edge
data_region(Z, R) % what region data calculation is in. optional
phi(X,Y,Z) % phi
ite(InReg, Data, ThenReg, ElseRegion, )


```

A cool key trick is fork and join nodes

Hash consing on a graph

```prolog
%re
:- use_module(library(chr)).
:- initialization(main,main).
:- chr_constraint lit/2, add/3, var/2, split/3, fresh/1.


dedup @ var(X,N) \ var(X,N) <=> true. 
dedupadd @ add(X,Y,Z) \ add(X,Y,Z) <=> true. 

% also congruence. Split could be called Eq
share @ var(X,N), var(X,M), fresh(P) <=> P1 is P + 1 | fresh(P1), var(X,P), split(P,N,M).
shareadd @ add(X,Y,Z), add(X,Y,Z1), fresh(P) <=> P1 is P + 1 | fresh(P1), add(X,Y,P), split(P,Z,Z1).


norm1 @ split(N,Y,_) \ add(X,Y,Z)  <=> add(X,N,Z).
norm2 @ split(N,_,Y) \ add(X,Y,Z)  <=> add(X,N,Z).
norm3 @ split(N,X,_) \ add(X,Y,Z)  <=> add(N,Y,Z).
norm4 @ split(N,_,X) \ add(X,Y,Z)  <=> add(N,Y,Z).

% hmm. This is becoming an egraph
% var(X,N) \ var(X,M) <=> link(N,M)
% different style. In the split style, everything has one port connection, which is nice.

% plus other ways of hooking up
norm_share % add(X,Y,Z), add(X1,Y1,Z1), share(X0, X, X1), share(Y0, Y, Y1), fresh(P) <=>
  P1 is P + 1 | add(X0,Y0,P), share(P, Z, Z1).

% share is commutative. so always build and use it in pairs?
% share(Z,X,Y) \ share(Z,Y,X)
% if we had more share, it would also become apparent that share is associative.

% X + Y -> Y + X as an egraph rule.
% add_comm @ add(X,Y,Z) <=> add(X,Y,Z1), add(Y,X,Z2), join(Z1,Z2,Z)



main() :- 
% two copies of x + y
var(x,1),
var(y,2),
add(1,2,3),

var(x,4),
var(y,5),
add(4,5,6),
fresh(7),
chr_show_store(true).

```

## Term Indexing

See automated theorem proving.

## Order Sorted Logic

# Systems

## Maude

<https://github.com/fadoss/umaudemc> unified model checking tool

<https://github.com/hwayne/lets-prove-leftpad/tree/master/maude> proving leftpad in maude

<https://github.com/SRI-CSL/Maude/tree/master/src/Interface> Interfaces

<https://github.com/SRI-CSL/Maude/blob/master/src/Main/prelude.maude> prelude

[Programming and Symbolic Computation in Maude 2019](https://arxiv.org/pdf/1910.08416.pdf)

[Bool]
looks like maude has reflective reasoning

polymorphic operators. Huh

attributes
memo - memozie the result
otherwise attribute
print

a matching equation

load
reduce in MYMOD
sort A.
subsort A < B.

```
fmod MyNat is
    sort Nat .
    op zero : -> Nat .
    op s_ : Nat -> Nat .
    op _+_ : Nat Nat -> Nat .
    vars N M : Nat .
    eq zero + N = N .
    eq (s N) + M = s (N + M) .
endfm 
```

<http://maude.cs.illinois.edu/w/index.php/Some_Papers_on_Maude_and_on_Rewriting_Logic> papers

Maude formal environment
 coherence, temrination,
 CETA library

 full maude is a seperate library thing?

 Debugger. That's interesting. Have it pause at each action?
 Ematching quantifier logging done right

 search command, that's cool.
 Takes pattern
 Search types.

 red in STRING : "hello" + "world".

 nonexec eq

 ceq cmb commands for conditional equation and conditional membership
 We can easily enulate these.

(relation is-zero Zero)

I feel like catlab ought to be trivially encodable into this system
Brutal.

[Maude as a Library: An Efficient All-Purpose Programming Interface](https://link.springer.com/chapter/10.1007/978-3-031-12441-9_14)
<https://github.com/fadoss/maude-bindings>
<https://fadoss.github.io/maude-bindings/>

[Pure Type Systems in Rewriting Logic: Specifying Typed Higher-Order Languages in a First-Order Logical Framework](https://courses.engr.illinois.edu/cs522/sp2016/PureTypeSystemsInRewritingLogic.pdf)

frozenness. could frozen survive rebuilding? survive hash consing?
[20 years of rewriting logic](https://www.sciencedirect.com/science/article/pii/S1567832612000707)

[Programming and symbolic computation in Maude 2020](https://www.sciencedirect.com/science/article/am/pii/S2352220818301135)
[Theorem Proving for Maude Specifications Using Lean](https://link.springer.com/chapter/10.1007/978-3-031-17244-1_16)

<https://fadoss.github.io/maude-bindings/>

```python
import maude
maude.init()
m = maude.getModule('NAT')
t = m.parseTerm('2 * 3')
t.reduce()
print(t)x
```

[Context-sensitive Rewriting Lucas](https://www.researchgate.net/publication/341029369_Context-Sensitive_Rewriting)

There is a sense that we've already screwed up context even before we've done anything equational just because of hash consing. Hash consing makes trees into dags and now terms are not in unique contexts.
Context tagging is a way to undo or prevent work that hash consing does.
Maybe rebuilding and hash consing are a kind of rewriting step and therefore may need to be activated only in certain circumstances

TPDB format for termination includes context sensitive anotations
it affects termination, so that makes sense.

Memo - can mark terms as memo so they memoize the normal form they write to.

OPerator strategires - can mark which arguments must be evaluated before the total operator is evaluated. Functional modules only

Frozen - can mark whether whole subterms are frozen. Is this that different?

System modules vs functional modules. System modules specify concurrent rewrite systems. Functional modules are assumed church rosser and terminating

<https://fadoss.github.io/strat-examples/>

rewriting graphs can be model checked with respect to ltl formula. That's cool

<http://maude.cs.illinois.edu/w/images/0/0f/BMgrt_2003.pdf> proof system

<http://maude.cs.uiuc.edu/maude1/tutorial/> tutorial for maude exampls

```
fmod A-GRAPH is
   sorts Edge Node .
   ops n1 n2 n3 n4 n5 : -> Node .
   ops a b c d e f : -> Edge .
   ops source target : Edge -> Node .

   eq source(a) = n1 .  eq target(a) = n2 .
   eq source(b) = n1 .  eq target(b) = n3 .
   eq source(c) = n3 .  eq target(c) = n4 .
   eq source(d) = n4 .  eq target(d) = n2 .
   eq source(e) = n2 .  eq target(e) = n5 .
   eq source(f) = n2 .  eq target(f) = n1 .
endfm
```

path example. Shows  the subsorting technique. In the manual they show some weird "kind" example.

```
fmod PATH is
   protecting NAT .
   protecting A-GRAPH .

   sorts Path Path? .
   subsorts Edge < Path < Path? .
   op _;_ : Path? Path? -> Path? [assoc] .
   ops source target : Path -> Node .
   op length : Path -> Nat .

   var E : Edge .
   var P : Path .

   cmb (E ; P) : Path if target(E) == source(P) .

   eq source(E ; P) = source(E) .
   eq target(P ; E) = target(E) .
   eq length(E) = s(0) .
   eq length(E ; P) = s(0) + length(P) .
endfm
```

This is cool. It's sequent proof search

```
mod SEQUENT-RULES-PROP-LOG is
  protecting PROP-LOG .
  sort Configuration .
  subsort Sequent < Configuration .
  op empty : -> Configuration .
  op __ : Configuration Configuration -> Configuration
                                         [assoc comm id: empty] .
  vars R S : PropSet .
  vars P Q : Prop .

  rl [Identity] :        empty
                    => -----------
                       |- (P, ~ P) .

  rl [Cut] :           |- (R, P) |- (S, ~ P)
                    => ---------------------
                            |- (R, S) .

  rl [Weakening] :       |- R
                    => ---------
                       |- (R, P) .

  rl [Disjunction] :     |- (R, P, Q)
                    => ----------------
                       |- (R, (P \/ Q)) .

  rl [Conjunction] :   |- (R, P) |- (S, Q)
                    => -------------------
                       |- (R, S, (P /\ Q)) .

  rl [Truth] :          empty
                    => -------
                        |- tt .
endm
```

manual rule application <https://github.com/fadoss/maude-bindings/blob/master/tests/python/apply.py>

### Unification

```python
# https://github.com/fadoss/maude-bindings/blob/master/tests/python/unify.py
import maude
import itertools

maude.init(advise=False)

##### From Maude 3.1 manual, §13.4

maude.input('''fmod UNIFICATION-EX1 is
 protecting NAT .
 op f : Nat Nat -> Nat .
 op f : NzNat Nat -> NzNat .
 op f : Nat NzNat -> NzNat .
endfm''')

uex1 = maude.getModule('UNIFICATION-EX1')

uex1_t1 = uex1.parseTerm('f(X:Nat, Y:Nat) ^ B:NzNat')
uex1_t2 = uex1.parseTerm('A:NzNat ^ f(Y:Nat, Z:Nat)')

print('Unifiers for', uex1_t1, 'and', uex1_t2)

for unifier in uex1.unify([(uex1_t1, uex1_t2)]):
 print('Unifier', unifier)
 print('X =', unifier.find('X'))
 print('T =', unifier.find('T'))
 print('B:NzNat =', unifier.find('B', uex1.findSort('NzNat')))
 print('X:NzNat =', unifier.find('X', uex1.findSort('NzNat')))

 print('σ({}) = {}'.format(uex1_t1, unifier.instantiate(uex1_t1)))
 print('σ(3) =', unifier.instantiate(uex1.parseTerm('3')))
```

### Equation Search

```python
import maude

test_mod = """
  mod SEARCH is
    sort Num .
 
    op _+_ : Num Num -> Num .
    ops a b c d e f : -> Num .

    vars n m p  : Num .
    rl [lassoc] : (n + m) + p => n + (m + p) .
    rl [rassoc] : n + (m + p) => (n + m) + p .
    rl [comm] : n + m => m + n .

  endm"""
maude.init()
maude.input(test_mod)
mod = maude.getModule('SEARCH')

t = mod.parseTerm("(a + b) + c")
# t.search takes in parameters. I thnk the first one is no step, one step, *step
for (sol, subst, seq, steps) in t.search(5, mod.parseTerm("c + (b + n)"), depth=2):
    path = seq()
    print(subst) # n = a
    print(path) # an interleaved list of term and rule.

```

I do feel like there is way to hack cost into this. Define cost via computational equations... Hmm.

Ok, so an equality condition on the cost function

```python
import maude

test_mod = """
  mod SEARCH is
    protecting NAT .
    sort Num .
 
    op plus : Num Num -> Num .
    op neg : Num -> Num .
    ops a b c d e f z : -> Num .

    vars n m p  : Num .
    rl [lassoc] : plus(plus(n, m), p) => plus(n,  plus(m , p)) .
    rl [rassoc] : plus(n,  plus(m , p))  => plus(plus(n, m), p) .
    rl [comm] : plus(n , m) => plus(m , n) .
    eq plus(n, neg(n)) = z .
    eq plus(n, z) = n . 

    op cost : Num -> Nat .
    eq cost(plus(n,m)) = cost(n) + cost(m) .
    eq cost(a) = 1 .
    eq cost(b) = 1 .
    eq cost(c) = 1 .
    eq cost(z) = 1 .

  endm"""
maude.init()
maude.input(test_mod)
mod = maude.getModule('SEARCH')

#t = mod.parseTerm("plus(plus(a , b), c)")
t = mod.parseTerm("plus(a,plus(b , neg(a)))")
# t.search takes in parameters. I thnk the first one is no step, one step, *step
#for (sol, subst, seq, steps) in t.search(5, mod.parseTerm("plus(c, plus(b , n))"), depth=2):
n = mod.parseTerm("n ")
import pprint
for (sol, subst, seq, steps) in t.search(maude.ANY_STEPS, n , condition=[maude.EqualityCondition(mod.parseTerm("cost(n)"),mod.parseTerm("1") )], depth=3):
    path = seq()
    print(subst) # n = a
    pprint.pprint(path) # an interleaved list of term and rule.

```

### Built ins

Chspter 8 of manual

- Rat
- Float
- string
- list
- sets
- Map
-

```python
import maude


maude.init()
mod = maude.getModule('NAT')
def term(s):
  t = mod.parseTerm(s)
  t.reduce()
  print(t)

term("max(10,0)")
term("10 + 2 * 3")
term("s s 0")

mod = maude.getModule('BOOL')
mod = maude.getModule('INT')
mod = maude.getModule('STRING')

term("length(\"hello\")")
term(")
```

### Category

```python
import maude

test_mod = """
  fmod TESTMOD is
    sort Term .
    op foo : Term -> Term .
    ops x bar : -> Term .
    eq foo(x) = bar .
  endfm"""


test_mod = """
  fmod CATEGORY is
    sort Ob Morph Morph? TYPE .
    subsort Morph < Morph? .
    op comp : Morph? Morph? -> Morph? . *** [assoc]
    op id : Ob -> Morph .
    ops cod dom : Morph -> Ob .
    op hom : Ob Ob -> TYPE .
    op typ : Morph -> TYPE . 
    vars f g h : Morph .
    vars a b c : Ob .
    *** eq comp(comp(f,g), h) = comp(f, comp(g, h)) . 
    eq comp(id(a),f) = f .
    eq comp(f, id(a)) = f .
    cmb comp(f,g) : Morph if hom(a,b) := typ(f) /\ hom(b,c) := typ(g)  . 
    *** cmb comp(f,g) : Morph if dom(f) = cod(g) .

  endfm"""
maude.init()
maude.input(test_mod)
mod = maude.getModule('CATEGORY')

t = mod.parseTerm("comp(id(a),comp(id(a), id(a)))")
print(t.reduce())
print(t)

```

"matching equations" are multipatterns rather than guards

## Eqlog

[CATEGORY-BASED SEMANTICS FOR EQUATIONAL AND CONSTRAINT LOGIC PROGRAMMING](https://www.cs.ox.ac.uk/files/3444/PRG116.pdf)
Goguen Meseguer

## K

```bash
rm -rf /tmp/ktest
mkdir /tmp/ktest && cd /tmp/ktest
echo "
module LESSON

  syntax Color ::= Yellow() | Blue()
  syntax Fruit ::= Banana() | Blueberry()
  syntax Color ::= colorOf(Fruit) [function]

  rule colorOf(Banana()) => Yellow()
  rule colorOf(Blueberry()) => Blue()

endmodule
" > lesson.k
kompile lesson.k
krun -cPGM='colorOf(Banana())'
```

<https://dl.acm.org/doi/pdf/10.1145/3314221.3314601> instruction semantics for x86 in K
<https://kframework.org/index.html>
intepreter, compiler, formal prover thing
<http://www.matching-logic.org/>

<https://kframework.org/faq/>
Systems to compare to according to them
Redex, Maude, Spoofax, OTT, [Rascal](https://www.rascal-mpl.org/),  ATL and model driven

[popl : matching logic: foundations of K framework](https://www.youtube.com/watch?v=Awsv0BlJgbo&ab_channel=ACMSIGPLAN)

[Generating Proof Certificates for a Language-Agnostic Deductive Program Verifier](https://xchen.page/assets/pdf/LCT+23-paper.pdf) encpdong matchng loic into metamath?

[K vs. Coq as Language Verification Frameworks](https://runtimeverification.com/blog/k-vs-coq-as-language-verification-frameworks-part-1-of-3/)

## spoofax
<https://spoofax.dev/background/stratego/strategic-rewriting/term-rewriting/>

strategic rewriting

# Other Systems

Pure
Obj
ASF+SDF <https://homepages.cwi.nl/~paulk/publications/FASE99.html/node5.html> (superseced by Stratego and Rascal)
ELAN (superseded by Tom <http://tom.loria.fr/wiki/index.php/Main_Page> )
mcrl2

Strategy
Stratgo

PLT redex - context sensitive rewriting?

<https://link.springer.com/chapter/10.1007/978-3-030-17502-3_6> term rewriting engine competiton
rule engine competition benchamrks
<https://hal.inria.fr/hal-01883212/document>
<https://rec.gforge.inria.fr/> but it isn't responding
<https://sourcesup.renater.fr/scm/viewvc.php/rec/>

[dedukti term rewritng engine](https://drops.dagstuhl.de/opus/volltexte/2020/12357/pdf/LIPIcs-FSCD-2020-35.pdf)

[cafeobj](https://cafeobj.org/intro/en/)

<https://redex.racket-lang.org/>

[cafeobj](https://cafeobj.org/intro/en/)

RMT - rewriting modfulo theories <https://profs.info.uaic.ro/~stefan.ciobaca/inriaparis2017/pres.pdf> <https://github.com/ciobaca/rmt/>

[](https://github.com/joshrule/term-rewriting-rs)

<https://github.com/comby-tools/comby> comby a rewriting sed tool for languages. Odd.

# TRaaT Rust

<https://www21.in.tum.de/~nipkow/TRaAT/programs/>

```rust
// https://www21.in.tum.de/~nipkow/TRaAT/programs/trs.ML
type VName = (String, i32);

#[derive(PartialEq, Eq, Clone, Debug)]
enum Term {
    V(VName),
    T(String, Vec<Term>),
}

// indom: Checks if a vname is in a substitution
fn indom(x: &VName, s: &[(VName, Term)]) -> bool {
    s.iter().any(|(y, _)| x == y)
}

// app: Applies a substitution to a vname
fn app(s: &[(VName, Term)], x: &VName) -> Term {
    for (y, t) in s {
        if x == y {
            return t.clone();
        }
    }
    panic!("vname not found in substitution");
}

// lift: Applies a substitution to a term
fn lift(s: &[(VName, Term)], term: &Term) -> Term {
    match term {
        Term::V(x) => {
            if indom(x, s) {
                app(s, x)
            } else {
                term.clone()
            }
        }
        Term::T(f, ts) => Term::T(f.clone(), ts.iter().map(|t| lift(s, t)).collect()),
    }
}

// occurs: Checks if a vname occurs in a term
fn occurs(x: &VName, term: &Term) -> bool {
    match term {
        Term::V(y) => x == y,
        Term::T(_, ts) => ts.iter().any(|t| occurs(x, t)),
    }
}

fn solve(mut eqs: Vec<(Term, Term)>, mut s: Vec<(VName, Term)>) -> Option<Vec<(VName, Term)>> {
    while let Some((lhs, rhs)) = eqs.pop() {
        match (lhs, rhs) {
            (Term::V(x), t) | (t, Term::V(x))  => {
              if Term::V(x.clone()) != t {
                elim(&x, &t, &mut eqs, &mut s)?;
              }
            }
            (Term::T(f, ts), Term::T(g, us)) if f == g => {
                eqs.extend(ts.into_iter().zip(us));
            }
            _ => return None,
        }
    }
    Some(s)
}

fn elim(
    x: &VName,
    t: &Term,
    eqs: &mut Vec<(Term, Term)>,
    s: &mut Vec<(VName, Term)>,
) -> Option<()> {
    if occurs(x, t) {
        None
    } else {
        let xt_subst = vec![(x.clone(), lift(s, t))];
        eqs.iter_mut()
            .for_each(|eq| *eq = (lift(&xt_subst, &eq.0), lift(&xt_subst, &eq.1)));
        s.iter_mut()
            .for_each(|sub| *sub = (sub.0.clone(), lift(&xt_subst, &sub.1)));
        s.push((x.clone(), t.clone()));
        Some(())
    }
}

// unify: Tries to find a unifying substitution for two terms
fn unify(t1: &Term, t2: &Term) -> Option<Vec<(VName, Term)>> {
    solve(vec![(t1.clone(), t2.clone())], vec![])
}

// matchs: Tries to match two terms under a substitution
fn matchs(mut eqs: Vec<(Term, Term)>, mut s: Vec<(VName, Term)>) -> Option<Vec<(VName, Term)>> {
    while let Some((lhs, rhs)) = eqs.pop() {
        match (&lhs, &rhs) {
            (Term::V(x), t) => {
                if indom(x, &s) {
                    if app(&s, x) == *t {
                        continue;
                    } else {
                        return None;
                    }
                } else {
                    s.push((x.clone(), t.clone()));
                }
            }
            (Term::T(f, ts), Term::T(g, us)) if f == g => {
                eqs.extend(ts.iter().cloned().zip(us.iter().cloned()));
            }
            _ => return None,
        }
    }
    Some(s)
}

// match_term: Wrapper for matchs to match a single term pair
fn match_term(pat: &Term, obj: &Term) -> Option<Vec<(VName, Term)>> {
    matchs(vec![(pat.clone(), obj.clone())], vec![])
}

const NORM: &str = "normal form";

// rewrite: Attempts to rewrite a term using a list of rewrite rules
fn rewrite(rules: &[(Term, Term)], term: &Term) -> Option<Term> {
    rules.iter().find_map(|(l, r)| {
        match_term(l, term)
            .map(|subst| lift(&subst, r))
    }).or_else(|| None)
}

// norm: Normalizes a term by repeatedly applying rewrite until no more rules can be applied
fn norm(rules: &[(Term, Term)], term: &Term) -> Term {
    let mut current_term = term.clone();
    while let Some(new_term) = rewrite(rules, &current_term) {
        if new_term == current_term {
            break;
        }
        current_term = new_term;
    }
    current_term
}


fn main() {
    println!("Hello, world!");
}

```

# 2020 Term rewritng notes

2020-12-07

<https://www.regular-expressions.info/recurse.html>

2020-07-17 from "Bash"
There is a thing I've heard that bash and piping is shockingly performant for some tasks. Stream processing and stuff.

You can kind of get database operations  

- wc - word count
- grep
- head
- sort - can sort of columns?
- uniq
- awk - all kinds of crap
- join
- seq 1 100

<http://williamslab.bscb.cornell.edu/?page_id=287>

Gnu parallel [https://www.youtube.com/watch?v=OpaiGYxkSuQ&list=PL284C9FF2488BC6D1&index=2&t=0s](https://www.youtube.com/watch?v=OpaiGYxkSuQ&list=PL284C9FF2488BC6D1&index=2&t=0s)

2020-08-10

Knuth Bendix completion is interesintg. It solves the word problem

String rewriting can be use to normalize finitely presented categories sometimes. If we list the generating morphisms and the base equalities of composition, knuth bendix may be able to generate the closure, which we can use to figure out if two morphisms are the same with a guarantee.

String matching algorithms are relevant.

The Boyer Moore algorithm makes some jumps based on comparisons you've already made. These jumps can be calculated based on properties of the pattern

[https://www.sciencedirect.com/science/article/pii/S1567832610001025](https://www.sciencedirect.com/science/article/pii/S1567832610001025) - efficiency issues in the kbmag procedure. Describes using suffix trees to find critical pairs

[https://gap-packages.github.io/kbmag/doc/chap1.html#X7DFB63A97E67C0A1](https://gap-packages.github.io/kbmag/doc/chap1.html#X7DFB63A97E67C0A1) KBMAG gap package. Accessible through GAP.jl

Are the SKI combinators expressible in string rewriting? They have a tree structure and are expressed as such ordinarily. Maybe parenthesis can be used as inhibitors? Or we could have a moving evaluation marker?

    <code>(S) -> S
    (K) -> K
    (I) -> I
    IK -> K
    IS -> S
    II -> I
    ... all concrete
    Sxyz = xz(yz)
    
    </code>

Building a turing machien out of a string rewrite system. Have special characters represent the state. and have the patterns include the surrounding context. Enumerate all the characters in state and tape characters.

    <code>aSb -> acS
    aSb -> Scb</code>

Computational group theory is a thing.

Finite categories which have both finite morphisms and finite objects are approachable. It is clear that most questions one might ask about a finite category is approachable by brute force or maybe by encoding to some graph problems or SAT problem.

Finitely presented categories are the next up the chain in complexity. In this case we take a free category generated by some morphisms and some equations identifying certain composition patterns. It is less clear whether natural questions are decidable or not.

What questions do we care about:

- Are two morphisms expressions equal?
- Produce a morphism from object A to B
- Confirm some mapping is a Functor
- Confirm some functor mapping is a natural transformation.

It is my belief that some questions about these can

The next level of category one might want to talk about is one for which you have guaranteed constructions, such as cartesian, closed, dagger, monoidal, etc. I'm not sure which of these qualifiers are compatible with being finite. [https://arxiv.org/abs/0908.3347](https://arxiv.org/abs/0908.3347)  To me, this feels analogous to being able to work with terms rather than just strings.

# Misc

[Gershom Bazerman on "Homological Computations for Term Rewriting Systems"](https://www.youtube.com/watch?v=WdawrT-6Qzk&ab_channel=PapersWeLove)

[rewritng modulo SMT and open system analysis](https://shemesh.larc.nasa.gov/fm/papers/wrla2014-draft.pdf)

[tools in term rewriting for education](https://arxiv.org/pdf/2002.12554.pdf)

<http://www.cs.tau.ac.il/~nachum/papers/klop.pdf> - Klop review on term Rewriting. Cody's RG pick

[A Taste of Rewrite Systems](https://homepage.divms.uiowa.edu/~fleck/181content/taste-fixed.pdf)

<http://cl-informatik.uibk.ac.at/teaching/ws20/trs/content.php> term rewriting course mitteldorp

[code generation via hogher order rewrite systems](https://link.springer.com/chapter/10.1007/978-3-642-12251-4_9)
