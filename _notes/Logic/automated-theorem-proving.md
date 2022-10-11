---
layout: post
title: Automated Theorem Proving
---

See also notes on:
- SMT
- prolog
- datalog


- Vampire
- E Prover https://wwwlehre.dhbw-stuttgart.de/~sschulz/E/E.html
- Zipperposition

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


[vampire tutorial](https://github.com/vprover/ase17tutorial)

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

# Methodology 
## Unification
Two way matching.
Is there a substitution for variables that solves an equation. Yes

Anti-unification is an interesting topic. Generalization.
## Resolution
Put clauses in cnf. Each clause is an `\/` of positive and negative atoms.
Take two clauses that have matching (unifiable) positive and negative pieces 

Hyperresolution

## Subsumption
Cleaning out the database.

given C(X) ,  C(a) is redundant (subsumed). You can remove it from clause database. A question is how to do this quickly. See Term indexing.

## Paramodulation
https://math.stackexchange.com/questions/865562/a-simple-yet-non-superficial-explanation-of-what-paramodulation-means-in-the

Paramodulation is dealing with equality pieces in clauses.
http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.34.9958&rep=rep1&type=pdf

# Term Indexing
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


# Misc
Set of Support
prio

- <https://www.ncbi.nlm.nih.gov/pmc/articles/PMC7324010/> Teaching Automated Theorem Proving by Example: PyRes 1.2
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


[auto2](https://arxiv.org/pdf/1605.07577.pdf) interesting system that combines egraphs and sturation proving https://github.com/bzhan/auto2 he alos mentions gowers as influence