---
date: 2024-03-11
title: "Termination Checkers: Playing with AProVE"
---

An interesting category of solver that is not discussed much is that of termination checkers.

I've been looking into this recently because I'd like to discharge the well formedness of recursive definitions in my very unbaked python ITP [knuckledragger](https://github.com/philzook58/knuckledragger) by just calling one of these solvers.

It's kind odd that lots of people just dump onto SMT solvers but most systems I know of that have termination questions don't dump onto these specialized termination solvers, they roll their own. Perhaps there is a good reason.

# Let's Try It Out

You can dig into the [termination competition](https://termination-portal.org/wiki/Termination_Competition) website ([overview paper](https://link.springer.com/chapter/10.1007/978-3-030-17502-3_10)).
I made a copy of the competition repo that has the more readable `.trs` format here <https://github.com/philzook58/TPDB> <https://termination-portal.org/wiki/TPDB> I haven't found anything that much juicier than `foo bar biz` rewrite systems in here so far.

Some of the solvers I see in the competition are

- AProVE <https://aprove.informatik.rwth-aachen.de/interface>
- NaTT <https://www.trs.cm.is.nagoya-u.ac.jp/NaTT/>
- ttt <http://cl-informatik.uibk.ac.at/ttt2/>
- muterm <http://zenon.dsic.upv.es/muterm/>

AProVe is consistently highly ranked and has lots of features. It appears to be available as a [java jar](https://github.com/aprove-developers/aprove-releases/releases) but is closed source.
You can find web demo versions of aprove here <https://aprove.informatik.rwth-aachen.de/interface> which is useful for playing around and seeing the input formats. I pulled examples below from these.

NaTT is open source and apparently has a very high termination power to complexity ratio. It implements only one good generic termnation ordering, weight path ordering. (I needed to install ocamlgraph, xml-light and then rename MYXML.ml to myXML.ml to get it compiled)

There is a proof format from these solvers that can be checked via the CeTA Isabelle system <http://cl-informatik.uibk.ac.at/isafor/>. It's xml. Even understanding this proof format seems like quite an undertaking to my eye. See also Coq CoLor/Rainbow, CiME/Coccinelle  <http://cl-informatik.uibk.ac.at/software/cpf/> describes an input format and proof format

Here's a Peano plus.

```python
%%file /tmp/ex.trs
(VAR x y)
(RULES
    plus(0,y) -> y
    plus(s(x),y) -> s(plus(x,y))
)
```

    Writing /tmp/ex.trs

```python
! java -ea -jar ~/Documents/solvers/aprove.jar -p plain -m wst /tmp/ex.trs
```

    YICES stderr: yices: invalid option: -e
    YICES stderr: Try 'yices --help' for more information
    YICES stderr: yices: invalid option: -e
    YICES stderr: Try 'yices --help' for more information
    YES
    proof of /tmp/ex.trs
    # AProVE Commit ID: 8b4ec3a549e709bdb38c8a065b8ff21f2ca0de28 jan-christoph 20240203 unpublished dirty
    
    
    Termination w.r.t. Q of the given QTRS could be proven:
    
    (0) QTRS
    (1) QTRSRRRProof [EQUIVALENT, 45 ms]
    (2) QTRS
    (3) QTRSRRRProof [EQUIVALENT, 0 ms]
    (4) QTRS
    (5) RisEmptyProof [EQUIVALENT, 0 ms]
    (6) YES
    
    
    ----------------------------------------
    
    (0)
    Obligation:
    Q restricted rewrite system:
    The TRS R consists of the following rules:
    
       plus(0, y) -> y
       plus(s(x), y) -> s(plus(x, y))
    
    Q is empty.
    
    ----------------------------------------
    
    (1) QTRSRRRProof (EQUIVALENT)
    Used ordering:
    Polynomial interpretation [POLO]:
    
       POL(0) = 2
       POL(plus(x_1, x_2)) = 2*x_1 + x_2
       POL(s(x_1)) = x_1
    With this ordering the following rules can be removed by the rule removal processor [LPAR04] because they are oriented strictly:
    
       plus(0, y) -> y
    
    
    
    
    ----------------------------------------
    
    (2)
    Obligation:
    Q restricted rewrite system:
    The TRS R consists of the following rules:
    
       plus(s(x), y) -> s(plus(x, y))
    
    Q is empty.
    
    ----------------------------------------
    
    (3) QTRSRRRProof (EQUIVALENT)
    Used ordering:
    Polynomial interpretation [POLO]:
    
       POL(plus(x_1, x_2)) = 2*x_1 + x_2
       POL(s(x_1)) = 1 + x_1
    With this ordering the following rules can be removed by the rule removal processor [LPAR04] because they are oriented strictly:
    
       plus(s(x), y) -> s(plus(x, y))
    
    
    
    
    ----------------------------------------
    
    (4)
    Obligation:
    Q restricted rewrite system:
    R is empty.
    Q is empty.
    
    ----------------------------------------
    
    (5) RisEmptyProof (EQUIVALENT)
    The TRS R is empty. Hence, termination is trivially proven.
    ----------------------------------------
    
    (6)
    YES

```python
! ~/Documents/solvers/NaTT/bin/NaTT.exe /tmp/ex.trs # woops. i guess I need the xml format. yuck. forget that.
```

    Fatal error: exception Xml_light_errors.Xml_error(_)

This is what non termination looks like. This is a cogent definition of an infinite stream of 0, but certainly not terminating.

```python
%%file /tmp/nonterm.trs
(VAR x y)
(RULES
    zeros -> cons(0, zeros)
)

```

    Writing /tmp/nonterm.trs

```python
! java -ea -jar ~/Documents/solvers/aprove.jar -p plain -m wst /tmp/nonterm.trs
```

    YICES stderr: yices: invalid option: -e
    YICES stderr: Try 'yices --help' for more information
    YICES stderr: yices: invalid option: -e
    YICES stderr: Try 'yices --help' for more information
    NO
    proof of /tmp/nonterm.trs
    # AProVE Commit ID: 8b4ec3a549e709bdb38c8a065b8ff21f2ca0de28 jan-christoph 20240203 unpublished dirty
    
    
    Termination w.r.t. Q of the given QTRS could be disproven:
    
    (0) QTRS
    (1) Overlay + Local Confluence [EQUIVALENT, 0 ms]
    (2) QTRS
    (3) DependencyPairsProof [EQUIVALENT, 7 ms]
    (4) QDP
    (5) UsableRulesProof [EQUIVALENT, 0 ms]
    (6) QDP
    (7) QReductionProof [EQUIVALENT, 0 ms]
    (8) QDP
    (9) NonTerminationLoopProof [COMPLETE, 0 ms]
    (10) NO
    
    
    ----------------------------------------
    
    (0)
    Obligation:
    Q restricted rewrite system:
    The TRS R consists of the following rules:
    
       zeros -> cons(0, zeros)
    
    Q is empty.
    
    ----------------------------------------
    
    (1) Overlay + Local Confluence (EQUIVALENT)
    The TRS is overlay and locally confluent. By [NOC] we can switch to innermost.
    ----------------------------------------
    
    (2)
    Obligation:
    Q restricted rewrite system:
    The TRS R consists of the following rules:
    
       zeros -> cons(0, zeros)
    
    The set Q consists of the following terms:
    
       zeros
    
    
    ----------------------------------------
    
    (3) DependencyPairsProof (EQUIVALENT)
    Using Dependency Pairs [AG00,LPAR04] we result in the following initial DP problem.
    ----------------------------------------
    
    (4)
    Obligation:
    Q DP problem:
    The TRS P consists of the following rules:
    
       ZEROS -> ZEROS
    
    The TRS R consists of the following rules:
    
       zeros -> cons(0, zeros)
    
    The set Q consists of the following terms:
    
       zeros
    
    We have to consider all minimal (P,Q,R)-chains.
    ----------------------------------------
    
    (5) UsableRulesProof (EQUIVALENT)
    As all Q-normal forms are R-normal forms we are in the innermost case. Hence, by the usable rules processor [LPAR04] we can delete all non-usable rules [FROCOS05] from R.
    ----------------------------------------
    
    (6)
    Obligation:
    Q DP problem:
    The TRS P consists of the following rules:
    
       ZEROS -> ZEROS
    
    R is empty.
    The set Q consists of the following terms:
    
       zeros
    
    We have to consider all minimal (P,Q,R)-chains.
    ----------------------------------------
    
    (7) QReductionProof (EQUIVALENT)
    We deleted the following terms from Q as each root-symbol of these terms does neither occur in P nor in R.[THIEMANN].
    
       zeros
    
    
    ----------------------------------------
    
    (8)
    Obligation:
    Q DP problem:
    The TRS P consists of the following rules:
    
       ZEROS -> ZEROS
    
    R is empty.
    Q is empty.
    We have to consider all minimal (P,Q,R)-chains.
    ----------------------------------------
    
    (9) NonTerminationLoopProof (COMPLETE)
    We used the non-termination processor [FROCOS05] to show that the DP problem is infinite.
    Found a loop by semiunifying a rule from P directly.
    
    s = ZEROS evaluates to  t =ZEROS
    
    Thus s starts an infinite chain as s semiunifies with t with the following substitutions:
    * Matcher: [ ]
    * Semiunifier: [ ]
    
    --------------------------------------------------------------------------------
    Rewriting sequence
    
    The DP semiunifies directly so there is only one rewrite step from ZEROS to ZEROS.
    
    
    
    
    ----------------------------------------
    
    (10)
    NO

Consider this reformulation of plus. It does not terminate. Funny huh.

```python
%%file /tmp/ite.trs
(VAR x y)
(RULES
    ite(true, x,y) -> x
    ite(false,x,y) -> y
    pred(s(x)) -> x
    eq(x,x) -> true
    eq(s(x), s(y)) -> eq(x,y) 
    plus(x,y) -> ite(eq(x,0), y, s(plus(pred(x),y)))
)
```

    Overwriting /tmp/ite.trs

```python
! java -ea -jar ~/Documents/solvers/aprove.jar -p plain -m wst /tmp/ite.trs
```

    YICES stderr: yices: invalid option: -e
    YICES stderr: Try 'yices --help' for more information
    YICES stderr: yices: invalid option: -e
    YICES stderr: Try 'yices --help' for more information
    YICES stderr: yices: invalid option: -e
    YICES stderr: Try 'yices --help' for more information
    NO
    proof of /tmp/ite.trs
    # AProVE Commit ID: 8b4ec3a549e709bdb38c8a065b8ff21f2ca0de28 jan-christoph 20240203 unpublished dirty
    
    
    Termination w.r.t. Q of the given QTRS could be disproven:
    
    (0) QTRS
    (1) Overlay + Local Confluence [EQUIVALENT, 4 ms]
    (2) QTRS
    (3) DependencyPairsProof [EQUIVALENT, 0 ms]
    (4) QDP
    (5) DependencyGraphProof [EQUIVALENT, 0 ms]
    (6) AND
        (7) QDP
            (8) UsableRulesProof [EQUIVALENT, 0 ms]
            (9) QDP
            (10) QReductionProof [EQUIVALENT, 0 ms]
            (11) QDP
            (12) QDPSizeChangeProof [EQUIVALENT, 0 ms]
            (13) YES
        (14) QDP
            (15) UsableRulesProof [EQUIVALENT, 0 ms]
            (16) QDP
            (17) QReductionProof [EQUIVALENT, 0 ms]
            (18) QDP
            (19) UsableRulesReductionPairsProof [EQUIVALENT, 0 ms]
            (20) QDP
            (21) TransformationProof [EQUIVALENT, 0 ms]
            (22) QDP
            (23) TransformationProof [EQUIVALENT, 0 ms]
            (24) QDP
            (25) QReductionProof [EQUIVALENT, 0 ms]
            (26) QDP
            (27) NonTerminationLoopProof [COMPLETE, 0 ms]
            (28) NO
    
    
    ----------------------------------------
    
    (0)
    Obligation:
    Q restricted rewrite system:
    The TRS R consists of the following rules:
    
       ite(true, x, y) -> x
       ite(false, x, y) -> y
       pred(s(x)) -> x
       eq(x, x) -> true
       eq(s(x), s(y)) -> eq(x, y)
       plus(x, y) -> ite(eq(x, 0), y, s(plus(pred(x), y)))
    
    Q is empty.
    
    ----------------------------------------
    
    (1) Overlay + Local Confluence (EQUIVALENT)
    The TRS is overlay and locally confluent. By [NOC] we can switch to innermost.
    ----------------------------------------
    
    (2)
    Obligation:
    Q restricted rewrite system:
    The TRS R consists of the following rules:
    
       ite(true, x, y) -> x
       ite(false, x, y) -> y
       pred(s(x)) -> x
       eq(x, x) -> true
       eq(s(x), s(y)) -> eq(x, y)
       plus(x, y) -> ite(eq(x, 0), y, s(plus(pred(x), y)))
    
    The set Q consists of the following terms:
    
       ite(true, x0, x1)
       ite(false, x0, x1)
       pred(s(x0))
       eq(x0, x0)
       eq(s(x0), s(x1))
       plus(x0, x1)
    
    
    ----------------------------------------
    
    (3) DependencyPairsProof (EQUIVALENT)
    Using Dependency Pairs [AG00,LPAR04] we result in the following initial DP problem.
    ----------------------------------------
    
    (4)
    Obligation:
    Q DP problem:
    The TRS P consists of the following rules:
    
       EQ(s(x), s(y)) -> EQ(x, y)
       PLUS(x, y) -> ITE(eq(x, 0), y, s(plus(pred(x), y)))
       PLUS(x, y) -> EQ(x, 0)
       PLUS(x, y) -> PLUS(pred(x), y)
       PLUS(x, y) -> PRED(x)
    
    The TRS R consists of the following rules:
    
       ite(true, x, y) -> x
       ite(false, x, y) -> y
       pred(s(x)) -> x
       eq(x, x) -> true
       eq(s(x), s(y)) -> eq(x, y)
       plus(x, y) -> ite(eq(x, 0), y, s(plus(pred(x), y)))
    
    The set Q consists of the following terms:
    
       ite(true, x0, x1)
       ite(false, x0, x1)
       pred(s(x0))
       eq(x0, x0)
       eq(s(x0), s(x1))
       plus(x0, x1)
    
    We have to consider all minimal (P,Q,R)-chains.
    ----------------------------------------
    
    (5) DependencyGraphProof (EQUIVALENT)
    The approximation of the Dependency Graph [LPAR04,FROCOS05,EDGSTAR] contains 2 SCCs with 3 less nodes.
    ----------------------------------------
    
    (6)
    Complex Obligation (AND)
    
    ----------------------------------------
    
    (7)
    Obligation:
    Q DP problem:
    The TRS P consists of the following rules:
    
       EQ(s(x), s(y)) -> EQ(x, y)
    
    The TRS R consists of the following rules:
    
       ite(true, x, y) -> x
       ite(false, x, y) -> y
       pred(s(x)) -> x
       eq(x, x) -> true
       eq(s(x), s(y)) -> eq(x, y)
       plus(x, y) -> ite(eq(x, 0), y, s(plus(pred(x), y)))
    
    The set Q consists of the following terms:
    
       ite(true, x0, x1)
       ite(false, x0, x1)
       pred(s(x0))
       eq(x0, x0)
       eq(s(x0), s(x1))
       plus(x0, x1)
    
    We have to consider all minimal (P,Q,R)-chains.
    ----------------------------------------
    
    (8) UsableRulesProof (EQUIVALENT)
    As all Q-normal forms are R-normal forms we are in the innermost case. Hence, by the usable rules processor [LPAR04] we can delete all non-usable rules [FROCOS05] from R.
    ----------------------------------------
    
    (9)
    Obligation:
    Q DP problem:
    The TRS P consists of the following rules:
    
       EQ(s(x), s(y)) -> EQ(x, y)
    
    R is empty.
    The set Q consists of the following terms:
    
       ite(true, x0, x1)
       ite(false, x0, x1)
       pred(s(x0))
       eq(x0, x0)
       eq(s(x0), s(x1))
       plus(x0, x1)
    
    We have to consider all minimal (P,Q,R)-chains.
    ----------------------------------------
    
    (10) QReductionProof (EQUIVALENT)
    We deleted the following terms from Q as each root-symbol of these terms does neither occur in P nor in R.[THIEMANN].
    
       ite(true, x0, x1)
       ite(false, x0, x1)
       pred(s(x0))
       eq(x0, x0)
       eq(s(x0), s(x1))
       plus(x0, x1)
    
    
    ----------------------------------------
    
    (11)
    Obligation:
    Q DP problem:
    The TRS P consists of the following rules:
    
       EQ(s(x), s(y)) -> EQ(x, y)
    
    R is empty.
    Q is empty.
    We have to consider all minimal (P,Q,R)-chains.
    ----------------------------------------
    
    (12) QDPSizeChangeProof (EQUIVALENT)
    By using the subterm criterion [SUBTERM_CRITERION] together with the size-change analysis [AAECC05] we have proven that there are no infinite chains for this DP problem. 
    
    From the DPs we obtained the following set of size-change graphs:
    *EQ(s(x), s(y)) -> EQ(x, y)
    The graph contains the following edges 1 > 1, 2 > 2
    
    
    ----------------------------------------
    
    (13)
    YES
    
    ----------------------------------------
    
    (14)
    Obligation:
    Q DP problem:
    The TRS P consists of the following rules:
    
       PLUS(x, y) -> PLUS(pred(x), y)
    
    The TRS R consists of the following rules:
    
       ite(true, x, y) -> x
       ite(false, x, y) -> y
       pred(s(x)) -> x
       eq(x, x) -> true
       eq(s(x), s(y)) -> eq(x, y)
       plus(x, y) -> ite(eq(x, 0), y, s(plus(pred(x), y)))
    
    The set Q consists of the following terms:
    
       ite(true, x0, x1)
       ite(false, x0, x1)
       pred(s(x0))
       eq(x0, x0)
       eq(s(x0), s(x1))
       plus(x0, x1)
    
    We have to consider all minimal (P,Q,R)-chains.
    ----------------------------------------
    
    (15) UsableRulesProof (EQUIVALENT)
    As all Q-normal forms are R-normal forms we are in the innermost case. Hence, by the usable rules processor [LPAR04] we can delete all non-usable rules [FROCOS05] from R.
    ----------------------------------------
    
    (16)
    Obligation:
    Q DP problem:
    The TRS P consists of the following rules:
    
       PLUS(x, y) -> PLUS(pred(x), y)
    
    The TRS R consists of the following rules:
    
       pred(s(x)) -> x
    
    The set Q consists of the following terms:
    
       ite(true, x0, x1)
       ite(false, x0, x1)
       pred(s(x0))
       eq(x0, x0)
       eq(s(x0), s(x1))
       plus(x0, x1)
    
    We have to consider all minimal (P,Q,R)-chains.
    ----------------------------------------
    
    (17) QReductionProof (EQUIVALENT)
    We deleted the following terms from Q as each root-symbol of these terms does neither occur in P nor in R.[THIEMANN].
    
       ite(true, x0, x1)
       ite(false, x0, x1)
       eq(x0, x0)
       eq(s(x0), s(x1))
       plus(x0, x1)
    
    
    ----------------------------------------
    
    (18)
    Obligation:
    Q DP problem:
    The TRS P consists of the following rules:
    
       PLUS(x, y) -> PLUS(pred(x), y)
    
    The TRS R consists of the following rules:
    
       pred(s(x)) -> x
    
    The set Q consists of the following terms:
    
       pred(s(x0))
    
    We have to consider all minimal (P,Q,R)-chains.
    ----------------------------------------
    
    (19) UsableRulesReductionPairsProof (EQUIVALENT)
    By using the usable rules with reduction pair processor [LPAR04] with a polynomial ordering [POLO], all dependency pairs and the corresponding usable rules [FROCOS05] can be oriented non-strictly. All non-usable rules are removed, and those dependency pairs and usable rules that have been oriented strictly or contain non-usable symbols in their left-hand side are removed as well.
    
    No dependency pairs are removed.
    
    The following rules are removed from R:
    
       pred(s(x)) -> x
    Used ordering: POLO with Polynomial interpretation [POLO]:
    
       POL(PLUS(x_1, x_2)) = 2*x_1 + x_2
       POL(pred(x_1)) = x_1
       POL(s(x_1)) = x_1
    
    
    ----------------------------------------
    
    (20)
    Obligation:
    Q DP problem:
    The TRS P consists of the following rules:
    
       PLUS(x, y) -> PLUS(pred(x), y)
    
    R is empty.
    The set Q consists of the following terms:
    
       pred(s(x0))
    
    We have to consider all minimal (P,Q,R)-chains.
    ----------------------------------------
    
    (21) TransformationProof (EQUIVALENT)
    By instantiating [LPAR04] the rule PLUS(x, y) -> PLUS(pred(x), y) we obtained the following new rules [LPAR04]:
    
       (PLUS(pred(z0), z1) -> PLUS(pred(pred(z0)), z1),PLUS(pred(z0), z1) -> PLUS(pred(pred(z0)), z1))
    
    
    ----------------------------------------
    
    (22)
    Obligation:
    Q DP problem:
    The TRS P consists of the following rules:
    
       PLUS(pred(z0), z1) -> PLUS(pred(pred(z0)), z1)
    
    R is empty.
    The set Q consists of the following terms:
    
       pred(s(x0))
    
    We have to consider all minimal (P,Q,R)-chains.
    ----------------------------------------
    
    (23) TransformationProof (EQUIVALENT)
    By instantiating [LPAR04] the rule PLUS(pred(z0), z1) -> PLUS(pred(pred(z0)), z1) we obtained the following new rules [LPAR04]:
    
       (PLUS(pred(pred(z0)), z1) -> PLUS(pred(pred(pred(z0))), z1),PLUS(pred(pred(z0)), z1) -> PLUS(pred(pred(pred(z0))), z1))
    
    
    ----------------------------------------
    
    (24)
    Obligation:
    Q DP problem:
    The TRS P consists of the following rules:
    
       PLUS(pred(pred(z0)), z1) -> PLUS(pred(pred(pred(z0))), z1)
    
    R is empty.
    The set Q consists of the following terms:
    
       pred(s(x0))
    
    We have to consider all minimal (P,Q,R)-chains.
    ----------------------------------------
    
    (25) QReductionProof (EQUIVALENT)
    We deleted the following terms from Q as they contain symbols which do neither occur in P nor in R.[THIEMANN].
    
       pred(s(x0))
    
    
    ----------------------------------------
    
    (26)
    Obligation:
    Q DP problem:
    The TRS P consists of the following rules:
    
       PLUS(pred(pred(z0)), z1) -> PLUS(pred(pred(pred(z0))), z1)
    
    R is empty.
    Q is empty.
    We have to consider all (P,Q,R)-chains.
    ----------------------------------------
    
    (27) NonTerminationLoopProof (COMPLETE)
    We used the non-termination processor [FROCOS05] to show that the DP problem is infinite.
    Found a loop by semiunifying a rule from P directly.
    
    s = PLUS(pred(pred(z0)), z1) evaluates to  t =PLUS(pred(pred(pred(z0))), z1)
    
    Thus s starts an infinite chain as s semiunifies with t with the following substitutions:
    * Matcher: [z0 / pred(z0)]
    * Semiunifier: [ ]
    
    --------------------------------------------------------------------------------
    Rewriting sequence
    
    The DP semiunifies directly so there is only one rewrite step from PLUS(pred(pred(z0)), z1) to PLUS(pred(pred(pred(z0))), z1).
    
    
    
    
    ----------------------------------------
    
    (28)
    NO

It's because we're used to the lazy execution semantics of if-then-else. The trs format is agnostic about the ordering rules are applied.
It could keep adding `pred` to the terms and never reduce them.
`PLUS(pred(pred(z0)), z1) to PLUS(pred(pred(pred(z0))), z1)`

We can get around this with an explicit `eval(t)` token and rules to move it around. Or we could reformulate it back to how we had it above.

- <https://spoofax.dev/background/stratego/strategic-rewriting/limitations-of-rewriting/>
- <https://dl.acm.org/doi/10.1145/3397677> Context-sensitive Rewriting Salvador Lucas

There is a notion of context sensitive rewriting as one way of dealing with things like this.
<https://aprove.informatik.rwth-aachen.de/help_new/trs.html#trs> There's some other interesting constructs here like equational. I don't know what they do.

```python
%%file /tmp/ite2.trs

(VAR X Y Z)
(STRATEGY CONTEXTSENSITIVE
    (and 1)
    (true)
    (false)
    (if 1)
    (add 1)
    (0)
    (s)
    (first 1 2)
    (nil)
    (cons)
    (from)
)
(RULES
    and(true,X) -> X
    and(false,Y) -> false
    if(true,X,Y) -> X
    if(false,X,Y) -> Y
    add(0,X) -> X
    add(s(X),Y) -> s(add(X,Y))
    first(0,X) -> nil
    first(s(X),cons(Y,Z)) -> cons(Y,first(X,Z))
    from(X) -> cons(X,from(s(X)))
)

```

    Overwriting /tmp/ite2.trs

```python
! java -ea -jar ~/Documents/solvers/aprove.jar -p plain -m wst /tmp/ite2.trs
```

    YES
    proof of /tmp/ite2.trs
    # AProVE Commit ID: 8b4ec3a549e709bdb38c8a065b8ff21f2ca0de28 jan-christoph 20240203 unpublished dirty
    
    
    Termination of the given CSR could be proven:
    
    (0) CSR
    (1) CSRRRRProof [EQUIVALENT, 50 ms]
    (2) CSR
    (3) CSRRRRProof [EQUIVALENT, 0 ms]
    (4) CSR
    (5) RisEmptyProof [EQUIVALENT, 0 ms]
    (6) YES
    
    
    ----------------------------------------
    
    (0)
    Obligation:
    Context-sensitive rewrite system:
    The TRS R consists of the following rules:
    
       and(true, X) -> X
       and(false, Y) -> false
       if(true, X, Y) -> X
       if(false, X, Y) -> Y
       add(0, X) -> X
       add(s(X), Y) -> s(add(X, Y))
       first(0, X) -> nil
       first(s(X), cons(Y, Z)) -> cons(Y, first(X, Z))
       from(X) -> cons(X, from(s(X)))
    
    The replacement map contains the following entries:
    
    and: {1}
    true: empty set
    false: empty set
    if: {1}
    add: {1}
    0: empty set
    s: empty set
    first: {1, 2}
    nil: empty set
    cons: empty set
    from: empty set
    
    ----------------------------------------
    
    (1) CSRRRRProof (EQUIVALENT)
    The following CSR is given: Context-sensitive rewrite system:
    The TRS R consists of the following rules:
    
       and(true, X) -> X
       and(false, Y) -> false
       if(true, X, Y) -> X
       if(false, X, Y) -> Y
       add(0, X) -> X
       add(s(X), Y) -> s(add(X, Y))
       first(0, X) -> nil
       first(s(X), cons(Y, Z)) -> cons(Y, first(X, Z))
       from(X) -> cons(X, from(s(X)))
    
    The replacement map contains the following entries:
    
    and: {1}
    true: empty set
    false: empty set
    if: {1}
    add: {1}
    0: empty set
    s: empty set
    first: {1, 2}
    nil: empty set
    cons: empty set
    from: empty set
    Used ordering:
    Polynomial interpretation [POLO]:
    
       POL(0) = 1
       POL(add(x_1, x_2)) = 2*x_1 + x_2
       POL(and(x_1, x_2)) = x_1 + x_2
       POL(cons(x_1, x_2)) = 0
       POL(false) = 0
       POL(first(x_1, x_2)) = 2 + 2*x_1 + 2*x_2
       POL(from(x_1)) = 0
       POL(if(x_1, x_2, x_3)) = 2 + x_1 + x_2 + x_3
       POL(nil) = 0
       POL(s(x_1)) = 2
       POL(true) = 0
    With this ordering the following rules can be removed by the rule removal processor [LPAR04] because they are oriented strictly:
    
       if(true, X, Y) -> X
       if(false, X, Y) -> Y
       add(0, X) -> X
       add(s(X), Y) -> s(add(X, Y))
       first(0, X) -> nil
       first(s(X), cons(Y, Z)) -> cons(Y, first(X, Z))
    
    
    
    
    ----------------------------------------
    
    (2)
    Obligation:
    Context-sensitive rewrite system:
    The TRS R consists of the following rules:
    
       and(true, X) -> X
       and(false, Y) -> false
       from(X) -> cons(X, from(s(X)))
    
    The replacement map contains the following entries:
    
    and: {1}
    true: empty set
    false: empty set
    s: empty set
    cons: empty set
    from: empty set
    
    ----------------------------------------
    
    (3) CSRRRRProof (EQUIVALENT)
    The following CSR is given: Context-sensitive rewrite system:
    The TRS R consists of the following rules:
    
       and(true, X) -> X
       and(false, Y) -> false
       from(X) -> cons(X, from(s(X)))
    
    The replacement map contains the following entries:
    
    and: {1}
    true: empty set
    false: empty set
    s: empty set
    cons: empty set
    from: empty set
    Used ordering:
    Polynomial interpretation [POLO]:
    
       POL(and(x_1, x_2)) = 1 + x_1 + x_2
       POL(cons(x_1, x_2)) = 0
       POL(false) = 0
       POL(from(x_1)) = 1
       POL(s(x_1)) = 0
       POL(true) = 1
    With this ordering the following rules can be removed by the rule removal processor [LPAR04] because they are oriented strictly:
    
       and(true, X) -> X
       and(false, Y) -> false
       from(X) -> cons(X, from(s(X)))
    
    
    
    
    ----------------------------------------
    
    (4)
    Obligation:
    Context-sensitive rewrite system:
    R is empty.
    
    ----------------------------------------
    
    (5) RisEmptyProof (EQUIVALENT)
    The CSR R is empty. Hence, termination is trivially proven.
    ----------------------------------------
    
    (6)
    YES

# A Random Pile of Comments, Motivations, and Deep Waters

Termination does show up if you've ever used a more interactive system like Coq, lean, Isabelle, Agda, ACL2, Liquid Haskell, F* or Dafny. Some of these systems enforce that recursive definitions are obviously strucutrally descreasing on some argument. They have a very simple termination checker that is made powerful by the fact you can take in some pretty complicated structurally descreasing objects. You can pretty quickly run aground on this stuff once you leave the tutorials.

Termination is related to the more pragmatic question of runtime bounds. Termination is the relatively coarse qurestion of whether a program or dynamic system ever stops or reaches some goal. Runtime bounds want an explicit upper bound expression of some kind of [worst case execution time](https://en.wikipedia.org/wiki/Worst-case_execution_time) (WCET). This can be crucial in safety critical control system software. Also bounds could save you money on your ethereum contract.

More typical verification solvers like CBMC are checking reachability. They find if there exists an execution that has some bad end state (usually looking for bad behavior you want to show is not there, memory violations, arrertions errors, out of bounds, violating functional specs, etc). Another way of putting is is termination is [liveness property](https://en.wikipedia.org/wiki/Safety_and_liveness_properties), reachability is a safety property.

It also relatedly shows up in the the field of total functional programming. <https://ncatlab.org/ufias2012/files/turner.pdf>
In some respects non-termination is a kind of effect. <https://news.ycombinator.com/item?id=25178483> Non-termination "is kind of" or can be modeled as a secret extra value your program returns, similar to how errors or IO can be modeled.

For a discrete finite system, termination amounts to asking whether there are any loops in the graph of states.
<https://en.wikipedia.org/wiki/Cycle_detection>

One way of doing so is to find a topological order and assign an integer to ever state such that it only flows to states of smaller
integer. The index in an topologically ordered array of nodes works. This is a measure function.

This may be hard to do if there is an explosively large number of states. We are also often interested in systems with infinite possible states.

A similar notion appears in dynamical/control systems in the form of a [Lyapunov function](https://en.wikipedia.org/wiki/Lyapunov_function). This is a function $V(x)$, totally made up, that you can show is bounded below and always decreasing (negative time derivative) according to the dynamics of the system. These functions can be used to certify a basin of stability for a control system.

An introduction to termination in term rewriting is to be found in chapter 5 of [term rewriting and all that](https://zubairabid.com/Semester7/subjects/PoPL/books/TRaAT.pdf). The "state" of a term rewriting system is the current term you've rewritten to. There are a priori an infinite family of possible terms `foo, bar(foo), bar(bar(foo)), ...`, so things get hairy.

Most generally, what one wants to show is that the step relation of the system is a [well-founded relation](https://en.wikipedia.org/wiki/Well-founded_relation). More or less "well-founded" is just the mathematical terminology for terminating. Canonical examples of wellfounded relations are `<=` on the naturals.

The [ordinals](https://en.wikipedia.org/wiki/Ordinal_number) can be seen as one possible way to add infinities to the naturals. They are in a very loose respect similar to quaternions or complex numbers in that they extend a reasonable notion of number with wacky nonsense that somehow holds together and is useful. They have an interesting non-commutative notion of addition, multiplication, exponentiation, etc. They are weirder than those though because infinity is so weird and hard to study. Because of this, they are often presented in a way intertwined with set theory. A total (every element can be compared to each other) well order is [well-founded](https://en.wikipedia.org/wiki/Well-order). This is basically an ordinal.

The ability to prove termination of orders or different complexity demonstrates the power of your proof system. <https://en.wikipedia.org/wiki/Ordinal_analysis>

One way of showing you are well founded is if you are a subrelation of another well founded relation. This is kind of what term orderings like knuth bendix ordering (kbo) or path orderings (lpo, rpo) are for.

Another way is to show that you have an order preserving mapping into a nice well founded order. This is kind of what measure functions do.

The dependency pair framework is some important concept of how one proves termination in these solvers, but I don't understand it.

# Other Formats

AProVE takes in some interesting formats. See the webiste for more.

Integer transition systems.

## String rewriting

String rewriting systems like `fgh -> pqr` are equivalent to mono argument term rewriting system of the form `f(g(h(X))) -> p(q(r(X)))`. Kind of the string rewriting could be written as `YfghX -> YpqrX`. The term rewriting system syntax suppresses the context `Y`. Symmettrically we could model as `h(g(f(Y))) -> r(q(p(Y)))`. Interesting to muse on context sometimes.

```python
%%file /tmp/string.srs
(RULES
a b a a -> c b a b a ,
a c b -> a a b c b a
)


```

    Writing /tmp/string.srs

```python
! java -ea -jar ~/Documents/solvers/aprove.jar -m wst /tmp/string.srs -p plain
```

    YES
    proof of /tmp/string.srs
    # AProVE Commit ID: 8b4ec3a549e709bdb38c8a065b8ff21f2ca0de28 jan-christoph 20240203 unpublished dirty
    
    
    Termination w.r.t. Q of the given QTRS could be proven:
    
    (0) QTRS
    (1) RFCMatchBoundsTRSProof [EQUIVALENT, 0 ms]
    (2) YES
    
    
    ----------------------------------------
    
    (0)
    Obligation:
    Q restricted rewrite system:
    The TRS R consists of the following rules:
    
       a(b(a(a(x)))) -> c(b(a(b(a(x)))))
       a(c(b(x))) -> a(a(b(c(b(a(x))))))
    
    Q is empty.
    
    ----------------------------------------
    
    (1) RFCMatchBoundsTRSProof (EQUIVALENT)
    Termination of the TRS R could be shown with a Match Bound [MATCHBOUNDS1,MATCHBOUNDS2] of 2. This implies Q-termination of R.
    The following rules were used to construct the certificate:
    
       a(b(a(a(x)))) -> c(b(a(b(a(x)))))
       a(c(b(x))) -> a(a(b(c(b(a(x))))))
    
    The certificate found is represented by the following graph.
    The certificate consists of the following enumerated nodes:
    1, 4, 14, 15, 16, 17, 18, 19, 20, 21, 22, 27, 28, 29, 30, 36, 37, 38, 39, 40, 41, 42, 43, 44
    
    Node 1 is start node and node 4 is final node.
    
    Those nodes are connected through the following edges:
    
    * 1 to 14 labelled c_1(0)* 1 to 18 labelled a_1(0)* 4 to 4 labelled #_1(0)* 14 to 15 labelled b_1(0)* 15 to 16 labelled a_1(0)* 15 to 27 labelled c_1(1)* 16 to 17 labelled b_1(0)* 17 to 4 labelled a_1(0)* 17 to 27 labelled c_1(1)* 17 to 36 labelled a_1(1)* 18 to 19 labelled a_1(0)* 19 to 20 labelled b_1(0)* 20 to 21 labelled c_1(0)* 21 to 22 labelled b_1(0)* 22 to 4 labelled a_1(0)* 22 to 27 labelled c_1(1)* 22 to 36 labelled a_1(1)* 27 to 28 labelled b_1(1)* 28 to 29 labelled a_1(1)* 28 to 27 labelled c_1(1)* 28 to 41 labelled c_1(2)* 29 to 30 labelled b_1(1)* 30 to 4 labelled a_1(1)* 30 to 27 labelled c_1(1)* 30 to 36 labelled a_1(1)* 30 to 37 labelled a_1(1)* 36 to 37 labelled a_1(1)* 37 to 38 labelled b_1(1)* 38 to 39 labelled c_1(1)* 39 to 40 labelled b_1(1)* 40 to 4 labelled a_1(1)* 40 to 27 labelled c_1(1)* 40 to 36 labelled a_1(1)* 41 to 42 labelled b_1(2)* 42 to 43 labelled a_1(2)* 43 to 44 labelled b_1(2)* 44 to 37 labelled a_1(2)
    
    
    ----------------------------------------
    
    (2)
    YES

## C/Java
<https://aprove.informatik.rwth-aachen.de/interface/v-AProVE2023/c>
I haven't really gotten this one to work yet. It goes via LLVM, so aprove also support llvm.
Relatedly aprove also supports java bytecode <https://aprove.informatik.rwth-aachen.de/interface/v-AProVE2023/java_cpx> including a complexity mode

```python
%%file /tmp/fact.c

int nondetint();
int fact(int n) {
    if (n == 0) return 1;
    return n + fact(n-1);
}
int main(int n){
    return fact(nondetint());
}

```

    Overwriting /tmp/fact.c

```python
! java -ea -jar ~/Documents/solvers/aprove.jar -m wst /tmp/fact.c -p plain
```

    /tmp/fact.c:6:5: warning: only one parameter on 'main' declaration [-Wmain]
    int main(int n){
        ^
    1 warning generated.
    
    line 7:31 mismatched input 'noundef' expecting CLOSEP
    line 7:41 mismatched input ')' expecting ASSIGN
    line 8:7 mismatched input 'alloca' expecting TYPE
    line 9:7 mismatched input 'alloca' expecting TYPE
    line 10:14 mismatched input ',' expecting ASSIGN
    line 10:23 mismatched input ',' expecting ASSIGN
    line 11:7 mismatched input 'load' expecting TYPE
    line 11:24 mismatched input ',' expecting ASSIGN
    line 12:7 mismatched input 'icmp' expecting TYPE
    line 12:21 mismatched input ',' expecting ASSIGN
    line 13:10 mismatched input ',' expecting ASSIGN
    line 13:20 mismatched input ',' expecting ASSIGN
    line 15:0 mismatched input '6' expecting ASSIGN
    line 16:22 mismatched input ',' expecting ASSIGN
    line 19:0 mismatched input '7' expecting ASSIGN
    line 20:7 mismatched input 'load' expecting TYPE
    line 20:24 mismatched input ',' expecting ASSIGN
    line 21:7 mismatched input 'load' expecting TYPE
    line 21:24 mismatched input ',' expecting ASSIGN
    line 22:8 mismatched input 'sub' expecting TYPE
    line 22:22 mismatched input ',' expecting ASSIGN
    line 23:8 mismatched input 'call' expecting TYPE
    Aborted 1710187946Exec. 2, CToLLVM with some error. Reason: java.lang.AssertionError: Did not find any first block!.
                aprove.InputModules.Programs.llvm.parseStructures.LLVMParseFunctionDefinition.convertToFnDefinition(LLVMParseFunctionDefinition.java:37)
                aprove.InputModules.Programs.llvm.parseStructures.LLVMParseModule.createBasicStructure(LLVMParseModule.java:114)
                aprove.InputModules.Programs.llvm.Translator.translate(Translator.java:136)
                aprove.InputModules.Programs.llvm.Translator.translate(Translator.java:115)
                aprove.Framework.Input.Translator$TranslatorSkeleton.translate(Translator.java:91)
                aprove.InputModules.Programs.c.CToLLVMProcessor.process(CToLLVMProcessor.java:69)
                aprove.Strategies.ExecutableStrategies.Executor.execute(Executor.java:326)
                aprove.Strategies.ExecutableStrategies.Executor$Runner.wrappedRun(Executor.java:377)
                aprove.Strategies.Abortions.PooledJob.run(PooledJob.java:99)
                aprove.Strategies.Util.PrioritizableThreadPool$Worker.run(PrioritizableThreadPool.java:274)
                java.base/java.lang.Thread.run(Thread.java:829)
    java.lang.AssertionError: Did not find any first block!
     at aprove.InputModules.Programs.llvm.parseStructures.LLVMParseFunctionDefinition.convertToFnDefinition(LLVMParseFunctionDefinition.java:37)
     at aprove.InputModules.Programs.llvm.parseStructures.LLVMParseModule.createBasicStructure(LLVMParseModule.java:114)
     at aprove.InputModules.Programs.llvm.Translator.translate(Translator.java:136)
     at aprove.InputModules.Programs.llvm.Translator.translate(Translator.java:115)
     at aprove.Framework.Input.Translator$TranslatorSkeleton.translate(Translator.java:91)
     at aprove.InputModules.Programs.c.CToLLVMProcessor.process(CToLLVMProcessor.java:69)
     at aprove.Strategies.ExecutableStrategies.Executor.execute(Executor.java:326)
     at aprove.Strategies.ExecutableStrategies.Executor$Runner.wrappedRun(Executor.java:377)
     at aprove.Strategies.Abortions.PooledJob.run(PooledJob.java:99)
     at aprove.Strategies.Util.PrioritizableThreadPool$Worker.run(PrioritizableThreadPool.java:274)
     at java.base/java.lang.Thread.run(Thread.java:829)
    MAYBE
    proof of /tmp/fact.c
    # AProVE Commit ID: 8b4ec3a549e709bdb38c8a065b8ff21f2ca0de28 jan-christoph 20240203 unpublished dirty
    
    
    Termination of the given C Problem could not be shown:
    
    (0) C Problem
    
    
    ----------------------------------------
    
    (0)
    Obligation:
    c file /tmp/fact.c

## Haskell

I suppose this takes lazy evaluation into account

```python
%%file /tmp/hask.hs
-- https://aprove.informatik.rwth-aachen.de/interface/v-AProVE2023/haskell
{-# htermination (foldr1 :: (a -> a -> a) -> (List a) -> a) #-}


import qualified Prelude


data MyBool = MyTrue | MyFalse

data List a = Cons a (List a) | Nil


foldr1 :: (a -> a -> a) -> (List a) -> a

foldr1 f (Cons x Nil) = x

foldr1 f (Cons x xs) = f x (foldr1 f xs)

```

    Writing /tmp/hask.hs

```python
! java -ea -jar ~/Documents/solvers/aprove.jar -m wst /tmp/hask.hs -p plain
```

    YES
    proof of /tmp/hask.hs
    # AProVE Commit ID: 8b4ec3a549e709bdb38c8a065b8ff21f2ca0de28 jan-christoph 20240203 unpublished dirty
    
    
    H-Termination with start terms of the given HASKELL could be proven:
    
    (0) HASKELL
    (1) BR [EQUIVALENT, 0 ms]
    (2) HASKELL
    (3) COR [EQUIVALENT, 0 ms]
    (4) HASKELL
    (5) Narrow [SOUND, 0 ms]
    (6) QDP
    (7) QDPSizeChangeProof [EQUIVALENT, 0 ms]
    (8) YES
    
    
    ----------------------------------------
    
    (0)
    Obligation:
    mainModule Main 
    module Main where {
    import qualified Prelude;
    data List a = Cons a (List a)  | Nil ;
    
    foldr1 :: (a  ->  a  ->  a)  ->  List a  ->  a;
    foldr1 f (Cons x Nil) = x;
    foldr1 f (Cons x xs) = f x (foldr1 f xs);
    
    }
    
    ----------------------------------------
    
    (1) BR (EQUIVALENT)
    Replaced joker patterns by fresh variables and removed binding patterns.
    ----------------------------------------
    
    (2)
    Obligation:
    mainModule Main 
    module Main where {
    import qualified Prelude;
    data List a = Cons a (List a)  | Nil ;
    
    foldr1 :: (a  ->  a  ->  a)  ->  List a  ->  a;
    foldr1 f (Cons x Nil) = x;
    foldr1 f (Cons x xs) = f x (foldr1 f xs);
    
    }
    
    ----------------------------------------
    
    (3) COR (EQUIVALENT)
    Cond Reductions:
    The following Function with conditions
    "undefined |Falseundefined;
    "
    is transformed to
    "undefined  = undefined1;
    "
    "undefined0 True = undefined;
    "
    "undefined1  = undefined0 False;
    "
    
    ----------------------------------------
    
    (4)
    Obligation:
    mainModule Main 
    module Main where {
    import qualified Prelude;
    data List a = Cons a (List a)  | Nil ;
    
    foldr1 :: (a  ->  a  ->  a)  ->  List a  ->  a;
    foldr1 f (Cons x Nil) = x;
    foldr1 f (Cons x xs) = f x (foldr1 f xs);
    
    }
    
    ----------------------------------------
    
    (5) Narrow (SOUND)
    Haskell To QDPs
    
    digraph dp_graph {
    node [outthreshold=100, inthreshold=100];1[label="foldr1",fontsize=16,color="grey",shape="box"];1 -> 3[label="",style="dashed", color="grey", weight=3];
    3[label="foldr1 vx3",fontsize=16,color="grey",shape="box"];3 -> 4[label="",style="dashed", color="grey", weight=3];
    4[label="foldr1 vx3 vx4",fontsize=16,color="burlywood",shape="triangle"];15[label="vx4/Cons vx40 vx41",fontsize=10,color="white",style="solid",shape="box"];4 -> 15[label="",style="solid", color="burlywood", weight=9];
    15 -> 5[label="",style="solid", color="burlywood", weight=3];
    16[label="vx4/Nil",fontsize=10,color="white",style="solid",shape="box"];4 -> 16[label="",style="solid", color="burlywood", weight=9];
    16 -> 6[label="",style="solid", color="burlywood", weight=3];
    5[label="foldr1 vx3 (Cons vx40 vx41)",fontsize=16,color="burlywood",shape="box"];17[label="vx41/Cons vx410 vx411",fontsize=10,color="white",style="solid",shape="box"];5 -> 17[label="",style="solid", color="burlywood", weight=9];
    17 -> 7[label="",style="solid", color="burlywood", weight=3];
    18[label="vx41/Nil",fontsize=10,color="white",style="solid",shape="box"];5 -> 18[label="",style="solid", color="burlywood", weight=9];
    18 -> 8[label="",style="solid", color="burlywood", weight=3];
    6[label="foldr1 vx3 Nil",fontsize=16,color="black",shape="box"];6 -> 9[label="",style="solid", color="black", weight=3];
    7[label="foldr1 vx3 (Cons vx40 (Cons vx410 vx411))",fontsize=16,color="black",shape="box"];7 -> 10[label="",style="solid", color="black", weight=3];
    8[label="foldr1 vx3 (Cons vx40 Nil)",fontsize=16,color="black",shape="box"];8 -> 11[label="",style="solid", color="black", weight=3];
    9[label="error []",fontsize=16,color="red",shape="box"];10[label="vx3 vx40 (foldr1 vx3 (Cons vx410 vx411))",fontsize=16,color="green",shape="box"];10 -> 12[label="",style="dashed", color="green", weight=3];
    10 -> 13[label="",style="dashed", color="green", weight=3];
    11[label="vx40",fontsize=16,color="green",shape="box"];12[label="vx40",fontsize=16,color="green",shape="box"];13 -> 4[label="",style="dashed", color="red", weight=0];
    13[label="foldr1 vx3 (Cons vx410 vx411)",fontsize=16,color="magenta"];13 -> 14[label="",style="dashed", color="magenta", weight=3];
    14[label="Cons vx410 vx411",fontsize=16,color="green",shape="box"];}
    
    ----------------------------------------
    
    (6)
    Obligation:
    Q DP problem:
    The TRS P consists of the following rules:
    
       new_foldr1(vx3, Cons(vx40, Cons(vx410, vx411)), h) -> new_foldr1(vx3, Cons(vx410, vx411), h)
    
    R is empty.
    Q is empty.
    We have to consider all minimal (P,Q,R)-chains.
    ----------------------------------------
    
    (7) QDPSizeChangeProof (EQUIVALENT)
    By using the subterm criterion [SUBTERM_CRITERION] together with the size-change analysis [AAECC05] we have proven that there are no infinite chains for this DP problem. 
    
    From the DPs we obtained the following set of size-change graphs:
    *new_foldr1(vx3, Cons(vx40, Cons(vx410, vx411)), h) -> new_foldr1(vx3, Cons(vx410, vx411), h)
    The graph contains the following edges 1 >= 1, 2 > 2, 3 >= 3
    
    
    ----------------------------------------
    
    (8)
    YES

## Prolog

Prolog is extra interesting because prolog programs are inference rules. I'm not sure that the depth first strategy of prolog matters that much to me. It'd be interesting to support tabling or other strategies and ask about temrination of these

Some other links to take a look at

- <https://www.metalevel.at/prolog/termination>
- <https://www.cs.unipr.it/cTI/>
- <https://ciao-lang.org/ciao/build/doc/ciao.html/native_props_cost_doc.html#terminates/1>

```python
%%file /tmp/prolog.pl
%query: append(b,f,f)
% https://aprove.informatik.rwth-aachen.de/interface/v-AProVE2023/prolog
append([],L,L).
append([X|Xs],Ys,[X|Zs]) :- append(Xs,Ys,Zs).
```

    Overwriting /tmp/prolog.pl

```python
! java -ea -jar ~/Documents/solvers/aprove.jar -m wst /tmp/prolog.pl -p plain
```

    YES
    proof of /tmp/prolog.pl
    # AProVE Commit ID: 8b4ec3a549e709bdb38c8a065b8ff21f2ca0de28 jan-christoph 20240203 unpublished dirty
    
    
    Left Termination of the query pattern
    
    append(g,a,a)
    
    w.r.t. the given Prolog program could successfully be proven:
    
    (0) Prolog
    (1) PrologToPiTRSProof [SOUND, 0 ms]
    (2) PiTRS
    (3) DependencyPairsProof [EQUIVALENT, 0 ms]
    (4) PiDP
    (5) DependencyGraphProof [EQUIVALENT, 0 ms]
    (6) PiDP
    (7) UsableRulesProof [EQUIVALENT, 0 ms]
    (8) PiDP
    (9) PiDPToQDPProof [SOUND, 0 ms]
    (10) QDP
    (11) QDPSizeChangeProof [EQUIVALENT, 0 ms]
    (12) YES
    
    
    ----------------------------------------
    
    (0)
    Obligation:
    Clauses:
    
    append([], L, L).
    append(.(X, Xs), Ys, .(X, Zs)) :- append(Xs, Ys, Zs).
    
    
    Query: append(g,a,a)
    ----------------------------------------
    
    (1) PrologToPiTRSProof (SOUND)
    We use the technique of [TOCL09]. With regard to the inferred argument filtering the predicates were used in the following modes:
    
    append_in_3: (b,f,f)
    
    Transforming Prolog into the following Term Rewriting System:
    
    Pi-finite rewrite system:
    The TRS R consists of the following rules:
    
       append_in_gaa([], L, L) -> append_out_gaa([], L, L)
       append_in_gaa(.(X, Xs), Ys, .(X, Zs)) -> U1_gaa(X, Xs, Ys, Zs, append_in_gaa(Xs, Ys, Zs))
       U1_gaa(X, Xs, Ys, Zs, append_out_gaa(Xs, Ys, Zs)) -> append_out_gaa(.(X, Xs), Ys, .(X, Zs))
    
    The argument filtering Pi contains the following mapping:
    append_in_gaa(x1, x2, x3)  =  append_in_gaa(x1)
    
    []  =  []
    
    append_out_gaa(x1, x2, x3)  =  append_out_gaa
    
    .(x1, x2)  =  .(x1, x2)
    
    U1_gaa(x1, x2, x3, x4, x5)  =  U1_gaa(x5)
    
    
    
    
    
    Infinitary Constructor Rewriting Termination of PiTRS implies Termination of Prolog
    
    
    
    ----------------------------------------
    
    (2)
    Obligation:
    Pi-finite rewrite system:
    The TRS R consists of the following rules:
    
       append_in_gaa([], L, L) -> append_out_gaa([], L, L)
       append_in_gaa(.(X, Xs), Ys, .(X, Zs)) -> U1_gaa(X, Xs, Ys, Zs, append_in_gaa(Xs, Ys, Zs))
       U1_gaa(X, Xs, Ys, Zs, append_out_gaa(Xs, Ys, Zs)) -> append_out_gaa(.(X, Xs), Ys, .(X, Zs))
    
    The argument filtering Pi contains the following mapping:
    append_in_gaa(x1, x2, x3)  =  append_in_gaa(x1)
    
    []  =  []
    
    append_out_gaa(x1, x2, x3)  =  append_out_gaa
    
    .(x1, x2)  =  .(x1, x2)
    
    U1_gaa(x1, x2, x3, x4, x5)  =  U1_gaa(x5)
    
    
    
    ----------------------------------------
    
    (3) DependencyPairsProof (EQUIVALENT)
    Using Dependency Pairs [AG00,LOPSTR] we result in the following initial DP problem:
    Pi DP problem:
    The TRS P consists of the following rules:
    
       APPEND_IN_GAA(.(X, Xs), Ys, .(X, Zs)) -> U1_GAA(X, Xs, Ys, Zs, append_in_gaa(Xs, Ys, Zs))
       APPEND_IN_GAA(.(X, Xs), Ys, .(X, Zs)) -> APPEND_IN_GAA(Xs, Ys, Zs)
    
    The TRS R consists of the following rules:
    
       append_in_gaa([], L, L) -> append_out_gaa([], L, L)
       append_in_gaa(.(X, Xs), Ys, .(X, Zs)) -> U1_gaa(X, Xs, Ys, Zs, append_in_gaa(Xs, Ys, Zs))
       U1_gaa(X, Xs, Ys, Zs, append_out_gaa(Xs, Ys, Zs)) -> append_out_gaa(.(X, Xs), Ys, .(X, Zs))
    
    The argument filtering Pi contains the following mapping:
    append_in_gaa(x1, x2, x3)  =  append_in_gaa(x1)
    
    []  =  []
    
    append_out_gaa(x1, x2, x3)  =  append_out_gaa
    
    .(x1, x2)  =  .(x1, x2)
    
    U1_gaa(x1, x2, x3, x4, x5)  =  U1_gaa(x5)
    
    APPEND_IN_GAA(x1, x2, x3)  =  APPEND_IN_GAA(x1)
    
    U1_GAA(x1, x2, x3, x4, x5)  =  U1_GAA(x5)
    
    
    We have to consider all (P,R,Pi)-chains
    ----------------------------------------
    
    (4)
    Obligation:
    Pi DP problem:
    The TRS P consists of the following rules:
    
       APPEND_IN_GAA(.(X, Xs), Ys, .(X, Zs)) -> U1_GAA(X, Xs, Ys, Zs, append_in_gaa(Xs, Ys, Zs))
       APPEND_IN_GAA(.(X, Xs), Ys, .(X, Zs)) -> APPEND_IN_GAA(Xs, Ys, Zs)
    
    The TRS R consists of the following rules:
    
       append_in_gaa([], L, L) -> append_out_gaa([], L, L)
       append_in_gaa(.(X, Xs), Ys, .(X, Zs)) -> U1_gaa(X, Xs, Ys, Zs, append_in_gaa(Xs, Ys, Zs))
       U1_gaa(X, Xs, Ys, Zs, append_out_gaa(Xs, Ys, Zs)) -> append_out_gaa(.(X, Xs), Ys, .(X, Zs))
    
    The argument filtering Pi contains the following mapping:
    append_in_gaa(x1, x2, x3)  =  append_in_gaa(x1)
    
    []  =  []
    
    append_out_gaa(x1, x2, x3)  =  append_out_gaa
    
    .(x1, x2)  =  .(x1, x2)
    
    U1_gaa(x1, x2, x3, x4, x5)  =  U1_gaa(x5)
    
    APPEND_IN_GAA(x1, x2, x3)  =  APPEND_IN_GAA(x1)
    
    U1_GAA(x1, x2, x3, x4, x5)  =  U1_GAA(x5)
    
    
    We have to consider all (P,R,Pi)-chains
    ----------------------------------------
    
    (5) DependencyGraphProof (EQUIVALENT)
    The approximation of the Dependency Graph [LOPSTR] contains 1 SCC with 1 less node.
    ----------------------------------------
    
    (6)
    Obligation:
    Pi DP problem:
    The TRS P consists of the following rules:
    
       APPEND_IN_GAA(.(X, Xs), Ys, .(X, Zs)) -> APPEND_IN_GAA(Xs, Ys, Zs)
    
    The TRS R consists of the following rules:
    
       append_in_gaa([], L, L) -> append_out_gaa([], L, L)
       append_in_gaa(.(X, Xs), Ys, .(X, Zs)) -> U1_gaa(X, Xs, Ys, Zs, append_in_gaa(Xs, Ys, Zs))
       U1_gaa(X, Xs, Ys, Zs, append_out_gaa(Xs, Ys, Zs)) -> append_out_gaa(.(X, Xs), Ys, .(X, Zs))
    
    The argument filtering Pi contains the following mapping:
    append_in_gaa(x1, x2, x3)  =  append_in_gaa(x1)
    
    []  =  []
    
    append_out_gaa(x1, x2, x3)  =  append_out_gaa
    
    .(x1, x2)  =  .(x1, x2)
    
    U1_gaa(x1, x2, x3, x4, x5)  =  U1_gaa(x5)
    
    APPEND_IN_GAA(x1, x2, x3)  =  APPEND_IN_GAA(x1)
    
    
    We have to consider all (P,R,Pi)-chains
    ----------------------------------------
    
    (7) UsableRulesProof (EQUIVALENT)
    For (infinitary) constructor rewriting [LOPSTR] we can delete all non-usable rules from R.
    ----------------------------------------
    
    (8)
    Obligation:
    Pi DP problem:
    The TRS P consists of the following rules:
    
       APPEND_IN_GAA(.(X, Xs), Ys, .(X, Zs)) -> APPEND_IN_GAA(Xs, Ys, Zs)
    
    R is empty.
    The argument filtering Pi contains the following mapping:
    .(x1, x2)  =  .(x1, x2)
    
    APPEND_IN_GAA(x1, x2, x3)  =  APPEND_IN_GAA(x1)
    
    
    We have to consider all (P,R,Pi)-chains
    ----------------------------------------
    
    (9) PiDPToQDPProof (SOUND)
    Transforming (infinitary) constructor rewriting Pi-DP problem [LOPSTR] into ordinary QDP problem [LPAR04] by application of Pi.
    ----------------------------------------
    
    (10)
    Obligation:
    Q DP problem:
    The TRS P consists of the following rules:
    
       APPEND_IN_GAA(.(X, Xs)) -> APPEND_IN_GAA(Xs)
    
    R is empty.
    Q is empty.
    We have to consider all (P,Q,R)-chains.
    ----------------------------------------
    
    (11) QDPSizeChangeProof (EQUIVALENT)
    By using the subterm criterion [SUBTERM_CRITERION] together with the size-change analysis [AAECC05] we have proven that there are no infinite chains for this DP problem. 
    
    From the DPs we obtained the following set of size-change graphs:
    *APPEND_IN_GAA(.(X, Xs)) -> APPEND_IN_GAA(Xs)
    The graph contains the following edges 1 > 1
    
    
    ----------------------------------------
    
    (12)
    YES

# Bits and Bobbles

-
- <https://www.fstar-lang.org/tutorial/book/part4/part4_div.html>
- <https://lean-lang.org/blog/2024-1-11-recursive-definitions-in-lean/>
- <http://adam.chlipala.net/cpdt/html/GeneralRec.html> coq termination
- <https://coq.inria.fr/files/adt-2fev10-barras.pdf> the syntacticguard condition of coq - barras
- <https://ucsd-progsys.github.io/liquidhaskell/specifications/#specifying-measures> measures in liquid haskell
- <https://dafny.org/dafny/OnlineTutorial/Termination> dafny termination. decreases clauses
- <https://www.cs.utexas.edu/users/moore/acl2/manuals/current/manual/index-seo.php/ACL2____MEASURE?path=3921/6451/3296/53/1001>
- Maude termination assistant <https://maude.cs.uiuc.edu/tools/mta/>

```python
%%file /tmp/append.trs
(VAR x y z)
(RULES
    append(nil,y) -> y
    append(cons(x,z),y) -> cons(x, append(z,y))
)
```

```python
import subprocess
res = subprocess.run(["java", "-ea", "-jar", "/home/philip/Downloads/aprove.jar", "/tmp/ex.trs", "-p", "cpf"], capture_output=True, check=True)
print(res)
print(dir(res.stdout))
import xml.etree.ElementTree as ET
tree = ET.fromstring(res.stdout.decode())
print(tree)
print(tree.tag)
```

```python
tree.tag
tree.attrib
print([elem.tag for elem in tree])
input = tree.find("input")
print(dir(input))
input.text
ET.tostring(input)
ET.dump(input)
```

```python
def etree_to_dict(t):
    d = {t.tag : map(etree_to_dict, t.getchildren())}
    d.update(('@' + k, v) for k, v in t.attrib.iteritems())
    d['text'] = t.text
    return d
```

ebpf termination via C prover
<https://qmonnet.github.io/whirl-offload/2020/04/12/llvm-ebpf-asm/>
<https://mdaverde.com/posts/ebpf-dump-insns/>

```python
%%file /tmp/fact.c

int fact(int x){
    int y = 1;
    while(x > 1){
        x = x - 1;
        y = y * x;
    }
    return y;
}
```

    Overwriting /tmp/fact.c

```python
! java -ea -cp ~/Downloads/term-rewrite/aprove.jar aprove.CommandLineInterface.CFrontendMain /tmp/fact.c
```

    line 7:31 mismatched input 'noundef' expecting CLOSEP
    line 7:41 mismatched input ')' expecting ASSIGN
    line 8:7 mismatched input 'alloca' expecting TYPE
    line 9:7 mismatched input 'alloca' expecting TYPE
    line 10:14 mismatched input ',' expecting ASSIGN
    line 10:22 mismatched input ',' expecting ASSIGN
    line 11:21 mismatched input ',' expecting ASSIGN
    line 14:0 mismatched input '4' expecting ASSIGN
    line 15:7 mismatched input 'load' expecting TYPE
    line 15:23 mismatched input ',' expecting ASSIGN
    line 16:7 mismatched input 'icmp' expecting TYPE
    line 16:22 mismatched input ',' expecting ASSIGN
    line 17:10 mismatched input ',' expecting ASSIGN
    line 17:20 mismatched input ',' expecting ASSIGN
    line 19:0 mismatched input '7' expecting ASSIGN
    line 20:7 mismatched input 'load' expecting TYPE
    line 20:23 mismatched input ',' expecting ASSIGN
    line 21:7 mismatched input 'sub' expecting TYPE
    line 21:21 mismatched input ',' expecting ASSIGN
    line 22:14 mismatched input ',' expecting ASSIGN
    line 22:22 mismatched input ',' expecting ASSIGN
    line 23:8 mismatched input 'load' expecting TYPE
    line 23:24 mismatched input ',' expecting ASSIGN
    line 24:8 mismatched input 'load' expecting TYPE
    line 24:24 mismatched input ',' expecting ASSIGN
    line 25:8 mismatched input 'mul' expecting TYPE
    line 25:23 mismatched input ',' expecting ASSIGN
    line 26:2 mismatched input 'store' expecting ASSIGN
    line 26:15 mismatched input ',' expecting ASSIGN
    line 26:23 mismatched input ',' expecting ASSIGN
    line 27:13 mismatched input ',' expecting ASSIGN
    line 27:26 missing ASSIGN at '!'
    line 27:27 mismatched input '6' expecting OPENC
    line 30:8 mismatched input 'load' expecting TYPE
    line 30:24 mismatched input ',' expecting ASSIGN
    line 32:0 mismatched input '}' expecting ASSIGN
    java.lang.AssertionError: Did not find any first block!
     at aprove.InputModules.Programs.llvm.parseStructures.LLVMParseFunctionDefinition.convertToFnDefinition(LLVMParseFunctionDefinition.java:37)
     at aprove.InputModules.Programs.llvm.parseStructures.LLVMParseModule.createBasicStructure(LLVMParseModule.java:114)
     at aprove.InputModules.Programs.llvm.Translator.translate(Translator.java:136)
     at aprove.InputModules.Programs.llvm.Translator.translate(Translator.java:115)
     at aprove.Framework.Input.Translator$TranslatorSkeleton.translate(Translator.java:91)
     at aprove.InputModules.Programs.c.CToLLVMProcessor.process(CToLLVMProcessor.java:69)
     at aprove.Strategies.ExecutableStrategies.Executor.execute(Executor.java:326)
     at aprove.Strategies.ExecutableStrategies.Executor$Runner.wrappedRun(Executor.java:377)
     at aprove.Strategies.Abortions.PooledJob.run(PooledJob.java:99)
     at aprove.Strategies.Util.PrioritizableThreadPool$Worker.run(PrioritizableThreadPool.java:274)
     at java.base/java.lang.Thread.run(Thread.java:840)

```python
!clang -target bpf -O2 -c /tmp/fact.c -o /tmp/fact.o
```

```python
!llvm-objdump -d /tmp/fact.o
```

    /tmp/fact.o: file format elf64-bpf
    
    Disassembly of section .text:
    
    0000000000000000 <fact>:
           0: b7 00 00 00 01 00 00 00 r0 = 0x1
           1: bf 12 00 00 00 00 00 00 r2 = r1
           2: 67 02 00 00 20 00 00 00 r2 <<= 0x20
           3: c7 02 00 00 20 00 00 00 r2 s>>= 0x20
           4: b7 03 00 00 02 00 00 00 r3 = 0x2
           5: 6d 23 09 00 00 00 00 00 if r3 s> r2 goto +0x9 <LBB0_3>
           6: 07 01 00 00 01 00 00 00 r1 += 0x1
    
    0000000000000038 <LBB0_2>:
           7: bf 12 00 00 00 00 00 00 r2 = r1
           8: 07 02 00 00 fe ff ff ff r2 += -0x2
           9: 2f 20 00 00 00 00 00 00 r0 *= r2
          10: 07 01 00 00 ff ff ff ff r1 += -0x1
          11: bf 12 00 00 00 00 00 00 r2 = r1
          12: 67 02 00 00 20 00 00 00 r2 <<= 0x20
          13: 77 02 00 00 20 00 00 00 r2 >>= 0x20
          14: 25 02 f8 ff 02 00 00 00 if r2 > 0x2 goto -0x8 <LBB0_2>
    
    0000000000000078 <LBB0_3>:
          15: 95 00 00 00 00 00 00 00 exit

```python
! # angr decompile /tmp/fact.o  deosn't work
```

    Traceback (most recent call last):
      File "/home/philip/.local/bin/angr", line 8, in <module>
        sys.exit(main())
      File "/home/philip/.local/lib/python3.10/site-packages/angr/__main__.py", line 50, in main
        decompilation = decompile_functions(
      File "/home/philip/.local/lib/python3.10/site-packages/angr/analyses/decompiler/utils.py", line 651, in decompile_functions
        proj = angr.Project(path, auto_load_libs=False)
      File "/home/philip/.local/lib/python3.10/site-packages/angr/project.py", line 147, in __init__
        self.loader = cle.Loader(self.filename, concrete_target=concrete_target, **load_options)
      File "/home/philip/.local/lib/python3.10/site-packages/cle/loader.py", line 188, in __init__
        self.initial_load_objects = self._internal_load(
      File "/home/philip/.local/lib/python3.10/site-packages/cle/loader.py", line 782, in _internal_load
        obj = self._load_object_isolated(main_spec)
      File "/home/philip/.local/lib/python3.10/site-packages/cle/loader.py", line 985, in _load_object_isolated
        result = backend_cls(binary, binary_stream, is_main_bin=self._main_object is None, loader=self, **options)
      File "/home/philip/.local/lib/python3.10/site-packages/cle/backends/elf/elf.py", line 113, in __init__
        self.set_arch(self.extract_arch(self._reader))
      File "/home/philip/.local/lib/python3.10/site-packages/cle/backends/elf/elf.py", line 327, in extract_arch
        return archinfo.arch_from_id(arch_str, "le" if reader.little_endian else "be", reader.elfclass)
      File "/home/philip/.local/lib/python3.10/site-packages/archinfo/arch.py", line 887, in arch_from_id
        raise ArchNotFound(
    archinfo.arch.ArchNotFound: Can't find architecture info for architecture em_bpf with 64 bits and Iend_LE endness
