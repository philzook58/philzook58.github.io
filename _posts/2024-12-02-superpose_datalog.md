---
title: Superposition as a Super Datalog
date: 2024-12-02
---

[Resolution](https://en.wikipedia.org/wiki/Resolution_(logic)) is an old technique in automated reasoning. [Datalog](https://en.wikipedia.org/wiki/Datalog) is a family of languages capable of expressing recursive database queries. The ancestry of datalog can be traced back to resolution and it is interesting and fruitful to examine the capabilities of modern resolution style provers in light of the use cases and operational interpretability of datalog.

Datalog is quite simple. You have a starting set of facts in relations for example the edges in a graph. These can be stored as a relational table.

```prolog
edge(1,2).
edge(2,3).
```

Then you have rules that iteratively derive new facts from the currently existing facts. This is done by making a database query out of the body of the rule, and inserting the head with the found values.

```prolog
path(X,Y) :- edge(X,Y).  % if there is an edge, there is a path
path(X,Y) :- edge(X,Z), path(Z,Y). % You can paste an edge on the end of a path to get a new path.
```

[souffle](https://souffle-lang.github.io/simple) is a good dastaloig

```python
%%file /tmp/path.dl
.decl edge(x:number, y:number)
edge(1,2).
edge(2,3).

.decl path(x:number, y:number)
.output path(IO=stdout)
path(X,Y) :- edge(X,Y).
path(X,Y) :- edge(X,Z), path(Z,Y).
```

    Overwriting /tmp/path.dl

```python
! souffle /tmp/path.dl
```

    ---------------
    path
    ===============
    1 2
    1 3
    2 3
    ===============

You can also express basically the same thing to a first order theorem prover.

```python
%%file /tmp/path.p

cnf(edgeab, axiom, edge(a,b)).
cnf(edgebc, axiom, edge(b,c)).
cnf(edge_is_path , axiom, path(X,Y) | ~edge(X,Y)).
cnf(path_trans, axiom, path(X,Z) | ~edge(X,Y) | ~path(Y,Z)).

% alternative fof syntax for rules. There are more https://www.tptp.org/
%fof(edge_is_path , axiom, ![X,Y] : (edge(X,Y) => path(X,Y))).
%fof(path_transm, axiom, ![X,Y,Z] : ((path(X,Z) & edge(X,Y)) => path(Y,Z))).
```

    Overwriting /tmp/path.p

We can see the first two assertions establish the base edge facts and the the last two establish rules. To translate the logic programming rules to a first order ATP clause, we take the classical correspondence that implication `a -> b` is equivalent to `~a | b`. Hence for example  `path(X,Z) :- edge(X,Y), path(Y,Z).` becomes `path(X,Z) | ~edge(X,Y) | ~path(Y,Z)`. We can kind of think of negation `~` as a marker stating this literal goes in the body of the rule. There is an alternate prolog universe in which this was standard notation.

Two premier resolution style theorems provers are [Vampire](https://vprover.github.io/usage.html) and [eprover](https://github.com/eprover/eprover). They are usually top in class in the [CADE ATP competition](https://tptp.org/CASC/).

```python
! vampire /tmp/path.p
```

    % Running in auto input_syntax mode. Trying TPTP
    % SZS status Satisfiable for path
    % # SZS output start Saturation.
    cnf(u13,axiom,
        ~edge(b,X0) | path(X0,c)).
    
    cnf(u12,axiom,
        ~edge(a,X0) | path(X0,b)).
    
    cnf(u15,axiom,
        path(c,c)).
    
    cnf(u17,axiom,
        ~edge(c,X0) | path(X0,c)).
    
    cnf(u19,axiom,
        ~edge(c,X0) | path(X0,b)).
    
    cnf(u14,axiom,
        path(b,b)).
    
    cnf(u16,axiom,
        ~edge(b,X0) | path(X0,b)).
    
    cnf(u9,axiom,
        ~path(X0,X2) | ~edge(X0,X1) | path(X1,X2)).
    
    cnf(u18,axiom,
        path(c,b)).
    
    cnf(u8,axiom,
        ~edge(X0,X1) | path(X0,X1)).
    
    cnf(u1,axiom,
        edge(a,b)).
    
    cnf(u11,axiom,
        path(b,c)).
    
    cnf(u10,axiom,
        path(a,b)).
    
    cnf(u2,axiom,
        edge(b,c)).
    
    % # SZS output end Saturation.
    % ------------------------------
    % Version: Vampire 4.9 (commit 5ad494e78 on 2024-06-14 14:05:27 +0100)
    % Linked with Z3 4.12.3.0 79bbbf76d0c123481c8ca05cd3a98939270074d3 z3-4.8.4-7980-g79bbbf76d
    % Termination reason: Satisfiable
    
    % Memory used [KB]: 429
    % Time elapsed: 0.0000 s
    perf_event_open failed (instruction limiting will be disabled): Permission denied
    (If you are seeing 'Permission denied' ask your admin to run 'sudo sysctl -w kernel.perf_event_paranoid=-1' for you.)
    % ------------------------------
    % ------------------------------

Oh wow, sweet. That was easy. Blog post over.

No, sorry.

Really, a rule of thumb is that you should never be running either vampire or eprover without a `--mode` or `--auto` flag. The default modes are enormously slower.

In `casc_sat` mode we get piles of difficult to interpret garbage for vampire.

```python
! vampire --mode casc_sat /tmp/path.p
```

    % Running in auto input_syntax mode. Trying TPTP
    % WARNING: time unlimited strategy and instruction limiting not in place - attempting to translate instructions to time
    % fmb+10_1:1_sil=256000:i=98885:tgt=full:fmbsr=1.3:fmbss=10_0 on path for (495ds/98885Mi)
    Detected minimum model sizes of [1]
    Detected maximum model sizes of [3]
    TRYING [10]
    Finite Model Found!
    % SZS status Satisfiable for path
    perf_event_open failed (instruction limiting will be disabled): Permission denied
    (If you are seeing 'Permission denied' ask your admin to run 'sudo sysctl -w kernel.perf_event_paranoid=-1' for you.)
    % Solution written to "/tmp/vampire-proof-3398902"
    % SZS output start FiniteModel for path
    tff('declare_$i1',type,a:$i).
    tff('declare_$i2',type,b:$i).
    tff('declare_$i3',type,'fmb_$i_3':$i).
    tff('declare_$i4',type,a:$i).
    tff('declare_$i5',type,a:$i).
    tff('declare_$i6',type,a:$i).
    tff('declare_$i7',type,b:$i).
    tff('declare_$i8',type,a:$i).
    tff('declare_$i9',type,a:$i).
    tff('declare_$i10',type,'fmb_$i_10':$i).
    tff('finite_domain_$i',axiom,
          ! [X:$i] : (
             X = a | X = b | X = 'fmb_$i_3' | X = a | X = a | 
             X = a | X = b | X = a | X = a | X = 'fmb_$i_10'
          ) ).
    
    tff('distinct_domain_$i',axiom,
             a != b & a != 'fmb_$i_3' & a != a & a != a & a != a & 
             a != b & a != a & a != a & a != 'fmb_$i_10' & b != 'fmb_$i_3' & 
             b != a & b != a & b != a & b != b & b != a & 
             b != a & b != 'fmb_$i_10' & 'fmb_$i_3' != a & 'fmb_$i_3' != a & 'fmb_$i_3' != a & 
             'fmb_$i_3' != b & 'fmb_$i_3' != a & 'fmb_$i_3' != a & 'fmb_$i_3' != 'fmb_$i_10' & a != a & 
             a != a & a != b & a != a & a != a & a != 'fmb_$i_10' & 
             a != a & a != b & a != a & a != a & a != 'fmb_$i_10' & 
             a != b & a != a & a != a & a != 'fmb_$i_10' & b != a & 
             b != a & b != 'fmb_$i_10' & a != a & a != 'fmb_$i_10' & a != 'fmb_$i_10'
    ).
    
    tff(declare_c,type,c:$i).
    tff(c_definition,axiom,c = a).
    tff(declare_edge,type,edge: ($i * $i) > $o).
    tff(predicate_edge,axiom,
               edge(a,a)
             & edge(a,b)
             & ~edge(a,'fmb_$i_3')
    %         edge(a,a) undefined in model
    %         edge(a,a) undefined in model
    %         edge(a,a) undefined in model
    %         edge(a,b) undefined in model
    %         edge(a,a) undefined in model
    %         edge(a,a) undefined in model
    %         edge(a,'fmb_$i_10') undefined in model
             & edge(b,a)
             & edge(b,b)
             & ~edge(b,'fmb_$i_3')
    %         edge(b,a) undefined in model
    %         edge(b,a) undefined in model
    %         edge(b,a) undefined in model
    
    ... Blah blah blah blah...

    %         path('fmb_$i_10',b) undefined in model
    %         path('fmb_$i_10',a) undefined in model
    %         path('fmb_$i_10',a) undefined in model
    %         path('fmb_$i_10','fmb_$i_10') undefined in model
    
    ).
    
    % SZS output end FiniteModel for path
    % ------------------------------
    % Version: Vampire 4.9 (commit 5ad494e78 on 2024-06-14 14:05:27 +0100)
    % Linked with Z3 4.12.3.0 79bbbf76d0c123481c8ca05cd3a98939270074d3 z3-4.8.4-7980-g79bbbf76d
    % Termination reason: Satisfiable
    
    % Memory used [KB]: 682
    % Time elapsed: 0.001 s
    % ------------------------------
    % ------------------------------
    % Success in time 0.005 s

eprover in it's default mode does not terminate/saturate on this problem. We can kind of see the problem that it is resolving rules against rules, building larger and larger transitivity clauses.

```python
! eprover-ho --total-clause-set-limit=15 /tmp/path.p
```

    # Initializing proof state
    # Scanning for AC axioms
    #
    #cnf(i_0_3, plain, (edge(a,b))).
    #
    #cnf(i_0_4, plain, (edge(b,c))).
    #
    #cnf(i_0_5, plain, (path(X1,X2)|~edge(X1,X2))).
    #
    #cnf(i_0_6, plain, (path(X3,X2)|~path(X1,X2)|~edge(X1,X3))).
    #
    #cnf(i_0_8, plain, (path(X1,X2)|~edge(X3,X1)|~edge(X3,X2))).
    #
    #cnf(i_0_7, plain, (path(X1,X2)|~path(X4,X2)|~edge(X3,X1)|~edge(X4,X3))).
    #
    #cnf(i_0_9, plain, (path(X1,X2)|~edge(X3,X1)|~edge(X4,X3)|~edge(X4,X2))).
    ##
    #cnf(i_0_10, plain, (path(X1,X2)|~path(X4,X2)|~edge(X3,X1)|~edge(X5,X3)|~edge(X4,X5))).
    
    # Failure: User resource limit exceeded!
    # SZS status ResourceOut

However, we can get it to terminate with a reasonable database if we start tweaking the options controlling it's execution.

```python
! eprover-ho --print-saturated --literal-selection-strategy="SelectNegativeLiterals" /tmp/path.p
```

    # Initializing proof state
    # Scanning for AC axioms
    #
    #cnf(i_0_3, plain, (edge(a,b))).
    #
    #cnf(i_0_4, plain, (edge(b,c))).
    #
    #cnf(i_0_5, plain, (path(X1,X2)|~edge(X1,X2))).
    #
    #cnf(i_0_7, plain, (path(b,c))).
    #
    #cnf(i_0_8, plain, (path(a,b))).
    #
    #cnf(i_0_6, plain, (path(X3,X2)|~path(X1,X2)|~edge(X1,X3))).
    #
    #cnf(i_0_9, plain, (path(X1,c)|~edge(b,X1))).
    #
    #cnf(i_0_11, plain, (path(c,c))).
    #
    #cnf(i_0_10, plain, (path(X1,b)|~edge(a,X1))).
    #
    #cnf(i_0_13, plain, (path(b,b))).
    #
    #cnf(i_0_12, plain, (path(X1,c)|~edge(c,X1))).
    #
    #cnf(i_0_14, plain, (path(X1,b)|~edge(b,X1))).
    #
    #cnf(i_0_15, plain, (path(c,b))).
    #
    #cnf(i_0_16, plain, (path(X1,b)|~edge(c,X1))).
    
    # No proof found!
    # SZS status Satisfiable
    # Processed positive unit clauses:
    cnf(i_0_3, plain, (edge(a,b))).
    cnf(i_0_4, plain, (edge(b,c))).
    cnf(i_0_7, plain, (path(b,c))).
    cnf(i_0_8, plain, (path(a,b))).
    cnf(i_0_11, plain, (path(c,c))).
    cnf(i_0_13, plain, (path(b,b))).
    cnf(i_0_15, plain, (path(c,b))).
    
    # Processed negative unit clauses:
    
    # Processed non-unit clauses:
    cnf(i_0_5, plain, (path(X1,X2)|~edge(X1,X2))).
    cnf(i_0_6, plain, (path(X1,X2)|~path(X3,X2)|~edge(X3,X1))).
    cnf(i_0_9, plain, (path(X1,c)|~edge(b,X1))).
    cnf(i_0_10, plain, (path(X1,b)|~edge(a,X1))).
    cnf(i_0_12, plain, (path(X1,c)|~edge(c,X1))).
    cnf(i_0_14, plain, (path(X1,b)|~edge(b,X1))).
    cnf(i_0_16, plain, (path(X1,b)|~edge(c,X1))).
    
    # Unprocessed positive unit clauses:
    
    # Unprocessed negative unit clauses:
    
    # Unprocessed non-unit clauses:
    

In particular focus on the positive unit clause section

```
    # Processed positive unit clauses:
    cnf(i_0_3, plain, (edge(a,b))).
    cnf(i_0_4, plain, (edge(b,c))).
    cnf(i_0_7, plain, (path(b,c))).
    cnf(i_0_8, plain, (path(a,b))).
    cnf(i_0_11, plain, (path(c,c))).
    cnf(i_0_13, plain, (path(b,b))).
    cnf(i_0_15, plain, (path(c,b))).
```

So these provers in their rawest black box form can't really be used as datalogs, but if we peer under the covers a bit at the operational mechanisms, we can do it.

Even more so than that, in terms of pure raw mechanism these systems subsume things like equality saturation and knuth bendix completion. The difficulty id controlling them well enough to get the thing we want out.

# Ordered Resolution and Selection

The naive form of ground binary resolution looks like this. Regardless of whether A is true or false, we know one at least one of the clauses C and D is true.

```
C \/ A    ~A \/ D
-----------------
     C \/ D  
```

Our nontermination with eprover is because yea, this would just keep growing because the rule `path(X,Z) | ~edge(X,Y) | ~path(Y,Z)` could resolve against itself forever.

[Ordered resolution](https://lawrencecpaulson.github.io/papers/bachmair-hbar-resolution.pdf) is a paradigm for restricting the resolution process while maintaining completeness. It only requires certain resolutions to go through that fit the conditions of a term ordering and literal selection function.

An idea that is both simple and complex is that of [Term Orderings](https://www.cs.unm.edu/~mccune/prover9/manual/2009-11A/term-order.html). Sometimes, it makes sense to have an ordering on terms (simpler, smaller, faster, more expanded/foiled, defined earlier are all possible natural partial orders on terms). Having this play nice with unification variables/substitution and/or theories and/or alpha renaming and/or [lambda computation](https://arxiv.org/abs/1506.03943) is quite a bit trickier (rewrite and simplification orderings).

Ordered resolution kind of uses a term ordering sort of as a recipe on how to orient a `|` clause into a directed `:-` rule. If the largest literal is positive ("productive clauses"), it picked as the head. Other positive literals become negations in the body of the rule. If the largest literal is negative, then the entire clause is a constraint (Kind of a rule with head false `:- a, b, c.` You see these sorts of things in answer set programming, or you could see it if you are trying to refutation prove using datalog `false() :- a(),b(),c().`).

At the same time, a term ordering puts an ordering on the possible [Herbrand models](https://en.wikipedia.org/wiki/Herbrand_structure) (Herbrand models are sets of ground terms) of the theory, and it becomes possible to speak of a minimal model as we do in the context of datalog.

A big distinction between SAT solvers and ATPs and Datalog/Answer Set Programming is a notion of ["justification"](https://www.philipzucker.com/minikanren_inside_z3/). Datalog only derives facts that are forced to be true. SAT solvers seemingly give you a random model if there is one. Datalog gives you a particular "best" model.

Interestingly, in light of ordered resolution, there is a sense in which SAT solvers are also giving you a minimal model. It is minimal with respect to the current internal backtracking trail of the solvers, so a perspective on SAT is that it is building both a model and "good" literal ordering, or pivoting its literal ordering on the fly.

From the perspective of refutation proving, when one wants to show there can't be a satisfying model, it is sufficient to show there can't be a minimal model.

This is reminiscent of the notion of [symmetry breaking](https://en.wikipedia.org/wiki/Symmetry-breaking_constraints) in optimization that if there is some symmetry in your model (all reds can be swapped with blues in a graph coloring for example or permutations of vehicles in a routing problem), that it is useful to put an an extra ordering constraint to reduce the search space (prefer reds).

A term ordering naturally extends to an ordering on clauses. During the datalog like process to produce a minimal model (going in order through the clauses), if we hit a failing constraint, then there should have been an ordered resolution step possible to make a rule in an earlier "strata" that would have avoided the constraint failure. Carefully describing this idea is the proof of completeness of ordered resolution.

The literal selection function is basically an arbitrary function from clauses to literals. It is surprising to find that much flexibility. I don't have an intuitive feeling explanation for why this should be allowed.

Frankly, it's all a little confusing. `--literal-selection-strategy="SelectNegativeLiterals"` is sufficient to make our particular example saturate. Other possible options also work.

See slide 13 <https://www.tcs.ifi.lmu.de/lehre/ws-2024-25/atp/slides07-more-resolution.pdf>

![](/assets/ordered_resolve.png)

The key thing that is making our example terminate is probably "Nothing is Selected in D \/ B". The "rule" clauses have negative literals in them, so they will have something selected by the `SelectNegativeLiterals` strategy. The facts are a single positive unit literal, so will never have anything selected.

# Super Datalog and Beyond

These superposition systems however go far beyond datalog. It is under the capabilities of their calculus to be (with the appropriate clause prioerity, selection functions, and literal orderings)

- Knuth Bendix completion
- Prolog
- Egraphs
- Equality Saturation
- Hypothetical Datalog <https://www.philipzucker.com/contextual-datalog/>
- Contextual Egraphs <https://github.com/eytans/easter-egg> <https://arxiv.org/abs/2305.19203>
- Lambda egraphs via the new HO extensions to eprover

### Call Graphs as Ordering in Prolog and Datalog

Prolog and Datalog have a couple different notions of ordering in them.

- In prolog, the predicates in the body are ordered and the order that the rules appear also matters. More than that we kind of think of prolog as sort of a chain of function calls. The rules with a particular head define that predicate, and the body of the rule are the functions they rely on. The rules are an almost direct representation of the call graph <https://en.wikipedia.org/wiki/Call_graph> of the program (the graph of which functions call which functions). Recursive calls show up as self edges in the call graph, or mutually recursive definitions show up as connected components.
- In datalog, there is a derived notion of strata. Strata are again the connected components of the dependency graph of predicates. They are useful to note as an optimization, but crucially semantically important to note for one proper notion of negation

Prolog like goals are encoded as negated literals.

### Given Clause is kind of like Semi Naive Evaluation

Most if not all resolution style saturating theorem provers are organized around a given clause loops.

A pile of processed and unprocessed clauses are maintained. A clause in selected out of the unprocessed (the given clause) and all inference against the processed clauses are done. The results are thrown into the unprocessed.

This is similar to the seminaive distinction of delta (unprocessed) and old (processed) relations. The given clause procedure makes sure there is always one new thing in every attempt at inference because otherwise you are just redundantly rediscovering inferences.

Both Datalog and resolution can be executed in the naive style where you do a full inference sweep of the entire database every time.

The clause selection heuristics pick which clause to pick to be the given clause.

### Question Answering and Prolog

Question answering mode in ATPs gives you prolog like capabilities to return a substitution that makes the goal true.

 For example, consider this definition of an `add` predicate.

```python
%%file /tmp/add.pl
add(0,X,X).
add(s(X),Y,s(Z)) :- add(X,Y,Z).
```

    Overwriting /tmp/add.pl

```python
!swipl -s /tmp/add.pl -g "add(X,Y,s(s(0))),writeln([X,Y]),fail"
```

    [0,s(s(0))]
    [s(0),s(0)]
    [s(s(0)),0]
    [1;31mERROR: -g add(X,Y,s(s(0))),writeln([X,Y]),fail: false
    [0m

The equivalent in TPTP would be

```python
%%file /tmp/prolog.p
cnf(add_succ, axiom, add(s(X),Y,s(Z)) | ~add(X, Y, Z)).
cnf(add_z, axiom, add(z, Y, Y)).
fof(add_g, conjecture, ?[X,Y]: add(X,Y,s(s(z)))).
```

```python
! eprover-ho --answers=3 --conjectures-are-questions /tmp/prolog.p
```

    # Initializing proof state
    # Scanning for AC axioms
    #
    #cnf(i_0_4, plain, (add(z,X1,X1))).
    #
    #cnf(i_0_3, plain, (add(s(X1),X2,s(X3))|~add(X1,X2,X3))).
    #
    #cnf(i_0_5, negated_conjecture, ($answer(esk1_2(X1,X2))|~add(X1,X2,s(s(z))))).
    ## SZS status Theorem
    # SZS answers Tuple [[z, s(s(z))]|_]
    
    #cnf(i_0_6, negated_conjecture, ($answer(esk1_2(z,s(s(z)))))).
    #
    #cnf(i_0_7, negated_conjecture, ($answer(esk1_2(s(X1),X2))|~add(X1,X2,s(z)))).
    ## SZS answers Tuple [[s(z), s(z)]|_]
    
    #cnf(i_0_8, negated_conjecture, ($answer(esk1_2(s(z),s(z))))).
    #
    #cnf(i_0_9, negated_conjecture, ($answer(esk1_2(s(s(X1)),X2))|~add(X1,X2,z))).
    ## SZS answers Tuple [[s(s(z)), z]|_]
    
    # Proof found!

```python
! vampire --question_answering answer_literal --avatar off /tmp/prolog.p
```

    % Running in auto input_syntax mode. Trying TPTP
    % Refutation found. Thanks to Tanya!
    % SZS status Theorem for prolog
    % SZS answers Tuple [[z,s(s(z))]|_] for prolog
    % SZS output start Proof for prolog
    2. add(z,X1,X1) [input]
    3. ? [X0,X1] : add(X0,X1,s(s(z))) [input]
    4. ~? [X0,X1] : add(X0,X1,s(s(z))) [negated conjecture 3]
    5. ~? [X0,X1] : (add(X0,X1,s(s(z))) & ans0(X0,X1)) [answer literal 4]
    6. ! [X0,X1] : (~add(X0,X1,s(s(z))) | ~ans0(X0,X1)) [ennf transformation 5]
    7. ~add(X0,X1,s(s(z))) | ~ans0(X0,X1) [cnf transformation 6]
    8. ~ans0(z,s(s(z))) [resolution 7,2]
    9. ans0(X0,X1) [answer literal]
    10. $false [unit resulting resolution 9,8]
    % SZS output end Proof for prolog
    % ------------------------------
    % Version: Vampire 4.9 (commit 5ad494e78 on 2024-06-14 14:05:27 +0100)
    % Linked with Z3 4.12.3.0 79bbbf76d0c123481c8ca05cd3a98939270074d3 z3-4.8.4-7980-g79bbbf76d
    % Termination reason: Refutation
    
    % Memory used [KB]: 415
    % Time elapsed: 0.0000 s
    perf_event_open failed (instruction limiting will be disabled): Permission denied
    (If you are seeing 'Permission denied' ask your admin to run 'sudo sysctl -w kernel.perf_event_paranoid=-1' for you.)
    % ------------------------------
    % ------------------------------

### Equational Reasoning

#### Union Find

In a my egraphs 2024 talk <https://www.philipzucker.com/egraph2024_talk_done/> , I showed how to use Twee to get a union find. This is the same idea using eprover

```python
%%file /tmp/uf.p

cnf(ax1, axiom, a = b).
cnf(ax2, axiom, b = c).
cnf(ax2, axiom, c = b).
cnf(ax2, axiom, b = z).
cnf(ax2, axiom, z = c).
cnf(ax3, axiom, d = e).
```

    Overwriting /tmp/uf.p

```python
! eprover-ho --print-saturated /tmp/uf.p
```

    # Initializing proof state
    # Scanning for AC axioms
    #
    #cnf(i_0_7, plain, (b=a)).
    #
    #cnf(i_0_8, plain, (c=a)).
    ##
    #cnf(i_0_10, plain, (z=a)).
    ##
    #cnf(i_0_12, plain, (d=e)).
    
    # No proof found!
    # SZS status Satisfiable
    # Processed positive unit clauses:
    cnf(i_0_7, plain, (b=a)).
    cnf(i_0_8, plain, (c=a)).
    cnf(i_0_10, plain, (z=a)).
    cnf(i_0_12, plain, (d=e)).
    
    # Processed negative unit clauses:
    
    # Processed non-unit clauses:
    
    # Unprocessed positive unit clauses:
    
    # Unprocessed negative unit clauses:
    
    # Unprocessed non-unit clauses:
    
    

#### Egraph

I also mentioned in the talk how you can use knuth bendix completion to build an egraph out of ground equations, represent by its ground ocmpleted rewrite system

![](https://www.philipzucker.com/assets/egraph2024/egraph2.svg)
![](https://www.philipzucker.com/assets/egraph2024/egraphs_1.svg)

```python
%%file /tmp/groundshift.p
fof(shift, axiom, mul(a,two) = shift(a, one)).
fof(assoc, axiom, div(mul(a,two),two) = mul(a,div(two,two))).
fof(cancel, axiom, div(two,two) = one).
fof(unit_mul, axiom, mul(a,one) = a). 
fof(cancel, axiom, myterm = div(mul(a,two), two)).

```

    Overwriting /tmp/groundshift.p

```python
! eprover-ho --print-saturated --order-weights="myterm:100"  /tmp/groundshift.p
```

    setting user weights
    # Initializing proof state
    # Scanning for AC axioms
    #
    #cnf(i_0_4, plain, (mul(a,one)=a)).
    #
    #cnf(i_0_3, plain, (div(two,two)=one)).
    #
    #cnf(i_0_5, plain, (myterm=div(mul(a,two),two))).
    #
    #cnf(i_0_1, plain, (shift(a,one)=mul(a,two))).
    #
    #cnf(i_0_2, plain, (div(mul(a,two),two)=a)).
    #
    #cnf(i_0_5, plain, (myterm=a)).
    
    # No proof found!
    # SZS status Satisfiable
    # Processed positive unit clauses:
    cnf(i_0_4, plain, (mul(a,one)=a)).
    cnf(i_0_3, plain, (div(two,two)=one)).
    cnf(i_0_1, plain, (shift(a,one)=mul(a,two))).
    cnf(i_0_2, plain, (div(mul(a,two),two)=a)).
    cnf(i_0_5, plain, (myterm=a)).
    
    # Processed negative unit clauses:
    
    # Processed non-unit clauses:
    
    # Unprocessed positive unit clauses:
    
    # Unprocessed negative unit clauses:
    
    # Unprocessed non-unit clauses:
    
    

#### Knuth Bendix Completion

Knuth Bendix completion is a way to possibly turn a system of equations into a conlfuent terminating rewrite system. One example where t5his is possible is the free group. The default ordering of E is Knuth Bendix Ordering.

Maybe you're better off using Twee or [Waldmeister](https://www.mpi-inf.mpg.de/departments/automation-of-logic/software/waldmeister/download) (btw where is the waldmeister source? Is it still developed?). Not sure.

<https://www.metalevel.at/trs/>

```python
%%file /tmp/grp.p
cnf(ax1, axiom, mul(X,mul(Y,Z)) = mul(mul(X,Y),Z)).
cnf(ax2, axiom, mul(e,X) = X).
cnf(ax3, axiom, mul(inv(X), X) = e).
```

    Overwriting /tmp/grp.p

```python
!eprover-ho --print-saturated /tmp/grp.p
```

    # Initializing proof state
    # Scanning for AC axioms
    # mul is associative
    #
    #cnf(i_0_5, plain, (mul(e,X1)=X1)).
    #
    #cnf(i_0_6, plain, (mul(inv(X1),X1)=e)).
    #
    #cnf(i_0_4, plain, (mul(mul(X1,X2),X3)=mul(X1,mul(X2,X3)))).
    #
    #cnf(i_0_8, plain, (mul(inv(X1),mul(X1,X2))=X2)).
    #
    #cnf(i_0_13, plain, (mul(inv(e),X1)=X1)).
    #
    #cnf(i_0_12, plain, (mul(inv(inv(X1)),e)=X1)).
    #
    #cnf(i_0_16, plain, (mul(inv(inv(e)),X1)=X1)).
    #
    #cnf(i_0_23, plain, (inv(e)=e)).
    #
    #cnf(i_0_11, plain, (mul(inv(inv(X1)),X2)=mul(X1,X2))).
    #
    #cnf(i_0_12, plain, (mul(X1,e)=X1)).
    #
    #cnf(i_0_33, plain, (inv(inv(X1))=X1)).
    #
    #cnf(i_0_38, plain, (mul(X1,inv(X1))=e)).
    #
    #cnf(i_0_39, plain, (mul(X1,mul(inv(X1),X2))=X2)).
    ##
    #cnf(i_0_42, plain, (mul(X1,mul(X2,inv(mul(X1,X2))))=e)).
    #
    #cnf(i_0_61, plain, (mul(X2,inv(mul(X1,X2)))=inv(X1))).
    #
    #cnf(i_0_78, plain, (mul(inv(mul(X1,X2)),X1)=inv(X2))).
    #
    #cnf(i_0_77, plain, (inv(mul(X2,X1))=mul(inv(X1),inv(X2)))).
    ##
    # No proof found!
    # SZS status Satisfiable
    # Processed positive unit clauses:
    cnf(i_0_5, plain, (mul(e,X1)=X1)).
    cnf(i_0_6, plain, (mul(inv(X1),X1)=e)).
    cnf(i_0_4, plain, (mul(mul(X1,X2),X3)=mul(X1,mul(X2,X3)))).
    cnf(i_0_8, plain, (mul(inv(X1),mul(X1,X2))=X2)).
    cnf(i_0_23, plain, (inv(e)=e)).
    cnf(i_0_12, plain, (mul(X1,e)=X1)).
    cnf(i_0_33, plain, (inv(inv(X1))=X1)).
    cnf(i_0_38, plain, (mul(X1,inv(X1))=e)).
    cnf(i_0_39, plain, (mul(X1,mul(inv(X1),X2))=X2)).
    cnf(i_0_77, plain, (inv(mul(X1,X2))=mul(inv(X2),inv(X1)))).
    
    # Processed negative unit clauses:
    
    # Processed non-unit clauses:
    
    # Unprocessed positive unit clauses:
    
    # Unprocessed negative unit clauses:
    
    # Unprocessed non-unit clauses:
    
    

#### Egglog

The essence of [egglog](https://github.com/egraphs-good/egglog) in the same way the essence of datalog is the transitivity query is the connected component compression query (<https://kmicinski.com/assets/byods.pdf> section 5.4).

Here the compressed database holds a union find (The `=` facts, which are oriented according to the default term ordering). Notice that `path(b,b)` is deduped with respect to `path(d,d)` because they are expressing the same information.

```python
%%file /tmp/path.p

cnf(edgeab, axiom, edge(a,b)).
cnf(edgebc, axiom, edge(b,c)).
cnf(edgecd, axiom, edge(c,b)).
cnf(edgedc, axiom, edge(d,c)).
cnf(edgecd, axiom, edge(c,d)).

cnf(edge_is_path , axiom, path(X,Y) | ~edge(X,Y)).
cnf(path_trans, axiom, path(X,Z) | ~edge(X,Y) | ~path(Y,Z)).
cnf(path_eq, axiom, X = Y | ~path(X,Y) | ~path(Y,X)).

```

    Overwriting /tmp/path.p

```python
! eprover-ho --print-saturated --literal-selection-strategy="SelectNegativeLiterals" /tmp/path.p
```

    # Initializing proof state
    # Scanning for AC axioms
    #
    #cnf(i_0_9, plain, (edge(a,b))).
    #
    #cnf(i_0_10, plain, (edge(b,c))).
    #
    #cnf(i_0_11, plain, (edge(c,b))).
    #
    #cnf(i_0_13, plain, (edge(c,d))).
    #
    #cnf(i_0_12, plain, (edge(d,c))).
    #
    #cnf(i_0_14, plain, (path(X1,X2)|~edge(X1,X2))).
    #
    #cnf(i_0_17, plain, (path(d,c))).
    #
    #cnf(i_0_18, plain, (path(c,d))).
    #
    #cnf(i_0_19, plain, (path(c,b))).
    #
    #cnf(i_0_20, plain, (path(b,c))).
    #
    #cnf(i_0_21, plain, (path(a,b))).
    #
    #cnf(i_0_16, plain, (X1=X2|~path(X2,X1)|~path(X1,X2))).
    #
    #cnf(i_0_22, plain, (d=c)).
    #
    #cnf(i_0_23, plain, (c=b)).
    #
    #cnf(i_0_22, plain, (d=b)).
    #
    #cnf(i_0_18, plain, (path(b,b))).
    ##
    #cnf(i_0_12, plain, (edge(b,b))).
    ######
    #cnf(i_0_15, plain, (path(X1,X2)|~path(X3,X2)|~edge(X1,X3))).
    ##
    #cnf(i_0_28, plain, (path(X1,b)|~edge(X1,a))).
    
    # No proof found!
    # SZS status Satisfiable
    # Processed positive unit clauses:
    cnf(i_0_9, plain, (edge(a,b))).
    cnf(i_0_21, plain, (path(a,b))).
    cnf(i_0_23, plain, (c=b)).
    cnf(i_0_22, plain, (d=b)).
    cnf(i_0_18, plain, (path(b,b))).
    cnf(i_0_12, plain, (edge(b,b))).
    
    # Processed negative unit clauses:
    
    # Processed non-unit clauses:
    cnf(i_0_14, plain, (path(X1,X2)|~edge(X1,X2))).
    cnf(i_0_16, plain, (X1=X2|~path(X2,X1)|~path(X1,X2))).
    cnf(i_0_15, plain, (path(X1,X2)|~path(X3,X2)|~edge(X1,X3))).
    cnf(i_0_28, plain, (path(X1,b)|~edge(X1,a))).
    
    # Unprocessed positive unit clauses:
    
    # Unprocessed negative unit clauses:
    
    # Unprocessed non-unit clauses:
    
    

```python
%%file /tmp/eq.egg
(datatype node (a) (b) (c) (d))
(relation edge (node node))
(relation path (node node))
(edge (a) (b))
(edge (b) (c))
(edge (c) (d))
(edge (d) (c))
(edge (c) (b))

(rule ((edge x y)) ((path x y)))
(rule ((edge x y) (path y z)) ((path x z)))
(rule ((path x y) (path y x)) ((union x y)))

(run 10)
(print-function path 100)
```

    Overwriting /tmp/eq.egg

```python
!egglog /tmp/eq.egg
```

    Declared sort node.
    Declared function a.
    Declared function b.
    Declared function c.
    Declared function d.
    Declared function edge.
    Declared function path.
    Declared rule (rule ((edge x y))
              ((path x y))
                 ).
    Declared rule (rule ((edge x y)
               (path y z))
              ((path x z))
                 ).
     Declared rule (rule ((path x y)
               (path y x))
              ((union x y))
                 ).
    Ran schedule (repeat 10 (run)).
    Report: Rule (rule ((edge x y)        (path y z))       ((path x z))          ): search 0.000s, apply 0.000s, num matches 9
        Rule (rule ((edge x y))       ((path x y))          ): search 0.000s, apply 0.000s, num matches 7
        Rule (rule ((path x y)        (path y x))       ((union x y))          ): search 0.000s, apply 0.000s, num matches 5
        Ruleset : search 0.000s, apply 0.000s, rebuild 0.000s
        
    Printing up to 100 tuples of table path: 
    (path (b) (b))
    (path (a) (b))
    (
       (path (b) (b))
       (path (a) (b))
    )
    

# Bits and Bobbles

Most interesting knobs on eprover

- term-ordering. KBO vs LPO. precendence and weights
- clause priority. -x -H -D
- selection strategy

Altogether I find vampire more confusing to control when being used off label. I can kind of more or less interpret the various command line options to eprover in terms of the underlying calculus. Eprover also ships with a latex manual <https://github.com/eprover/eprover/blob/master/DOC/eprover.tex> which clarifies at least some things. Combining this + experimentation + Blanchette slides + Bachmair Ganzinger handbook of automated reasoning article is the only thing I've got.

I'm intrigued at the idea of using eprover as an operational mechanism rather than a solver for first order logic. A surface language which exposes more things like selection and clause ordering would be nice. I want a happy controllable predictable medium between datalog, prolog, and atp.

Prover9 exposes knobs and operational view is more emphasized

Are the orderings in datalog/prolog more like clause orderings, literal orderings, or selection. Or is this all not that related?
Goal clause prioritization "PreferGoals" `PreferGroundGoals` `

Hypthoetical datalog
`a -| b :- c.` The partially applied transitive rule is kind of a new hypthetical rule. If all variables are grounded in c, this is a what I have called hypothetical datalog.

I'm not entirely clear that selection is persay the thing that makes eprover terminate. The option may be kicking on a subsumption mechanism, which is what is really making it saturate?

The only difference under --print-strategy is

```
NoSelection: Perform ordinary superposition without selection.

SelectNegativeLiterals: Select all negative literals. For Horn clauses, this
implements the maximal literal positive unit strategy [Der91] previously
realized separately in E.
```

<https://domino.mpi-inf.mpg.de/internet/reports.nsf/c125634c000710cec125613300585c64/19a118dff60c0790c12572ff002b586a/$FILE/MPI-I-2007-RG1-001.pdf>
Superposition for Finite Domains (Plain Text
Version) Thomas Hillenbrand Christoph Weidenbach

|  | Propositions | Equations |
|---|------|------------|
| Brute Search | Resolution     |   Paramodulation         |
| Ordered Search | Ordered Resolution | Superposition |
| ? | Knuth Bendix Completion |
| Ground | Ground Ordered Resolution | EGraph |
| Goal Driven, Imperative, stacky | Prolog | Functional Logic Programming |
|Bottom Up Ground | Datalog | Egglog |
| Unoriented | Clause `|` | Eq `=` |
| Oriented   | rule `:-` | Rewrite `->` |

The features that make these provers powerful refutation provers make them harder to interpret when using them for other purposes like saturation.

Vampire has a ton of bells and whistles and it is harder for me to figure out how to control them.
E exposes more options that make sense to me and has a smaller core calculus.

Both have mechanisms that defer to smt/sat solvers to try to use their strengths (see AVATAR and splitting). When this occurs, I am more confused on how to interpret the model they've found.

We are running our theorem proving somewhat unusually in that we are really seeking a notion of saturated database/clause set and not trying to show unsat / refutation proof.

At this point, I think I prefer the `cnf` notation better than the `fof` notation. The precendence of `fof` is so unintuitive to me (and I suspect ) that I end up putting.

Unlike in prolog `|` has no intrinsic ordering. In datalog, the ordering of `,` commonly does not have operational meaning either.

The transitivity closure query is a little tired, but it really is the essence of datalog.

One aspect of datalog I find compelling is that it mirrors my simplistic image of what logic even is. Logic is axioms in some language and inference rules that take in theorems and produce new theorems. The set of all provable states is the closure of the axioms under the rules.

Resolution theorem proving is a little more involved. It is
You have clauses and you you can make an inference by smushing them together.

This is a method for classical first order logic because you can use skolemization to put the system into prenex normal form, where all the existential quantifiers are pushed outside the forall quantifiers via skolemization.  <https://en.wikipedia.org/wiki/Skolem_normal_form>

Clauses `a | c | ~d`

Resolution allows matching of rules against rules instead of only rule against facts.

<https://dl.acm.org/doi/10.1145/321250.321253> A Machine-Oriented Logic Based on the Resolution Principle - Robinson 1965

<https://en.wikipedia.org/wiki/Herbrand_structure>
<https://en.wikipedia.org/wiki/Herbrand%27s_theorem>

```
 D \/ B      C \/ ~A
-------------------
   sigma[D \/ C]

```

- $\sigma = mgu(A,B)$
- ...
- Nothing is selected in `D \/ B`
- `~A` is selected or ...

```python
import clingo
prog = """
edge(1,2;3,4).
path(X,Y) :- edge(X,Y).
"""
ctl = clingo.Control()
ctl.add(prog)
ctl.ground([("base",[])])
ctl.
```

    <clingo.control.Control at 0x7bed3d33eef0>

```python
%%file /tmp/path.p
edge(1,2; 2,3; 3,4).
path(X,Y) :- edge(X,Y).
path(X,Z) :- edge(X,Y), path(Y,Z).
```

    Overwriting /tmp/path.p

```python
! python3 -m clingo --text /tmp/path.p
```

    edge(1,2).
    edge(2,3).
    edge(3,4).
    path(1,2).
    path(2,3).
    path(3,4).
    path(2,4).
    path(1,3).
    path(1,4).

other datalogs to checkout

<https://inst.eecs.berkeley.edu/~cs294-260/sp24/2024-02-05-datalog>

- <https://s-arash.github.io/ascent/>
- slog
- gpu datalog
- logica
- dusa

- <https://www.philipzucker.com/notes/Logic/answer-set-programming/>
- <https://www.philipzucker.com/notes/Languages/datalog/>

# Superposition

atomic ground superposition - a contextual union find
ground superposition

colored egraphs

brainiac

cruanes slides <https://simon.cedeela.fr/assets/jetbrains_2021.pdf>

blanchette slides <https://www.tcs.ifi.lmu.de/lehre/ws-2024-25/atp/slides12-superposition.pdf>

model is ground rewrite rules = egraph?

weidenbach draft?
SCL simple clause
cdcl and superposition

The layering of ordering resolution (set knuth bendix) + equations (term knuth bendix) reminds me of my idea of egraph modulo theory / theory union finds as layers.

```python

# Horn
class Clause():
    hyps : list[tuple[int,int]] # negative literals
    conc : tuple[int,int]



def superpose(c1 : Clause, c2 : Clause):
    if c1.conc[0] == c2.conc[0]:
        x,y = c1.conc[1], c2.conc[1]
        if x < y:
            x,y = y,x
        return Clause(sorted(set(c1.hyps + c2.hyps)), (x,y))

def neg_superpose(c1 : Clause, c2 : Clause):

def equality_res():
    # delete all hyps of the form x=x

def factor():



```

# Ordered Ground Resolution

### Model Building and Completeness

Model Existence.

We want to pick a particular herbrand model. There are many. Pick an ordering.

Minimal herbrand makes sense in the context of datalog / horn clauses...

refutation Completeness proofs in general involve building models from saturated clauses (?) Robinson <https://web.stanford.edu/class/linguist289/robinson65.pdf>

In egraphs, we rag on completeness as silly. How silly is it?

### Knuth Bendix Analogy

Ordered Resolution completes a set of clauses into rules.
The rules can convert a ground database into a normal implied form. (The intensional to extensional database. The base facts to the ).

Consistency checks `:- a,b,c.` may mean that it is insistent to add certain base facts.

Alternative usage.

set rewriting = datalog
ordered resolution = knuth bendix for set rewriting
rewriting (ground) herbrand models.

Take a set of extra ground facts and close them out to minimal model that contains them, or possibly say they are inconstiant.

certain ground facts are equivalent under the axioms. ordered resolution builds the decision procedure.

strata ordering
accumulating semantics. obviously confluent if no negation.
{a, c} not b --> {d}

Convert clauses into datalog rules

datalog rules are like rewrite rules. They are oriented clauses.
You can run a base set of facts into a caonnical model.
Confluence.

dually, resolution/superposition is perhaps a generalized e-unification. Negated `p(A) != p(B)` can factor into stuff.
maybe splitting makes this correspondance better?

<https://www.philipzucker.com/string_knuth/>

body of rules and db are made of the same thing (?) This was part of the SQL = homomorphisms post. That the query and db are surprisingly symmetrical.

| Prop  |  Eq |
|---|---|
| Unoriented | Clause    | Equation |
| Oriented   | Rule `:-` | Rewrite |
| |   Ordered Resolution | KB |

```python
def subseq(body,  db):
    pass

def replace(db, body, head):
    """replace in quotes since monotonic"""
    pass

def rewrite(db, rules):
    # aka saturate

def overlaps(body1, body2):

def deduce():
    """find all critical pairs"""
    pass

def KB(clauses): # clauses ~ E
    done = False
    

```

### SAT solving comparison

sat solvers do not take it an a priori literal ordering. They discover a useful one via heuristics and pivoting.

<https://types.pl/@sandmouth/113528558531822923>
"""
there’s a fascinating viewpoint I’ve only become aware of in the last week that sat solvers in a sense do output a minimal model, they just don’t accept a definition of minimality in the form of a literal ordering nor do they output the ordering they discovered (which exists in the form of their internal decision and propagation trail). Ordered resolution by constrast <https://lawrencecpaulson.github.io/papers/bachmair-hbar-resolution.pdf> takes in an a priori definition of which literals you prefer to be true/false, which in turn tells you how to orient clauses into rules. The maximum positive literal of the clause is the head and any other positive literals become negations in the rule body. It’s a really interesting knob to travel between prolog and datalog and in between. It’s kind of like user defined datalog strata or something. I think this stuff is under explained nor properly translated to a logic programming viewpoint (at least in any reference I’ve read so far)
"""

ASP maybe is like SAT except the rule orientations are chosen.
What is conflict vs producing is preordianned by user.

### Splitting

Add an extra dimension to the reolsution style search. Instead of being purely sturating, we can fork our clause databases making a guess as to which part of the clause is true.

A clause can always be split by introducing a fresh symbol `q` that hodls the shared variables. If no shared varaibles, then q is propsitional and amenable to SAT solving / branching more easily. `q` can also be kind of seen as a propsotional clause abstraction / cegar. SAT modulo Resolution.
`a(X,Y) | b(Y,W)` ->  `q(Y) | a(X,Y)`  `~q(Y) | b(Y,W)`

Grounding. You can randomly (?) pick any instantiaions of clauses and then toss into SMT/SAT solver. If that grounding is unsat, cool.

AVATAR

<https://www.cl.cam.ac.uk/~lp15/papers/Arith/case-splitting.pdf>

```python
%%file 
```

### Logic Programming

The combination of the ordering and selection feels like a knob to tweak between prolog and datalog and other things. It would be nice to have a crisper picture of this.

- hyperresolution
- locking resolution <https://www.doc.ic.ac.uk/%7Ekb/MACTHINGS/SLIDES/2013Notes/7LControl4up13.pdf> boyer 1973 <https://www.cs.utexas.edu/~boyer/boyer-dissertation.pdf>
- unit resulting resolution

ordered resolution as a logic programming language

negative literals are goals. The Factoring rule is prolog style unification.

```python
# idea. preprocessor to convert to clauses + ordering + selection function.
# Or write own ordered resolution

import lark
grammar = """
rule: head ":-" selected "|" unselected.
"""
```

Marking particular predicates as selected or unselected.

```
:- constraint foo/2.  % means it isn't selected?
```

Or make it work like LPO.

```
decl foo : bar. % means it is a constructor and therefore at the bottom precedence.
```

Interactively saturate with every new definition? That would be a termination check (?)
It's kind of like elf or the termination arugments given to dafny / coq / lean etc.

`head  -| ctx  :- body.` hypothetical datalog. Maybe a notation for
`maxposliteral |  selected   | other`  CHR kind of has a multipart thing. I think in principle its just multiset rewrite rules. Its a conveience to not depelte and reinsert.
It is then the theorem provers job to discharge a term ordering that makes the max pos literal, selected literals work.
selected literals can emulate hyperresolution.

prolog vs E <https://wwwlehre.dhbw-stuttgart.de/~sschulz/E/FAQ.html>

<https://web4.ensiie.fr/~guillaume.burel/download/LFAT.pdf> focusing and atp. Focusing is a mechanism for describing the imperative nature of prolog or how the sequent claculus is like an imperative machine. <https://drops.dagstuhl.de/storage/00lipics/lipics-vol117-mfcs2018/LIPIcs.MFCS.2018.9/LIPIcs.MFCS.2018.9.pdf>

Termination checking of logic programs.
<https://www.sciencedirect.com/science/article/pii/0743106692900455>  Proving termination properties of prolog programs: A semantic approach
<https://www.metalevel.at/prolog/termination>
<https://www.cs.unipr.it/cTI/>  cTI: A Termination Inference Engine
<https://github.com/atp-lptp/automated-theorem-proving-for-prolog-verification>

elf had termination checking. But like simple syntactic.

IC3 and CHC.
IC3 vs saturation?

#### programming resolution

look at datalog program

continuation passing as an evaluation order forciong mechanism
<https://www.swi-prolog.org/pldoc/man?section=delcont> deliimited continuations?

```
call(edge(X,Y)) | ~edge(X,Y).

```

Consider more metagames I tried to play in egglog or datalog. They should be more doable.

first class clauses

`clause( poses, negs )`.

`assert`

It would be kind of cool to have computational proedciates. writeln
What was the deal with e-lop?

dcgs? Proof recording.

```
cnf(ax1, axiom, prove( A > B, Pf-Tl, Pf)).
```

This idea of staging resolution is like staging prolog.
Prolog macros? Kind of ugly as hell.
modules? Lambda prolog modules?

twelf

### Ordering

Ordering = datalog strata presciprtion

Using other term orderings -> datalog termination proofs
Or datalog consistency? Having negation but showing you won't derive then underive something.
"dynamic" stratification
This doesn't have a unique minimal model

```
b :- not a.
a :- not b.
```

This does. Stratification can't cover it though. So how to prove? Term ordering maybe.

```
b(n) :- not a(n).
a(n + 1) :- not b(n), n < 10.
```

d(1, N)
d(2, N) etc

There is some kind of redundancy symmettry in brute resolution and people have been fighting it from the beginning basically. Rewynolds, slagle, kowalski

<https://www.cs.upc.edu/~%7B%7Dalbert/cpo.zip> <https://arxiv.org/abs/1506.03943> computbility path ordering. compare types first
LPO RPO
KBO

### Selection Functions

SL SLD resolution. They use the term selection function.
<https://www.sciencedirect.com/science/article/abs/pii/0004370271900129> Linear resolution with selection function kowalski kuehner
<https://en.wikipedia.org/wiki/SLD_resolution> SLD resolution is so named S is for selection

Selection functions.
p :- not p, not q, z | a,b,c.
Some kind of CLP like syntax.
Maximalnegative/minimal does perhaps seem the most prolog like.  

Selection is like a goal ordering. a prolog rule p :- q,r,s. tries to deal with q, r, s in syntactic order. q would be selected.
But if prolog had more delcarative semantics, there might be some way for the system to pick from q,r,s as the next direction work on.

### Saturation and Proof by Consistency

inductionless induction

If we have a termination criteria / strata criteria for our prolog / datalog program, can we convert that to selection functions and a term ordering.

The prcendence gnerating routines of E seem like a nice way to fill in gaps. Syntax for constraints that put precedence or weight constraints.

Inductionless induction could be used to prove negations at lower levels?
The similaity of using induction to prove consistent (has model) is mentioned in paramodulation chapter of handbook

Could I use this to do progress and preservation proofs?
boolexpr progress proof?

```


```

Termination of lambda calculus requires the typing relation. Step-indexing. Logical relations.

### Sequents

Resolution doesn't seem to really be about classical first order logic.
neg and positive literals can be interpreted as parts of sequent. Resolution is cut.
Bachmair and ganzinger vaguely allude to macro proof steps

### Chaining

"bi-rweriting a term rewriting techniqyue for monotonic order relaTIONS" levy and agusty <https://www.iiia.csic.es/~levy/papers/RTA93.pdf>
<https://pdf.sciencedirectassets.com/272990/1-s2.0-S1571066100X00631/1-s2.0-S1571066104002968/main.pdf> Knuth-Bendix Completion for Non-Symmetric
Transitive Relations struith
<https://opus.bibliothek.uni-augsburg.de/opus4/frontdoor/index/index/year/2006/docId/229> Termination of ground non-symmetric Knuth-Bendix completion

chaining slagle 72
infinitary depth first search... ?
two rewrite relations. < + termorder and < + opptermorder

ordered chaining for total orderings <https://link.springer.com/chapter/10.1007/3-540-58156-1_32>

Rewrite Techniques for Transitive Relations

## Misc

<https://people.mpi-inf.mpg.de/~mfleury/paper/Weidenback_Book_CDCL.pdf>
Weidenbach chapter 2 draft

<https://core.ac.uk/download/303691264.pdf>  Formalizing the metatheory of logical calculi and automatic provers in Isabelle/HOL
(invited talk)
Blanchette, Jasmin Christian

<https://www.tcs.ifi.lmu.de/lehre/ws-2024-25/atp/paper.pdf>  Automated Theorem Proving∗ Dr. Uwe Waldmann

Types are dsichagred differently. see weidnebach chapter.
Type check ~ static.
A stratification of inference.
Stratification either comes from orderings, or explicit quasiquote thingy. Like z3py meta. Like two level type kovacs. like metaocaml. like HOL quote carette and farmer <https://arxiv.org/abs/1802.00405>
One could implement a quote mechanism inside of an ATP. Kind of an interesting idea.

Saturated clauses -> minimal model (according to that ordering)
Alterantive - push pop search in order of ordering to SAT solver.
Can cut out branches that are unsat.

Bachmair and ganzinger in handbook
<https://www.isa-afp.org/entries/Functional_Ordered_Resolution_Prover.html>

hypothetical datalog?
 |-
Ground database

minimal proofs

<https://rg1-teaching.mpi-inf.mpg.de/autrea-ws21/notes-3d.pdf> ordered resolution with selection waldemann.

<https://www.tcs.ifi.lmu.de/lehre/ws-2024-25/atp_de.html>
<https://www.tcs.ifi.lmu.de/lehre/ws-2024-25/atp/slides05-resolution.pdf>
ordering stratifies clause set by their maximal atom

polynomial unification. Restrict unfication to do small terms first
(guassian pivoting?)

<https://dl.acm.org/doi/pdf/10.1145/321420.321428> slagle 1967

Building a model from a saturation.

switching from ground to nonground makes > become !<=

sequent calculus and resolution. Cut or macro rules?
The multiset chjaracter of alsues makes permutation symettry

stratified resolution

2-sat ~ congruence closure?

`a | b` orients to `a :- b`

a | b | c. is a 3 way symmettric thing.

Multiequations a = b = c ? Could that be cogent?
a = b = c as a triangle. higher dimesional rewriting. ab -> c oriented.
Hmm. kind of jives with the equations = paths stuff.
unification sometimes uses the term.
a = b | c = d

Bachmair
Ganzigner
Niewenhuis <https://www.cs.upc.edu/~roberto/>
Rubio <https://www.cs.upc.edu/~albert/> <https://link.springer.com/chapter/10.1007/978-3-642-31585-5_21> nominal completion
waldemann <https://dblp.org/pid/w/UweWaldmann.html>
weidenbach
stickel
wayne snyder
hillenbrand
kuehner
kowalski
slagle
veroff
wos
suda
loveland
blanchette
bledsoe
gallier
baader
nipkow

<https://resources.mpi-inf.mpg.de/SATURATE/Saturate.html>
<https://resources.mpi-inf.mpg.de/SATURATE/doc/Saturate/node11.html>
transitive relations have special inference rule. chaining. paramdodulation is an instance...

Loveland book

<https://link.springer.com/article/10.1007/BF01190829> 1994 ganziner bachmair waldeman

whoa. this is insane <https://people.mpi-inf.mpg.de/alumni/ag2/2011/hg/index/index7.html>
I need to read like ganzinger's entire work
especially part 2.

mcallester. steensgard analysis

<https://www3.risc.jku.at/conferences/rta2008/slides/Slides_Hillenbrand.pdf> hillenbrand waldmeisetrt. in mathematica?

lock resolution
"the inverse method can also be encoded"

Bachmair and Ganzinger
"non-clausal reoslution and superposition wioth seelction and redunancy criteri"
"perfoect model semantics for logic programs with equality"
"rewirte based equational theorem proving with selection and simplification"
"rewrite techniques with transitive relations"
"ordered chaining for total orderings"

<https://www.sciencedirect.com/science/article/pii/S0890540106000617?via%3Dihub>  Modular proof systems for partial functions with Evans equality. Total and partial functions
Kuper  <https://www.sciencedirect.com/science/article/pii/S0890540183710631>  An Axiomatic Theory for Partial Functions
<https://www21.in.tum.de/students/set_theory_partial_functions/index.html> Formalising Set Theory Based on Partial Functions
<https://page.mi.fu-berlin.de/cbenzmueller/papers/C57.pdf>  Automating Free Logic in Isabelle/HOL

Man a return to form of category theory blog post 0. Flat is good anyway.
Avoiding junk elements is good.
Fun,El,El choiuce is like SEAR
Fun,Fun,Fun choice is like ETCS

subsets are partial functions to bool.
f(x) undef means x isn't in domain.
f(x) = false means not in subset
f(x) = true means in subset

```
DeclareSort("Fun")
# apply as ternary
apply = Function("apply", Fun, El, El, BoolSort()) # Fun Fun Fun?
undef = define("undef", [f,x], Not(Exists([y], apply(f,x,y))))
# f.x ~ y   notation for apply(f,x,y) is nice. Hard to see how to do this in python. Could make parser. Or overload __eq__ to check for a call. Hmmmm.

""" put partial application at metalevel."""

class PApply():
    f : Fun
    x : PApply | Fun # enable recursive expressions.
    def __eq__(self, y):
        if isinstance(y, ExprRef):
            return apply(self.f, self.x, y)
    def __call__(self, y):
        return PApply(self, y)
    def defined(self):
        return Exists([y], self == y)

def apply_eq(fx,y):
    if is_app(fx) and  fx.decl() == apply:
        return return fx[2] == y
    else:
    return apply(fx[0],fx[1],y)


```

<https://github.com/NikolajBjorner/ShonanArtOfSAT/blob/main/AkihisaYamada-slides.pdf>
satisfiability modulo rewriting
WP
CPO
HORPO

books
troesltra
pohlers proof thoery
takeuti
zach proof theory
handbook of proof theory
girard

kleene metamartrhemtics
computability theory by

theory resolution stickel 1985

vampire for QBF?

```
cnf( v(B) | v(c) )
v(skolem(A))
```

vampire for modal / intuitonsitc? Judicious choice of ordering /precdence to help?
<https://ieeexplore.ieee.org/document/848641> Chaining techniques for automated theorem proving in many-valued logics

nonclausal resolution
<https://www.sciencedirect.com/science/article/pii/S0890540105000258> Superposition with equivalence reasoning and delayed clause normal form transformation

### Saturate

<https://resources.mpi-inf.mpg.de/SATURATE/Saturate.html>
INteresting system. Interesting example files.
I doubt I can get this running

Saturation of first-order (constrained) clauses with the Saturate system <https://dl.acm.org/doi/10.5555/647193.720661>

```python
# clauses as sorted list
# use integer ids. negative for negative literals if we want those to come first?
atoms = []





```

## python

We pick the (name, neg) encoding because in python
{A,A} is neg lit
{A} is pos lit

is the same ordering as

(A, True) is neg lit
(A, False) is pos lit

Lesser things are "simpler" in some sense. "Smaller". We try to eliminate to lesser things.

Given saturated clause set, contruct model.

```python
def c(*ls): return sorted(ls,reverse=True, key=lambda x: (x[0], x[1]))
def l(atom, neg=False): return (atom,neg)
def cset(*cs): return sorted(cs)
def maxlit(c): return c[0]
def maxatom(c): return c[0][0]

b0,a0,b1,a1,b2,a2 = map(lambda x: l(x), "0b 0a 1b 1a 2b 2a".split())
nb0, na0, nb1, na1, nb2, na2 = map(lambda x: l(x, neg=True),  "0b 0a 1b 1a 2b 2a".split())

N = cset(
    c(b0, a1),
    c(a0, b0),
    c(nb0, a1),
    c(nb0, b1, nb0, b1),
    c(nb0, a2, b1),
    c(nb0, na2, b1),
    c(nb1, b2),
)
N
#def Ic(n): return sum(epsC(n) for i in range(n))
#def epsC(n): return {maximal(N[n])} if  else set()



```

    [[('0b', False), ('0a', False)],
     [('1a', False), ('0b', False)],
     [('1a', False), ('0b', True)],
     [('1b', False), ('1b', False), ('0b', True), ('0b', True)],
     [('2a', False), ('1b', False), ('0b', True)],
     [('2a', True), ('1b', False), ('0b', True)],
     [('2b', False), ('1b', True)]]

```python
def interp(model, clause): 
    for atom, neg in clause:
        if neg:
            if atom not in model:
                return True
        else:
            if atom in model:
                return True
    return False
    #return any(atom not in model if neg else atom in model for (atom, neg) in model)
Ic = set()
for c in N:
    print(Ic, c, interp(Ic, c))
    if not interp(Ic, c):
        atom,neg = maxlit(c)
        if neg:
            raise Exception("counterexample", c, Ic)
        Ic.add(atom)
Ic

```

    set() [('0b', False), ('0a', False)] False
    {'0b'} [('1a', False), ('0b', False)] True
    {'0b'} [('1a', False), ('0b', True)] False
    {'1a', '0b'} [('1b', False), ('1b', False), ('0b', True), ('0b', True)] False
    {'1a', '0b', '1b'} [('2a', False), ('1b', False), ('0b', True)] True
    {'1a', '0b', '1b'} [('2a', True), ('1b', False), ('0b', True)] True
    {'1a', '0b', '1b'} [('2b', False), ('1b', True)] False





    {'0b', '1a', '1b', '2b'}

Selection functions take in clause and select some subset of the negative literals.

Negative and positive literals are not treated symmetrically by the model generation process.
A little odd. I think we could have the model generation have everything true by default and derive not trues

```python
def allsel(c): return [atom for (atom, neg) in c if neg]
def nonesel(c): return []
def maxsel(c): return max(allsel(c))
def minsel(c): return min(allset(c))

def ordered_resolve(pc,nc): # positive and negative clause
    (a,neg) = maxlit(pc)
    assert not neg
    (b,neg) = maxlit(nc)
    assert neg
    assert a == b
    return cset(pc[1:] + nc[1:])

# https://www.tcs.ifi.lmu.de/lehre/ws-2024-25/atp/slides07-more-resolution.pdf
def resolve_osel(pc,nc,sel):
    assert len(sel(pc)) == 0
    a,neg = maxlit(pc)
    assert not neg
    bs = sel(nc)
    if len(bs) == 0:
        b,neg = maxlit(nc)
        assert neg
        return cset(pc[1:] + nc[1:])
    else:
        for b in bs:
            if b == a:
                c = nc.copy().remove((b,True))
                c.extend(pc[1:])
                return cset(c)

def factor(c,sel):
    a,neg = maxlit(c)
    assert c[1] == (a, neg)
    assert len(sel(c) == 0)
    return c[2:]





```

Are the any subsumption/redundant rules that work on ordered ground resolution?

Connection to SAT search (counterexample clauses? unit propagate )
Connection to sequents and other logics. Mega steps of inference

abstract dpll
<https://gist.github.com/kmicinski/17dffc8b2cbbd4f3264071e19ae75dfa> See this paper: <https://homepage.cs.uiowa.edu/~tinelli/papers/NieOT-JACM-06.pdf>

Otter vs discount loop

```python
from collections import defaultdict
def clausedict(cs):
    pcs,ncs = defaultdict(list),defaultdict(list)
    for c in cs:
        a,neg = maxlit(c)
        if neg:
            ncs[a].append(c)
        else:
            pcs[a].append(c)
    return pcs,ncs

def saturate(N):
    passive = N
    active = []
    while passive:
        passive.pop()

```

A term ordering gives a clause ordering.

Producing clauses.
A tern ordering turns a set of clauses into a model generating datalog / prolog program
The produced maximal atom is the head of a clause.
The strata are the levels.

This is ASP like.

blanchette had those slides about completeness discussing how models get built

## 2sat

```python

```

# METIS

<https://www.gilith.com/metis/>
ordered paramodulation
<https://github.com/gilith/metis>

# Eprover

```
  --expert-heuristic=<arg>
    Select one of the clause selection heuristics. Currently at least
    available: Auto, Weight, StandardWeight, RWeight, FIFO, LIFO, Uniq,
    UseWatchlist. For a full list check HEURISTICS/che_proofcontrol.c. Auto
    is recommended if you only want to find a proof. It is special in that it
    will also set some additional options. To have optimal performance, you
    also should specify -tAuto to select a good term ordering. LIFO is unfair
    and will make the prover incomplete. Uniq is used internally and is not
    very useful in most cases. You can define more heuristics using the
    option -H (see below).

      --split-clauses[=<arg>]
    Determine which clauses should be subject to splitting. The argument is
    the binary 'OR' of values for the desired classes:
         1:  Horn clauses
         2:  Non-Horn clauses
         4:  Negative clauses
         8:  Positive clauses
        16:  Clauses with both positive and negative literals
    Each set bit adds that class to the set of clauses which will be split.
    The option without the optional argument is equivalent to
    --split-clauses=7.

  --split-method=<arg>
    Determine how to treat ground literals in splitting. The argument is
    either '0' to denote no splitting of ground literals (they are all
    assigned to the first split clause produced), '1' to denote that all
    ground literals should form a single new clause, or '2', in which case
    ground literals are treated as usual and are all split off into
    individual clauses.

       -H <arg>
  --define-heuristic=<arg>
    Define a clause selection heuristic (see manual for details). Later
    definitions override previous definitions.
```

Special clause type `watchlist`

## Union find

In a my egraphs 2024 talk <https://www.philipzucker.com/egraph2024_talk_done/> , I showed how to use twee to get a union find. This is the same idea

```python
%%file /tmp/uf.p

cnf(ax1, axiom, a = b).
cnf(ax2, axiom, b = c).
cnf(ax2, axiom, c = b).
cnf(ax2, axiom, b = z).
cnf(ax2, axiom, z = c).
cnf(ax3, axiom, d = e).
%cnf(ax4, axiom, d != a).
```

    Overwriting /tmp/uf.p

```python
! eprover-ho --print-saturated /tmp/uf.p
```

    # Initializing proof state
    # Scanning for AC axioms
    #
    #cnf(i_0_7, plain, (b=a)).
    #
    #cnf(i_0_8, plain, (c=a)).
    ##
    #cnf(i_0_10, plain, (z=a)).
    ##
    #cnf(i_0_12, plain, (d=e)).
    
    # No proof found!
    # SZS status Satisfiable
    # Processed positive unit clauses:
    cnf(i_0_7, plain, (b=a)).
    cnf(i_0_8, plain, (c=a)).
    cnf(i_0_10, plain, (z=a)).
    cnf(i_0_12, plain, (d=e)).
    
    # Processed negative unit clauses:
    
    # Processed non-unit clauses:
    
    # Unprocessed positive unit clauses:
    
    # Unprocessed negative unit clauses:
    
    # Unprocessed non-unit clauses:
    
    

--print-saturated=teigEIGaA --print-sat-info

```python
! eprover-ho --order-precedence-generation=none
```

    eprover: Wrong argument to option -G (--order-precedence-generation). Possible values: none, unary_first, unary_freq, arity, invarity, const_max, const_min, freq, invfreq, invconjfreq, invfreqconjmax, invfreqconjmin, invfreqconstmin, invfreqhack, typefreq, invtypefreq, combfreq, invcombfreq, arrayopt, orient_axioms

"invfreq: Sort symbols by frequency (frequently occurring symbols are smaller).
In our experience, this is one of the best general-purpose precedence gen-
eration schemes."

"The option --literal-comparison=<arg> allow the user to select alterna-
tive literal comparison schemes. In particular, literals will be first compared by
predicate symbol, and only then by full terms. This is a poor man’s version of
transfinite KBO [LW07, KMV11], applied to literals only, but also extended to
LPO."

Ah, if I use `>` unquoted bash thinks its a file redirect

"There are two uses for a watchlist: To guide the proof search (using a heuris-
tic that prefers clauses on the watchlist), or to find purely constructive proofs
for clauses on the watchlist."

```python
! eprover-ho --output-level=4  --print-saturated --term-ordering=KBO6 --precedence="a>b>c>d>e>z" /tmp/uf.p
```

    cnf(ax1, axiom, (a=b), file('/tmp/uf.p', ax1)).
    cnf(ax2, axiom, (b=c), file('/tmp/uf.p', ax2)).
    cnf(ax2, axiom, (z=c), file('/tmp/uf.p', ax2)).
    cnf(ax3, axiom, (d=e), file('/tmp/uf.p', ax3)).
    # Initializing proof state
    # Scanning for AC axioms
    cnf(c_0_5, plain, (a=c),inference(rw, [status(thm)],[c_0_-9223372036854775799,c_0_-9223372036854775798])).
    cnf(c_0_6, plain, (b=z),inference(rw, [status(thm)],[c_0_-9223372036854775798,c_0_-9223372036854775797])).
    cnf(c_0_7, plain, (a=z),inference(rw, [status(thm)],[c_0_5,c_0_-9223372036854775797])).
    cnf(c_0_8, plain, (c=z), c_0_-9223372036854775797,['final']).
    cnf(c_0_9, plain, (d=e), c_0_-9223372036854775796,['final']).
    cnf(c_0_10, plain, (a=z), c_0_7,['final']).
    cnf(c_0_11, plain, (b=z), c_0_6,['final']).
    
    # No proof found!
    # SZS status Satisfiable
    # Processed positive unit clauses:
    cnf(c_0_8, plain, (c=z)).
    cnf(c_0_9, plain, (d=e)).
    cnf(c_0_10, plain, (a=z)).
    cnf(c_0_11, plain, (b=z)).
    
    # Processed negative unit clauses:
    
    # Processed non-unit clauses:
    
    # Unprocessed positive unit clauses:
    
    # Unprocessed negative unit clauses:
    
    # Unprocessed non-unit clauses:
    
    
    # Parsed axioms                        : 4
    # Removed by relevancy pruning/SinE    : 0
    # Initial clauses                      : 4
    # Removed in clause preprocessing      : 0
    # Initial clauses in saturation        : 4
    # Processed clauses                    : 6
    # ...of these trivial                  : 0
    # ...subsumed                          : 0
    # ...remaining for further processing  : 6
    # Other redundant clauses eliminated   : 0
    # Clauses deleted for lack of memory   : 0
    # Backward-subsumed                    : 0
    # Backward-rewritten                   : 2
    # Generated clauses                    : 0
    # ...of the previous two non-redundant : 2
    # ...aggressively subsumed             : 0
    # Contextual simplify-reflections      : 0
    # Paramodulations                      : 0
    # Factorizations                       : 0
    # NegExts                              : 0
    # Equation resolutions                 : 0
    # Disequality decompositions           : 0
    # Total rewrite steps                  : 3
    # ...of those cached                   : 1
    # Propositional unsat checks           : 0
    #    Propositional check models        : 0
    #    Propositional check unsatisfiable : 0
    #    Propositional clauses             : 0
    #    Propositional clauses after purity: 0
    #    Propositional unsat core size     : 0
    #    Propositional preprocessing time  : 0.000
    #    Propositional encoding time       : 0.000
    #    Propositional solver time         : 0.000
    #    Success case prop preproc time    : 0.000
    #    Success case prop encoding time   : 0.000
    #    Success case prop solver time     : 0.000
    # Current number of processed clauses  : 4
    #    Positive orientable unit clauses  : 4
    #    Positive unorientable unit clauses: 0
    #    Negative unit clauses             : 0
    #    Non-unit-clauses                  : 0
    # Current number of unprocessed clauses: 0
    # ...number of literals in the above   : 0
    # Current number of archived formulas  : 0
    # Current number of archived clauses   : 2
    # Clause-clause subsumption calls (NU) : 0
    # Rec. Clause-clause subsumption calls : 0
    # Non-unit clause-clause subsumptions  : 0
    # Unit Clause-clause subsumption calls : 0
    # Rewrite failures with RHS unbound    : 0
    # BW rewrite match attempts            : 2
    # BW rewrite match successes           : 2
    # Condensation attempts                : 0
    # Condensation successes               : 0
    # Termbank termtop insertions          : 32
    # Search garbage collected termcells   : 0

```python
! eprover-ho --output-level=4  --print-saturated --term-ordering=KBO6 --order-weights=a:9,b:8,c:7,d:6,e:5,z:4 /tmp/uf.p
```

    cnf(ax1, axiom, (a=b), file('/tmp/uf.p', ax1)).
    cnf(ax2, axiom, (b=c), file('/tmp/uf.p', ax2)).
    cnf(ax2, axiom, (z=c), file('/tmp/uf.p', ax2)).
    cnf(ax3, axiom, (d=e), file('/tmp/uf.p', ax3)).
    setting user weights
    # Initializing proof state
    # Scanning for AC axioms
    cnf(c_0_5, plain, (a=c),inference(rw, [status(thm)],[c_0_-9223372036854775799,c_0_-9223372036854775798])).
    cnf(c_0_6, plain, (b=z),inference(rw, [status(thm)],[c_0_-9223372036854775798,c_0_-9223372036854775797])).
    cnf(c_0_7, plain, (a=z),inference(rw, [status(thm)],[c_0_5,c_0_-9223372036854775797])).
    cnf(c_0_8, plain, (c=z), c_0_-9223372036854775797,['final']).
    cnf(c_0_9, plain, (d=e), c_0_-9223372036854775796,['final']).
    cnf(c_0_10, plain, (a=z), c_0_7,['final']).
    cnf(c_0_11, plain, (b=z), c_0_6,['final']).
    
    # No proof found!
    # SZS status Satisfiable
    # Processed positive unit clauses:
    cnf(c_0_8, plain, (c=z)).
    cnf(c_0_9, plain, (d=e)).
    cnf(c_0_10, plain, (a=z)).
    cnf(c_0_11, plain, (b=z)).
    
    # Processed negative unit clauses:
    
    # Processed non-unit clauses:
    
    # Unprocessed positive unit clauses:
    
    # Unprocessed negative unit clauses:
    
    # Unprocessed non-unit clauses:
    
    
    # Parsed axioms                        : 4
    # Removed by relevancy pruning/SinE    : 0
    # Initial clauses                      : 4
    # Removed in clause preprocessing      : 0
    # Initial clauses in saturation        : 4
    # Processed clauses                    : 6
    # ...of these trivial                  : 0
    # ...subsumed                          : 0
    # ...remaining for further processing  : 6
    # Other redundant clauses eliminated   : 0
    # Clauses deleted for lack of memory   : 0
    # Backward-subsumed                    : 0
    # Backward-rewritten                   : 2
    # Generated clauses                    : 0
    # ...of the previous two non-redundant : 2
    # ...aggressively subsumed             : 0
    # Contextual simplify-reflections      : 0
    # Paramodulations                      : 0
    # Factorizations                       : 0
    # NegExts                              : 0
    # Equation resolutions                 : 0
    # Disequality decompositions           : 0
    # Total rewrite steps                  : 3
    # ...of those cached                   : 1
    # Propositional unsat checks           : 0
    #    Propositional check models        : 0
    #    Propositional check unsatisfiable : 0
    #    Propositional clauses             : 0
    #    Propositional clauses after purity: 0
    #    Propositional unsat core size     : 0
    #    Propositional preprocessing time  : 0.000
    #    Propositional encoding time       : 0.000
    #    Propositional solver time         : 0.000
    #    Success case prop preproc time    : 0.000
    #    Success case prop encoding time   : 0.000
    #    Success case prop solver time     : 0.000
    # Current number of processed clauses  : 4
    #    Positive orientable unit clauses  : 4
    #    Positive unorientable unit clauses: 0
    #    Negative unit clauses             : 0
    #    Non-unit-clauses                  : 0
    # Current number of unprocessed clauses: 0
    # ...number of literals in the above   : 0
    # Current number of archived formulas  : 0
    # Current number of archived clauses   : 2
    # Clause-clause subsumption calls (NU) : 0
    # Rec. Clause-clause subsumption calls : 0
    # Non-unit clause-clause subsumptions  : 0
    # Unit Clause-clause subsumption calls : 0
    # Rewrite failures with RHS unbound    : 0
    # BW rewrite match attempts            : 2
    # BW rewrite match successes           : 2
    # Condensation attempts                : 0
    # Condensation successes               : 0
    # Termbank termtop insertions          : 32
    # Search garbage collected termcells   : 0

## edge path

```python
%%file /tmp/path.p

cnf(ax2, axiom, path(X,Y) | ~edge(X,Y)).
cnf(ax1, axiom, path(X,Z) | ~edge(X,Y) | ~path(Y,Z)).
cnf(ax1, axiom, edge(a,b)).
cnf(ax2, axiom, edge(b,c)).
cnf(ax3, axiom, edge(c,d)).

```

    Overwriting /tmp/path.p

NoSelection - doesm't terminate
NoGeneration - not sure what this one is doing
SelectNegativeLiterals
SelectLargestNegLit
--precedence="path>edge"
-term-ordering=LPO4

--literal-selection-strategy="SelectSmallestNegLit"

--auto doesn't process the path
No selection doesn't terminate.

--print-strategy

Oh yea. Those non ground are necessary if there is no multi-resolution rule.

precedence does not seem to matter to final result

--filter-saturated='u'
--literal-selection-strategy="SelectSmallestNegLit"

```python
! eprover-ho --literal-selection-strategy=none
```

    eprover: Wrong argument to option -W (--literal-selection-strategy). Possible values: NoSelection, NoGeneration, SelectNegativeLiterals, PSelectNegativeLiterals, SelectPureVarNegLiterals, PSelectPureVarNegLiterals, SelectLargestNegLit, PSelectLargestNegLit, SelectSmallestNegLit, PSelectSmallestNegLit, SelectLargestOrientable, PSelectLargestOrientable, MSelectLargestOrientable, SelectSmallestOrientable, PSelectSmallestOrientable, MSelectSmallestOrientable, SelectDiffNegLit, PSelectDiffNegLit, SelectGroundNegLit, PSelectGroundNegLit, SelectOptimalLit, PSelectOptimalLit, SelectMinOptimalLit, PSelectMinOptimalLit, SelectMinOptimalNoTypePred, PSelectMinOptimalNoTypePred, SelectMinOptimalNoXTypePred, PSelectMinOptimalNoXTypePred, SelectMinOptimalNoRXTypePred, PSelectMinOptimalNoRXTypePred, SelectCondOptimalLit, PSelectCondOptimalLit, SelectAllCondOptimalLit, PSelectAllCondOptimalLit, SelectOptimalRestrDepth2, PSelectOptimalRestrDepth2, SelectOptimalRestrPDepth2, PSelectOptimalRestrPDepth2, SelectOptimalRestrNDepth2, PSelectOptimalRestrNDepth2, SelectNonRROptimalLit, PSelectNonRROptimalLit, SelectNonStrongRROptimalLit, PSelectNonStrongRROptimalLit, SelectAntiRROptimalLit, PSelectAntiRROptimalLit, SelectNonAntiRROptimalLit, PSelectNonAntiRROptimalLit, SelectStrongRRNonRROptimalLit, PSelectStrongRRNonRROptimalLit, SelectUnlessUniqMax, PSelectUnlessUniqMax, SelectUnlessPosMax, PSelectUnlessPosMax, SelectUnlessUniqPosMax, PSelectUnlessUniqPosMax, SelectUnlessUniqMaxPos, PSelectUnlessUniqMaxPos, SelectComplex, PSelectComplex, SelectComplexExceptRRHorn, PSelectComplexExceptRRHorn, SelectLComplex, PSelectLComplex, SelectMaxLComplex, PSelectMaxLComplex, SelectMaxLComplexNoTypePred, PSelectMaxLComplexNoTypePred, SelectMaxLComplexNoXTypePred, PSelectMaxLComplexNoXTypePred, SelectComplexPreferNEQ, PSelectComplexPreferNEQ, SelectComplexPreferEQ, PSelectComplexPreferEQ, SelectComplexExceptUniqMaxHorn, PSelectComplexExceptUniqMaxHorn, MSelectComplexExceptUniqMaxHorn, SelectNewComplex, PSelectNewComplex, SelectNewComplexExceptUniqMaxHorn, PSelectNewComplexExceptUniqMaxHorn, SelectMinInfpos, PSelectMinInfpos, HSelectMinInfpos, GSelectMinInfpos, SelectMinInfposNoTypePred, PSelectMinInfposNoTypePred, SelectMin2Infpos, PSelectMin2Infpos, SelectComplexExceptUniqMaxPosHorn, PSelectComplexExceptUniqMaxPosHorn, SelectUnlessUniqMaxSmallestOrientable, PSelectUnlessUniqMaxSmallestOrientable, SelectDivLits, SelectDivPreferIntoLits, SelectMaxLComplexG, SelectMaxLComplexAvoidPosPred, SelectMaxLComplexAPPNTNp, SelectMaxLComplexAPPNoType, SelectMaxLComplexAvoidPosUPred, SelectComplexG, SelectComplexAHP, PSelectComplexAHP, SelectNewComplexAHP, PSelectNewComplexAHP, SelectComplexAHPExceptRRHorn, PSelectComplexAHPExceptRRHorn, SelectNewComplexAHPExceptRRHorn, PSelectNewComplexAHPExceptRRHorn, SelectNewComplexAHPExceptUniqMaxHorn, PSelectNewComplexAHPExceptUniqMaxHorn, SelectNewComplexAHPNS, SelectVGNonCR, SelectCQArEqLast, SelectCQArEqFirst, SelectCQIArEqLast, SelectCQIArEqFirst, SelectCQAr, SelectCQIAr, SelectCQArNpEqFirst, SelectCQIArNpEqFirst, SelectGrCQArEqFirst, SelectCQGrArEqFirst, SelectCQArNTEqFirst, SelectCQIArNTEqFirst, SelectCQArNTNpEqFirst, SelectCQIArNTNpEqFirst, SelectCQArNXTEqFirst, SelectCQIArNXTEqFirst, SelectCQArNTNp, SelectCQIArNTNp, SelectCQArNT, SelectCQIArNT, SelectCQArNp, SelectCQIArNp, SelectCQArNpEqFirstUnlessPDom, SelectCQArNTEqFirstUnlessPDom, SelectCQPrecW, SelectCQIPrecW, SelectCQPrecWNTNp, SelectCQIPrecWNTNp, SelectMaxLComplexAvoidAppVar, SelectMaxLComplexStronglyAvoidAppVar, SelectMaxLComplexPreferAppVar

```python
! eprover-ho --print-saturated --output-level=10 --term-ordering=LPO4 --expert-heuristic=FIFO --literal-selection-strategy="SelectLargestNegLit" --precedence="path>edge"   /tmp/path.p
```

    cnf(ax2, axiom, (path(X1,X2)|~edge(X1,X2)), file('/tmp/path.p', ax2)).
    cnf(ax1, axiom, (path(X1,X2)|~edge(X1,X3)|~path(X3,X2)), file('/tmp/path.p', ax1)).
    cnf(ax1, axiom, (edge(a,b)), file('/tmp/path.p', ax1)).
    cnf(ax2, axiom, (edge(b,c)), file('/tmp/path.p', ax2)).
    cnf(ax3, axiom, (edge(c,d)), file('/tmp/path.p', ax3)).
    cnf(c_0_6, plain, (path(X1,X2)|~edge(X1,X2)),inference(fof_simplification, [status(thm)],[c_0_1])).
    cnf(c_0_7, plain, (path(X1,X2)|~edge(X1,X3)|~path(X3,X2)),inference(fof_simplification, [status(thm)],[c_0_2])).
    # Initializing proof state
    cnf(c_0_8, plain, (edge(a,b)), c_0_-9223372036854775793,['eval']).
    cnf(c_0_9, plain, (edge(b,c)), c_0_-9223372036854775792,['eval']).
    cnf(c_0_10, plain, (edge(c,d)), c_0_-9223372036854775791,['eval']).
    cnf(c_0_11, plain, (path(X1,X2)|~edge(X1,X2)), c_0_-9223372036854775795,['eval']).
    cnf(c_0_12, plain, (path(X1,X2)|~path(X3,X2)|~edge(X1,X3)), c_0_-9223372036854775794,['eval']).
    # Scanning for AC axioms
    cnf(c_0_13, plain, (edge(a,b)), c_0_8,['new_given']).
    cnf(c_0_14, plain, (edge(b,c)), c_0_9,['new_given']).
    cnf(c_0_15, plain, (edge(c,d)), c_0_10,['new_given']).
    cnf(c_0_16, plain, (path(X1,X2)|~edge(X1,X2)), c_0_11,['new_given']).
    cnf(c_0_17, plain, (path(c,d)),inference(pm,[status(thm)],[c_0_16,c_0_15])).
    cnf(c_0_18, plain, (path(b,c)),inference(pm,[status(thm)],[c_0_16,c_0_14])).
    cnf(c_0_19, plain, (path(a,b)),inference(pm,[status(thm)],[c_0_16,c_0_13])).
    cnf(c_0_20, plain, (path(c,d)), c_0_17,['eval']).
    cnf(c_0_21, plain, (path(b,c)), c_0_18,['eval']).
    cnf(c_0_22, plain, (path(a,b)), c_0_19,['eval']).
    cnf(c_0_23, plain, (path(X1,X2)|~edge(X1,X3)|~path(X3,X2)), c_0_12,['new_given']).
    cnf(c_0_24, plain, (path(c,X1)|~path(d,X1)),inference(pm,[status(thm)],[c_0_23,c_0_15])).
    cnf(c_0_25, plain, (path(b,X1)|~path(c,X1)),inference(pm,[status(thm)],[c_0_23,c_0_14])).
    cnf(c_0_26, plain, (path(a,X1)|~path(b,X1)),inference(pm,[status(thm)],[c_0_23,c_0_13])).
    cnf(c_0_27, plain, (path(c,X1)|~path(d,X1)), c_0_24,['eval']).
    cnf(c_0_28, plain, (path(b,X1)|~path(c,X1)), c_0_25,['eval']).
    cnf(c_0_29, plain, (path(a,X1)|~path(b,X1)), c_0_26,['eval']).
    cnf(c_0_30, plain, (path(c,d)), c_0_20,['new_given']).
    cnf(c_0_31, plain, (path(b,c)), c_0_21,['new_given']).
    cnf(c_0_32, plain, (path(a,b)), c_0_22,['new_given']).
    cnf(c_0_33, plain, (path(c,X1)|~path(d,X1)), c_0_27,['new_given']).
    cnf(c_0_34, plain, (path(b,X1)|~path(c,X1)), c_0_28,['new_given']).
    cnf(c_0_35, plain, (path(b,d)),inference(pm,[status(thm)],[c_0_34,c_0_30])).
    cnf(c_0_36, plain, (path(b,d)), c_0_35,['eval']).
    cnf(c_0_37, plain, (path(a,X1)|~path(b,X1)), c_0_29,['new_given']).
    cnf(c_0_38, plain, (path(a,c)),inference(pm,[status(thm)],[c_0_37,c_0_31])).
    cnf(c_0_39, plain, (path(a,c)), c_0_38,['eval']).
    cnf(c_0_40, plain, (path(b,d)), c_0_36,['new_given']).
    cnf(c_0_41, plain, (path(a,d)),inference(pm,[status(thm)],[c_0_37,c_0_40])).
    cnf(c_0_42, plain, (path(a,d)), c_0_41,['eval']).
    cnf(c_0_43, plain, (path(a,c)), c_0_39,['new_given']).
    cnf(c_0_44, plain, (path(a,d)), c_0_42,['new_given']).
    cnf(c_0_45, plain, (edge(a,b)), c_0_13,['final']).
    cnf(c_0_46, plain, (edge(b,c)), c_0_14,['final']).
    cnf(c_0_47, plain, (edge(c,d)), c_0_15,['final']).
    cnf(c_0_48, plain, (path(c,d)), c_0_30,['final']).
    cnf(c_0_49, plain, (path(b,c)), c_0_31,['final']).
    cnf(c_0_50, plain, (path(a,b)), c_0_32,['final']).
    cnf(c_0_51, plain, (path(b,d)), c_0_40,['final']).
    cnf(c_0_52, plain, (path(a,c)), c_0_43,['final']).
    cnf(c_0_53, plain, (path(a,d)), c_0_44,['final']).
    cnf(c_0_54, plain, (path(X1,X2)|~edge(X1,X2)), c_0_16,['final']).
    cnf(c_0_55, plain, (path(X1,X2)|~edge(X1,X3)|~path(X3,X2)), c_0_23,['final']).
    cnf(c_0_56, plain, (path(c,X1)|~path(d,X1)), c_0_33,['final']).
    cnf(c_0_57, plain, (path(b,X1)|~path(c,X1)), c_0_34,['final']).
    cnf(c_0_58, plain, (path(a,X1)|~path(b,X1)), c_0_37,['final']).
    
    # No proof found!
    # SZS status Satisfiable
    # Processed positive unit clauses:
    cnf(c_0_45, plain, (edge(a,b))).
    cnf(c_0_46, plain, (edge(b,c))).
    cnf(c_0_47, plain, (edge(c,d))).
    cnf(c_0_48, plain, (path(c,d))).
    cnf(c_0_49, plain, (path(b,c))).
    cnf(c_0_50, plain, (path(a,b))).
    cnf(c_0_51, plain, (path(b,d))).
    cnf(c_0_52, plain, (path(a,c))).
    cnf(c_0_53, plain, (path(a,d))).
    
    # Processed negative unit clauses:
    
    # Processed non-unit clauses:
    cnf(c_0_54, plain, (path(X1,X2)|~edge(X1,X2))).
    cnf(c_0_55, plain, (path(X1,X2)|~edge(X1,X3)|~path(X3,X2))).
    cnf(c_0_56, plain, (path(c,X1)|~path(d,X1))).
    cnf(c_0_57, plain, (path(b,X1)|~path(c,X1))).
    cnf(c_0_58, plain, (path(a,X1)|~path(b,X1))).
    
    # Unprocessed positive unit clauses:
    
    # Unprocessed negative unit clauses:
    
    # Unprocessed non-unit clauses:
    
    
    # Parsed axioms                        : 5
    # Removed by relevancy pruning/SinE    : 0
    # Initial clauses                      : 5
    # Removed in clause preprocessing      : 0
    # Initial clauses in saturation        : 5
    # Processed clauses                    : 14
    # ...of these trivial                  : 0
    # ...subsumed                          : 0
    # ...remaining for further processing  : 14
    # Other redundant clauses eliminated   : 0
    # Clauses deleted for lack of memory   : 0
    # Backward-subsumed                    : 0
    # Backward-rewritten                   : 0
    # Generated clauses                    : 9
    # ...of the previous two non-redundant : 9
    # ...aggressively subsumed             : 0
    # Contextual simplify-reflections      : 0
    # Paramodulations                      : 9
    # Factorizations                       : 0
    # NegExts                              : 0
    # Equation resolutions                 : 0
    # Disequality decompositions           : 0
    # Total rewrite steps                  : 0
    # ...of those cached                   : 0
    # Propositional unsat checks           : 0
    #    Propositional check models        : 0
    #    Propositional check unsatisfiable : 0
    #    Propositional clauses             : 0
    #    Propositional clauses after purity: 0
    #    Propositional unsat core size     : 0
    #    Propositional preprocessing time  : 0.000
    #    Propositional encoding time       : 0.000
    #    Propositional solver time         : 0.000
    #    Success case prop preproc time    : 0.000
    #    Success case prop encoding time   : 0.000
    #    Success case prop solver time     : 0.000
    # Current number of processed clauses  : 14
    #    Positive orientable unit clauses  : 9
    #    Positive unorientable unit clauses: 0
    #    Negative unit clauses             : 0
    #    Non-unit-clauses                  : 5
    # Current number of unprocessed clauses: 0
    # ...number of literals in the above   : 0
    # Current number of archived formulas  : 0
    # Current number of archived clauses   : 0
    # Clause-clause subsumption calls (NU) : 1
    # Rec. Clause-clause subsumption calls : 1
    # Non-unit clause-clause subsumptions  : 0
    # Unit Clause-clause subsumption calls : 0
    # Rewrite failures with RHS unbound    : 0
    # BW rewrite match attempts            : 0
    # BW rewrite match successes           : 0
    # Condensation attempts                : 0
    # Condensation successes               : 0
    # Termbank termtop insertions          : 138
    # Search garbage collected termcells   : 9

## Knuth Bendix

UEQ
<http://cl-informatik.uibk.ac.at/software/mkbtt/download.php> 101 problems

<https://www.metalevel.at/trs/>

```python
%%file /tmp/grp.p
cnf(ax1, axiom, mul(X,mul(Y,Z)) = mul(mul(X,Y),Z)).
cnf(ax2, axiom, mul(e,X) = X).
cnf(ax3, axiom, mul(inv(X), X) = e).

```

    Overwriting /tmp/grp.p

```python
! eprover-ho --print-saturated --output-level=10 --term-ordering=KBO6 --literal-selection-strategy="SelectLargestNegLit"  /tmp/grp.p
```

## Unification

Raw usage. Equality resolution rule ought to put unifier into `ans` predicate.

`er` is equality resolution. Interesting.
I needed to give it a selection to make it do this

Ah, side condition says u != v has to be eligibile for resolution.

```python
%%file /tmp/unify.p

cnf(ax1, axiom, unifier(a(A),b(B)) | f(g(A)) != f(B)).
%cnf(ax1, axiom, g(A) != B  | f(g(A)) != f(B)).
% cnf(, ocnjecture, ?[A,B] : f(g(A)) = f(B)).  negate. ![A,B]: ~(f(g(A)) = f(B)).

```

    Overwriting /tmp/unify.p

```python
! eprover-ho --print-saturated --output-level=6 --literal-selection-strategy="SelectLargestNegLit" --proof-object /tmp/unify.p
```

    cnf(ax1, axiom, (unifier(a(X1),b(X2))|f(g(X1))!=f(X2)), file('/tmp/unify.p', ax1)).
    cnf(c_0_2, plain, (unifier(a(X1),b(X2))|f(g(X1))!=f(X2)),inference(fof_simplification, [status(thm)],[c_0_1])).
    # Initializing proof state
    cnf(c_0_3, plain, (unifier(a(X1),b(X2))|f(g(X1))!=f(X2)), c_0_-9223372036854775804,['eval']).
    # Scanning for AC axioms
    cnf(c_0_4, plain, (unifier(a(X1),b(X2))|f(g(X1))!=f(X2)), c_0_3,['new_given']).
    cnf(c_0_5, plain, (unifier(a(X1),b(g(X1)))),inference(er,[status(thm)],[c_0_4])).
    cnf(c_0_6, plain, (unifier(a(X1),b(g(X1)))), c_0_5,['eval']).
    cnf(c_0_7, plain, (unifier(a(X1),b(g(X1)))), c_0_6,['new_given']).
    cnf(c_0_8, plain, (unifier(a(X1),b(g(X1)))), c_0_7,['final']).
    cnf(c_0_9, plain, (unifier(a(X1),b(X2))|f(g(X1))!=f(X2)), c_0_4,['final']).
    
    # No proof found!
    # SZS status Satisfiable
    # SZS output start Saturation
    cnf(ax1, axiom, (unifier(a(X1),b(X2))|f(g(X1))!=f(X2)), file('/tmp/unify.p', ax1)).
    cnf(c_0_1, plain, (unifier(a(X1),b(X2))|f(g(X1))!=f(X2)), inference(fof_simplification,[status(thm)],[ax1])).
    cnf(c_0_2, plain, (unifier(a(X1),b(X2))|f(g(X1))!=f(X2)), c_0_1, ['final']).
    cnf(c_0_3, plain, (unifier(a(X1),b(g(X1)))), inference(er,[status(thm)],[c_0_2]), ['final']).
    # SZS output end Saturation
    # Processed positive unit clauses:
    cnf(c_0_3, plain, (unifier(a(X1),b(g(X1))))).
    
    # Processed negative unit clauses:
    
    # Processed non-unit clauses:
    cnf(c_0_9, plain, (unifier(a(X1),b(X2))|f(g(X1))!=f(X2))).
    
    # Unprocessed positive unit clauses:
    
    # Unprocessed negative unit clauses:
    
    # Unprocessed non-unit clauses:
    
    
    # Parsed axioms                        : 1
    # Removed by relevancy pruning/SinE    : 0
    # Initial clauses                      : 1
    # Removed in clause preprocessing      : 0
    # Initial clauses in saturation        : 1
    # Processed clauses                    : 2
    # ...of these trivial                  : 0
    # ...subsumed                          : 0
    # ...remaining for further processing  : 2
    # Other redundant clauses eliminated   : 0
    # Clauses deleted for lack of memory   : 0
    # Backward-subsumed                    : 0
    # Backward-rewritten                   : 0
    # Generated clauses                    : 1
    # ...of the previous two non-redundant : 1
    # ...aggressively subsumed             : 0
    # Contextual simplify-reflections      : 0
    # Paramodulations                      : 0
    # Factorizations                       : 0
    # NegExts                              : 0
    # Equation resolutions                 : 1
    # Disequality decompositions           : 0
    # Total rewrite steps                  : 0
    # ...of those cached                   : 0
    # Propositional unsat checks           : 0
    #    Propositional check models        : 0
    #    Propositional check unsatisfiable : 0
    #    Propositional clauses             : 0
    #    Propositional clauses after purity: 0
    #    Propositional unsat core size     : 0
    #    Propositional preprocessing time  : 0.000
    #    Propositional encoding time       : 0.000
    #    Propositional solver time         : 0.000
    #    Success case prop preproc time    : 0.000
    #    Success case prop encoding time   : 0.000
    #    Success case prop solver time     : 0.000
    # Current number of processed clauses  : 2
    #    Positive orientable unit clauses  : 1
    #    Positive unorientable unit clauses: 0
    #    Negative unit clauses             : 0
    #    Non-unit-clauses                  : 1
    # Current number of unprocessed clauses: 0
    # ...number of literals in the above   : 0
    # Current number of archived formulas  : 0
    # Current number of archived clauses   : 0
    # Clause-clause subsumption calls (NU) : 0
    # Rec. Clause-clause subsumption calls : 0
    # Non-unit clause-clause subsumptions  : 0
    # Unit Clause-clause subsumption calls : 0
    # Rewrite failures with RHS unbound    : 0
    # BW rewrite match attempts            : 0
    # BW rewrite match successes           : 0
    # Condensation attempts                : 0
    # Condensation successes               : 0
    # Termbank termtop insertions          : 53
    # Search garbage collected termcells   : 3

Also E-unification and lambda unification

```python
%%file /tmp/eq.p
cnf(assoc, axiom, mul(X,mul(Y,Z)) = mul(mul(X,Y),Z)).
cnf(com, axiom, mul(Y,X) = mul(X,Y)).
%fof(mul_e, conjecture, ?[X,Y] : mul(mul(a,Y), X) = mul(X,mul(a,X))).
%fof(mul_e, conjecture, ?[X,Y,Z] : mul(mul(Z,Y), X) = mul(X,mul(Z,X))).

```

    Overwriting /tmp/eq.p

```python
!eprover-ho --print-saturated --output-level=6 --literal-selection-strategy="SelectLargestNegLit"  /tmp/eq.p
```

    cnf(assoc, axiom, (mul(X1,mul(X2,X3))=mul(mul(X1,X2),X3)), file('/tmp/eq.p', assoc)).
    cnf(com, axiom, (mul(X1,X2)=mul(X2,X1)), file('/tmp/eq.p', com)).
    # Initializing proof state
    cnf(c_0_3, plain, (mul(X1,X2)=mul(X2,X1)), c_0_-9223372036854775802,['eval']).
    cnf(c_0_4, plain, (mul(mul(X1,X2),X3)=mul(X1,mul(X2,X3))), c_0_-9223372036854775803,['eval']).
    # Scanning for AC axioms
    # mul is AC
    # AC handling enabled
    cnf(c_0_5, plain, (mul(X1,X2)=mul(X2,X1)), c_0_3,['new_given']).
    cnf(c_0_6, plain, (mul(mul(X1,X2),X3)=mul(X1,mul(X2,X3))), c_0_4,['new_given']).
    cnf(c_0_7, plain, (mul(X1,mul(X2,X3))=mul(X3,mul(X1,X2))),inference(pm,[status(thm)],[c_0_5,c_0_6])).
    cnf(c_0_8, plain, (mul(mul(X1,mul(X2,X3)),X4)=mul(mul(X1,X2),mul(X3,X4))),inference(pm,[status(thm)],[c_0_6,c_0_6])).
    cnf(c_0_9, plain, (mul(X2,mul(X3,X1))=mul(X1,mul(X2,X3))),inference(pm,[status(thm)],[c_0_5,c_0_6])).
    cnf(c_0_10, plain, (mul(mul(X2,X1),X3)=mul(X1,mul(X2,X3))),inference(pm,[status(thm)],[c_0_6,c_0_5])).
    cnf(c_0_11, plain, (mul(mul(X2,X1),X3)=mul(X1,mul(X2,X3))),inference(pm,[status(thm)],[c_0_6,c_0_5])).
    cnf(c_0_12, plain, (mul(X1,mul(X2,mul(X3,X4)))=mul(mul(X1,X2),mul(X3,X4))),inference(rw, [status(thm)],[inference(rw, [status(thm)],[c_0_8,c_0_6]),c_0_6])).
    cnf(c_0_13, plain, (mul(X1,mul(X2,mul(X3,X4)))=mul(X1,mul(X2,mul(X3,X4)))),inference(rw, [status(thm)],[c_0_12,c_0_6])).
    cnf(c_0_14, plain, (mul(X2,mul(X1,X3))=mul(X1,mul(X2,X3))),inference(rw, [status(thm)],[c_0_10,c_0_6])).
    cnf(c_0_15, plain, (mul(X2,mul(X1,X3))=mul(X1,mul(X2,X3))),inference(rw, [status(thm)],[c_0_11,c_0_6])).
    cnf(c_0_16, plain, (mul(X1,mul(X2,X3))=mul(X3,mul(X1,X2))), c_0_7,['eval']).
    cnf(c_0_17, plain, (mul(X2,mul(X3,X1))=mul(X1,mul(X2,X3))), c_0_9,['eval']).
    cnf(c_0_18, plain, (mul(X2,mul(X1,X3))=mul(X1,mul(X2,X3))), c_0_14,['eval']).
    cnf(c_0_19, plain, (mul(X2,mul(X1,X3))=mul(X1,mul(X2,X3))), c_0_15,['eval']).
    cnf(c_0_20, plain, (mul(X1,mul(X2,X3))=mul(X3,mul(X1,X2))), c_0_16,['new_given']).
    cnf(c_0_21, plain, (mul(X3,mul(X4,mul(X1,X2)))=mul(X1,mul(X2,mul(X3,X4)))),inference(pm,[status(thm)],[c_0_6,c_0_20])).
    cnf(c_0_22, plain, (mul(X1,mul(X3,mul(X4,X2)))=mul(mul(X3,X4),mul(X1,X2))),inference(pm,[status(thm)],[c_0_20,c_0_20])).
    cnf(c_0_23, plain, (mul(X2,mul(X3,X1))=mul(mul(X2,X3),X1)),inference(pm,[status(thm)],[c_0_5,c_0_20])).
    cnf(c_0_24, plain, (mul(mul(X2,mul(X3,X1)),X4)=mul(X1,mul(mul(X2,X3),X4))),inference(pm,[status(thm)],[c_0_6,c_0_20])).
    cnf(c_0_25, plain, (mul(X4,mul(X2,mul(X3,X1)))=mul(X1,mul(mul(X2,X3),X4))),inference(pm,[status(thm)],[c_0_20,c_0_20])).
    cnf(c_0_26, plain, (mul(X1,mul(X2,X3))=mul(mul(X1,X2),X3)),inference(pm,[status(thm)],[c_0_5,c_0_20])).
    cnf(c_0_27, plain, (mul(X2,mul(X3,X1))=mul(X3,mul(X1,X2))),inference(pm,[status(thm)],[c_0_20,c_0_20])).
    cnf(c_0_28, plain, (mul(X4,mul(mul(X1,X2),X3))=mul(X1,mul(X2,mul(X3,X4)))),inference(pm,[status(thm)],[c_0_6,c_0_20])).
    cnf(c_0_29, plain, (mul(X1,mul(X4,mul(X2,X3)))=mul(mul(X3,X4),mul(X1,X2))),inference(pm,[status(thm)],[c_0_20,c_0_20])).
    cnf(c_0_30, plain, (mul(X3,mul(X1,X2))=mul(mul(X2,X3),X1)),inference(pm,[status(thm)],[c_0_5,c_0_20])).
    cnf(c_0_31, plain, (mul(mul(X3,mul(X1,X2)),X4)=mul(X1,mul(mul(X2,X3),X4))),inference(pm,[status(thm)],[c_0_6,c_0_20])).
    cnf(c_0_32, plain, (mul(X4,mul(X3,mul(X1,X2)))=mul(X1,mul(mul(X2,X3),X4))),inference(pm,[status(thm)],[c_0_20,c_0_20])).
    cnf(c_0_33, plain, (mul(X2,mul(X3,X1))=mul(mul(X1,X2),X3)),inference(pm,[status(thm)],[c_0_5,c_0_20])).
    cnf(c_0_34, plain, (mul(X2,mul(X3,X1))=mul(X1,mul(X2,X3))),inference(pm,[status(thm)],[c_0_20,c_0_20])).
    cnf(c_0_35, plain, (mul(X4,mul(X1,mul(X2,X3)))=mul(mul(X1,X2),mul(X3,X4))),inference(pm,[status(thm)],[c_0_20,c_0_6])).
    cnf(c_0_36, plain, (mul(X3,mul(X2,X1))=mul(X1,mul(X2,X3))),inference(pm,[status(thm)],[c_0_20,c_0_5])).
    cnf(c_0_37, plain, (mul(X3,mul(X2,X1))=mul(X1,mul(X2,X3))),inference(pm,[status(thm)],[c_0_20,c_0_5])).
    cnf(c_0_38, plain, (mul(X1,mul(X2,mul(X3,X4)))=mul(X4,mul(X1,mul(X2,X3)))),inference(pm,[status(thm)],[c_0_20,c_0_6])).
    cnf(c_0_39, plain, (mul(X1,mul(X3,X2))=mul(X3,mul(X1,X2))),inference(pm,[status(thm)],[c_0_20,c_0_5])).
    cnf(c_0_40, plain, (mul(X1,mul(X3,X2))=mul(X3,mul(X1,X2))),inference(pm,[status(thm)],[c_0_20,c_0_5])).
    cnf(c_0_41, plain, (mul(X1,mul(X3,mul(X4,X2)))=mul(X3,mul(X4,mul(X1,X2)))),inference(rw, [status(thm)],[c_0_22,c_0_6])).
    cnf(c_0_42, plain, (mul(X2,mul(X3,X1))=mul(X2,mul(X3,X1))),inference(rw, [status(thm)],[c_0_23,c_0_6])).
    cnf(c_0_43, plain, (mul(X2,mul(X3,mul(X1,X4)))=mul(X1,mul(mul(X2,X3),X4))),inference(rw, [status(thm)],[inference(rw, [status(thm)],[c_0_24,c_0_6]),c_0_6])).
    cnf(c_0_44, plain, (mul(X2,mul(X3,mul(X1,X4)))=mul(X1,mul(X2,mul(X3,X4)))),inference(rw, [status(thm)],[c_0_43,c_0_6])).
    cnf(c_0_45, plain, (mul(X4,mul(X2,mul(X3,X1)))=mul(X1,mul(X2,mul(X3,X4)))),inference(rw, [status(thm)],[c_0_25,c_0_6])).
    cnf(c_0_46, plain, (mul(X1,mul(X2,X3))=mul(X1,mul(X2,X3))),inference(rw, [status(thm)],[c_0_26,c_0_6])).
    cnf(c_0_47, plain, (mul(X4,mul(X1,mul(X2,X3)))=mul(X1,mul(X2,mul(X3,X4)))),inference(rw, [status(thm)],[c_0_28,c_0_6])).
    cnf(c_0_48, plain, (mul(X1,mul(X4,mul(X2,X3)))=mul(X3,mul(X4,mul(X1,X2)))),inference(rw, [status(thm)],[c_0_29,c_0_6])).
    cnf(c_0_49, plain, (mul(X3,mul(X1,X2))=mul(X2,mul(X3,X1))),inference(rw, [status(thm)],[c_0_30,c_0_6])).
    cnf(c_0_50, plain, (mul(X3,mul(X1,mul(X2,X4)))=mul(X1,mul(mul(X2,X3),X4))),inference(rw, [status(thm)],[inference(rw, [status(thm)],[c_0_31,c_0_6]),c_0_6])).
    cnf(c_0_51, plain, (mul(X3,mul(X1,mul(X2,X4)))=mul(X1,mul(X2,mul(X3,X4)))),inference(rw, [status(thm)],[c_0_50,c_0_6])).
    cnf(c_0_52, plain, (mul(X4,mul(X3,mul(X1,X2)))=mul(X1,mul(X2,mul(X3,X4)))),inference(rw, [status(thm)],[c_0_32,c_0_6])).
    cnf(c_0_53, plain, (mul(X2,mul(X3,X1))=mul(X1,mul(X2,X3))),inference(rw, [status(thm)],[c_0_33,c_0_6])).
    cnf(c_0_54, plain, (mul(X4,mul(X1,mul(X2,X3)))=mul(X1,mul(X2,mul(X3,X4)))),inference(rw, [status(thm)],[c_0_35,c_0_6])).
    cnf(c_0_55, plain, (mul(X3,mul(X4,mul(X1,X2)))=mul(X1,mul(X2,mul(X3,X4)))), c_0_21,['eval']).
    cnf(c_0_56, plain, (mul(X1,mul(X3,mul(X4,X2)))=mul(X3,mul(X4,mul(X1,X2)))), c_0_41,['eval']).
    cnf(c_0_57, plain, (mul(X2,mul(X3,mul(X1,X4)))=mul(X1,mul(X2,mul(X3,X4)))), c_0_44,['eval']).
    cnf(c_0_58, plain, (mul(X4,mul(X2,mul(X3,X1)))=mul(X1,mul(X2,mul(X3,X4)))), c_0_45,['eval']).
    cnf(c_0_59, plain, (mul(X2,mul(X3,X1))=mul(X3,mul(X1,X2))), c_0_27,['eval']).
    cnf(c_0_60, plain, (mul(X4,mul(X1,mul(X2,X3)))=mul(X1,mul(X2,mul(X3,X4)))), c_0_47,['eval']).
    cnf(c_0_61, plain, (mul(X1,mul(X4,mul(X2,X3)))=mul(X3,mul(X4,mul(X1,X2)))), c_0_48,['eval']).
    cnf(c_0_62, plain, (mul(X3,mul(X1,X2))=mul(X2,mul(X3,X1))), c_0_49,['eval']).
    cnf(c_0_63, plain, (mul(X3,mul(X1,mul(X2,X4)))=mul(X1,mul(X2,mul(X3,X4)))), c_0_51,['eval']).
    cnf(c_0_64, plain, (mul(X4,mul(X3,mul(X1,X2)))=mul(X1,mul(X2,mul(X3,X4)))), c_0_52,['eval']).
    cnf(c_0_65, plain, (mul(X2,mul(X3,X1))=mul(X1,mul(X2,X3))), c_0_53,['eval']).
    cnf(c_0_66, plain, (mul(X2,mul(X3,X1))=mul(X1,mul(X2,X3))), c_0_34,['eval']).
    cnf(c_0_67, plain, (mul(X4,mul(X1,mul(X2,X3)))=mul(X1,mul(X2,mul(X3,X4)))), c_0_54,['eval']).
    cnf(c_0_68, plain, (mul(X3,mul(X2,X1))=mul(X1,mul(X2,X3))), c_0_36,['eval']).
    cnf(c_0_69, plain, (mul(X3,mul(X2,X1))=mul(X1,mul(X2,X3))), c_0_37,['eval']).
    cnf(c_0_70, plain, (mul(X1,mul(X2,mul(X3,X4)))=mul(X4,mul(X1,mul(X2,X3)))), c_0_38,['eval']).
    cnf(c_0_71, plain, (mul(X1,mul(X3,X2))=mul(X3,mul(X1,X2))), c_0_39,['eval']).
    cnf(c_0_72, plain, (mul(X1,mul(X3,X2))=mul(X3,mul(X1,X2))), c_0_40,['eval']).
    cnf(c_0_73, plain, (mul(X2,mul(X3,X1))=mul(X1,mul(X2,X3))), c_0_17,['subsumed(c_0_20)']).
    cnf(c_0_74, plain, (mul(X2,mul(X1,X3))=mul(X1,mul(X2,X3))), c_0_18,['new_given']).
    cnf(c_0_75, plain, (mul(X3,mul(mul(X1,X2),X4))=mul(X1,mul(X2,mul(X3,X4)))),inference(pm,[status(thm)],[c_0_6,c_0_74])).
    cnf(c_0_76, plain, (mul(X1,mul(X3,mul(X2,X4)))=mul(mul(X3,X4),mul(X1,X2))),inference(pm,[status(thm)],[c_0_20,c_0_74])).
    cnf(c_0_77, plain, (mul(X1,mul(X3,mul(X2,X4)))=mul(X2,mul(X1,mul(X3,X4)))),inference(pm,[status(thm)],[c_0_74,c_0_74])).
    cnf(c_0_78, plain, (mul(X2,mul(X1,X3))=mul(mul(X2,X3),X1)),inference(pm,[status(thm)],[c_0_5,c_0_74])).
    cnf(c_0_79, plain, (mul(mul(X2,mul(X1,X3)),X4)=mul(X1,mul(mul(X2,X3),X4))),inference(pm,[status(thm)],[c_0_6,c_0_74])).
    cnf(c_0_80, plain, (mul(X4,mul(X2,mul(X1,X3)))=mul(X1,mul(mul(X2,X3),X4))),inference(pm,[status(thm)],[c_0_20,c_0_74])).
    cnf(c_0_81, plain, (mul(X1,mul(X3,X2))=mul(mul(X1,X2),X3)),inference(pm,[status(thm)],[c_0_5,c_0_74])).
    cnf(c_0_82, plain, (mul(X2,mul(X3,mul(X1,X4)))=mul(X1,mul(X2,mul(X3,X4)))),inference(pm,[status(thm)],[c_0_74,c_0_74])).
    cnf(c_0_83, plain, (mul(X2,mul(X1,X3))=mul(X3,mul(X1,X2))),inference(pm,[status(thm)],[c_0_20,c_0_74])).
    cnf(c_0_84, plain, (mul(X1,mul(X3,X2))=mul(X1,mul(X2,X3))),inference(pm,[status(thm)],[c_0_20,c_0_74])).
    cnf(c_0_85, plain, (mul(X3,mul(mul(X1,X2),X4))=mul(X1,mul(X2,mul(X3,X4)))),inference(pm,[status(thm)],[c_0_6,c_0_74])).
    cnf(c_0_86, plain, (mul(X1,mul(X3,mul(X2,X4)))=mul(mul(X3,X4),mul(X1,X2))),inference(pm,[status(thm)],[c_0_20,c_0_74])).
    cnf(c_0_87, plain, (mul(X1,mul(X3,mul(X2,X4)))=mul(X2,mul(X1,mul(X3,X4)))),inference(pm,[status(thm)],[c_0_74,c_0_74])).
    cnf(c_0_88, plain, (mul(X2,mul(X1,X3))=mul(mul(X2,X3),X1)),inference(pm,[status(thm)],[c_0_5,c_0_74])).
    cnf(c_0_89, plain, (mul(mul(X2,mul(X1,X3)),X4)=mul(X1,mul(mul(X2,X3),X4))),inference(pm,[status(thm)],[c_0_6,c_0_74])).
    cnf(c_0_90, plain, (mul(X4,mul(X2,mul(X1,X3)))=mul(X1,mul(mul(X2,X3),X4))),inference(pm,[status(thm)],[c_0_20,c_0_74])).
    cnf(c_0_91, plain, (mul(X1,mul(X3,X2))=mul(mul(X1,X2),X3)),inference(pm,[status(thm)],[c_0_5,c_0_74])).
    cnf(c_0_92, plain, (mul(X2,mul(X3,mul(X1,X4)))=mul(X1,mul(X2,mul(X3,X4)))),inference(pm,[status(thm)],[c_0_74,c_0_74])).
    cnf(c_0_93, plain, (mul(X2,mul(X1,X3))=mul(X3,mul(X1,X2))),inference(pm,[status(thm)],[c_0_20,c_0_74])).
    cnf(c_0_94, plain, (mul(X1,mul(X3,X2))=mul(X1,mul(X2,X3))),inference(pm,[status(thm)],[c_0_20,c_0_74])).
    cnf(c_0_95, plain, (mul(X3,mul(X1,mul(X2,X4)))=mul(mul(X1,X2),mul(X3,X4))),inference(pm,[status(thm)],[c_0_74,c_0_6])).
    cnf(c_0_96, plain, (mul(X2,mul(X4,mul(X1,X3)))=mul(X1,mul(X2,mul(X3,X4)))),inference(pm,[status(thm)],[c_0_74,c_0_20])).
    cnf(c_0_97, plain, (mul(X2,mul(X3,mul(X4,X1)))=mul(X1,mul(X2,mul(X3,X4)))),inference(pm,[status(thm)],[c_0_74,c_0_20])).
    cnf(c_0_98, plain, (mul(X2,mul(X3,X1))=mul(X1,mul(X2,X3))),inference(pm,[status(thm)],[c_0_74,c_0_5])).
    cnf(c_0_99, plain, (mul(X2,mul(X3,X1))=mul(X1,mul(X2,X3))),inference(pm,[status(thm)],[c_0_74,c_0_5])).
    cnf(c_0_100, plain, (mul(X1,mul(X2,mul(X3,X4)))=mul(mul(X2,X3),mul(X1,X4))),inference(pm,[status(thm)],[c_0_74,c_0_6])).
    cnf(c_0_101, plain, (mul(X1,mul(X4,mul(X2,X3)))=mul(X2,mul(X1,mul(X3,X4)))),inference(pm,[status(thm)],[c_0_74,c_0_20])).
    cnf(c_0_102, plain, (mul(X1,mul(X3,mul(X4,X2)))=mul(X2,mul(X1,mul(X3,X4)))),inference(pm,[status(thm)],[c_0_74,c_0_20])).
    cnf(c_0_103, plain, (mul(X1,mul(X3,X2))=mul(X2,mul(X1,X3))),inference(pm,[status(thm)],[c_0_74,c_0_5])).
    cnf(c_0_104, plain, (mul(X1,mul(X3,X2))=mul(X2,mul(X1,X3))),inference(pm,[status(thm)],[c_0_74,c_0_5])).
    cnf(c_0_105, plain, (mul(X3,mul(X1,mul(X2,X4)))=mul(X1,mul(X2,mul(X3,X4)))),inference(rw, [status(thm)],[c_0_75,c_0_6])).
    cnf(c_0_106, plain, (mul(X1,mul(X3,mul(X2,X4)))=mul(X3,mul(X4,mul(X1,X2)))),inference(rw, [status(thm)],[c_0_76,c_0_6])).
    cnf(c_0_107, plain, (mul(X2,mul(X1,X3))=mul(X2,mul(X3,X1))),inference(rw, [status(thm)],[c_0_78,c_0_6])).
    cnf(c_0_108, plain, (mul(X2,mul(X1,mul(X3,X4)))=mul(X1,mul(mul(X2,X3),X4))),inference(rw, [status(thm)],[inference(rw, [status(thm)],[c_0_79,c_0_6]),c_0_6])).
    cnf(c_0_109, plain, (mul(X2,mul(X1,mul(X3,X4)))=mul(X1,mul(X2,mul(X3,X4)))),inference(rw, [status(thm)],[c_0_108,c_0_6])).
    cnf(c_0_110, plain, (mul(X4,mul(X2,mul(X1,X3)))=mul(X1,mul(X2,mul(X3,X4)))),inference(rw, [status(thm)],[c_0_80,c_0_6])).
    cnf(c_0_111, plain, (mul(X1,mul(X3,X2))=mul(X1,mul(X2,X3))),inference(rw, [status(thm)],[c_0_81,c_0_6])).
    cnf(c_0_112, plain, (mul(X3,mul(X1,mul(X2,X4)))=mul(X1,mul(X2,mul(X3,X4)))),inference(rw, [status(thm)],[c_0_85,c_0_6])).
    cnf(c_0_113, plain, (mul(X1,mul(X3,mul(X2,X4)))=mul(X3,mul(X4,mul(X1,X2)))),inference(rw, [status(thm)],[c_0_86,c_0_6])).
    cnf(c_0_114, plain, (mul(X2,mul(X1,X3))=mul(X2,mul(X3,X1))),inference(rw, [status(thm)],[c_0_88,c_0_6])).
    cnf(c_0_115, plain, (mul(X2,mul(X1,mul(X3,X4)))=mul(X1,mul(mul(X2,X3),X4))),inference(rw, [status(thm)],[inference(rw, [status(thm)],[c_0_89,c_0_6]),c_0_6])).
    cnf(c_0_116, plain, (mul(X2,mul(X1,mul(X3,X4)))=mul(X1,mul(X2,mul(X3,X4)))),inference(rw, [status(thm)],[c_0_115,c_0_6])).
    cnf(c_0_117, plain, (mul(X4,mul(X2,mul(X1,X3)))=mul(X1,mul(X2,mul(X3,X4)))),inference(rw, [status(thm)],[c_0_90,c_0_6])).
    cnf(c_0_118, plain, (mul(X1,mul(X3,X2))=mul(X1,mul(X2,X3))),inference(rw, [status(thm)],[c_0_91,c_0_6])).
    cnf(c_0_119, plain, (mul(X3,mul(X1,mul(X2,X4)))=mul(X1,mul(X2,mul(X3,X4)))),inference(rw, [status(thm)],[c_0_95,c_0_6])).
    cnf(c_0_120, plain, (mul(X1,mul(X2,mul(X3,X4)))=mul(X2,mul(X3,mul(X1,X4)))),inference(rw, [status(thm)],[c_0_100,c_0_6])).
    cnf(c_0_121, plain, (mul(X3,mul(X1,mul(X2,X4)))=mul(X1,mul(X2,mul(X3,X4)))), c_0_105,['eval']).
    cnf(c_0_122, plain, (mul(X1,mul(X3,mul(X2,X4)))=mul(X3,mul(X4,mul(X1,X2)))), c_0_106,['eval']).
    cnf(c_0_123, plain, (mul(X1,mul(X3,mul(X2,X4)))=mul(X2,mul(X1,mul(X3,X4)))), c_0_77,['eval']).
    cnf(c_0_124, plain, (mul(X2,mul(X1,X3))=mul(X2,mul(X3,X1))), c_0_107,['eval']).
    cnf(c_0_125, plain, (mul(X2,mul(X1,mul(X3,X4)))=mul(X1,mul(X2,mul(X3,X4)))), c_0_109,['eval']).
    cnf(c_0_126, plain, (mul(X4,mul(X2,mul(X1,X3)))=mul(X1,mul(X2,mul(X3,X4)))), c_0_110,['eval']).
    cnf(c_0_127, plain, (mul(X1,mul(X3,X2))=mul(X1,mul(X2,X3))), c_0_111,['eval']).
    cnf(c_0_128, plain, (mul(X2,mul(X3,mul(X1,X4)))=mul(X1,mul(X2,mul(X3,X4)))), c_0_82,['eval']).
    cnf(c_0_129, plain, (mul(X2,mul(X1,X3))=mul(X3,mul(X1,X2))), c_0_83,['eval']).
    cnf(c_0_130, plain, (mul(X1,mul(X3,X2))=mul(X1,mul(X2,X3))), c_0_84,['eval']).
    cnf(c_0_131, plain, (mul(X3,mul(X1,mul(X2,X4)))=mul(X1,mul(X2,mul(X3,X4)))), c_0_112,['eval']).
    cnf(c_0_132, plain, (mul(X1,mul(X3,mul(X2,X4)))=mul(X3,mul(X4,mul(X1,X2)))), c_0_113,['eval']).
    cnf(c_0_133, plain, (mul(X1,mul(X3,mul(X2,X4)))=mul(X2,mul(X1,mul(X3,X4)))), c_0_87,['eval']).
    cnf(c_0_134, plain, (mul(X2,mul(X1,X3))=mul(X2,mul(X3,X1))), c_0_114,['eval']).
    cnf(c_0_135, plain, (mul(X2,mul(X1,mul(X3,X4)))=mul(X1,mul(X2,mul(X3,X4)))), c_0_116,['eval']).
    cnf(c_0_136, plain, (mul(X4,mul(X2,mul(X1,X3)))=mul(X1,mul(X2,mul(X3,X4)))), c_0_117,['eval']).
    cnf(c_0_137, plain, (mul(X1,mul(X3,X2))=mul(X1,mul(X2,X3))), c_0_118,['eval']).
    cnf(c_0_138, plain, (mul(X2,mul(X3,mul(X1,X4)))=mul(X1,mul(X2,mul(X3,X4)))), c_0_92,['eval']).
    cnf(c_0_139, plain, (mul(X2,mul(X1,X3))=mul(X3,mul(X1,X2))), c_0_93,['eval']).
    cnf(c_0_140, plain, (mul(X1,mul(X3,X2))=mul(X1,mul(X2,X3))), c_0_94,['eval']).
    cnf(c_0_141, plain, (mul(X3,mul(X1,mul(X2,X4)))=mul(X1,mul(X2,mul(X3,X4)))), c_0_119,['eval']).
    cnf(c_0_142, plain, (mul(X2,mul(X4,mul(X1,X3)))=mul(X1,mul(X2,mul(X3,X4)))), c_0_96,['eval']).
    cnf(c_0_143, plain, (mul(X2,mul(X3,mul(X4,X1)))=mul(X1,mul(X2,mul(X3,X4)))), c_0_97,['eval']).
    cnf(c_0_144, plain, (mul(X2,mul(X3,X1))=mul(X1,mul(X2,X3))), c_0_98,['eval']).
    cnf(c_0_145, plain, (mul(X2,mul(X3,X1))=mul(X1,mul(X2,X3))), c_0_99,['eval']).
    cnf(c_0_146, plain, (mul(X1,mul(X2,mul(X3,X4)))=mul(X2,mul(X3,mul(X1,X4)))), c_0_120,['eval']).
    cnf(c_0_147, plain, (mul(X1,mul(X4,mul(X2,X3)))=mul(X2,mul(X1,mul(X3,X4)))), c_0_101,['eval']).
    cnf(c_0_148, plain, (mul(X1,mul(X3,mul(X4,X2)))=mul(X2,mul(X1,mul(X3,X4)))), c_0_102,['eval']).
    cnf(c_0_149, plain, (mul(X1,mul(X3,X2))=mul(X2,mul(X1,X3))), c_0_103,['eval']).
    cnf(c_0_150, plain, (mul(X1,mul(X3,X2))=mul(X2,mul(X1,X3))), c_0_104,['eval']).
    cnf(c_0_151, plain, (mul(X2,mul(X1,X3))=mul(X1,mul(X2,X3))), c_0_19,['subsumed(c_0_74)']).
    cnf(c_0_152, plain, (mul(X2,mul(X3,X1))=mul(X3,mul(X1,X2))), c_0_59,['subsumed(c_0_20)']).
    cnf(c_0_153, plain, (mul(X3,mul(X1,X2))=mul(X2,mul(X3,X1))), c_0_62,['subsumed(c_0_20)']).
    cnf(c_0_154, plain, (mul(X2,mul(X3,X1))=mul(X1,mul(X2,X3))), c_0_65,['subsumed(c_0_20)']).
    cnf(c_0_155, plain, (mul(X2,mul(X3,X1))=mul(X1,mul(X2,X3))), c_0_66,['subsumed(c_0_20)']).
    cnf(c_0_156, plain, (mul(X3,mul(X2,X1))=mul(X1,mul(X2,X3))), c_0_68,['new_given']).
    cnf(c_0_157, plain, (mul(X4,mul(X3,mul(X1,X2)))=mul(X1,mul(X2,mul(X3,X4)))),inference(pm,[status(thm)],[c_0_6,c_0_156])).
    cnf(c_0_158, plain, (mul(X1,mul(X4,mul(X3,X2)))=mul(mul(X3,X4),mul(X1,X2))),inference(pm,[status(thm)],[c_0_20,c_0_156])).
    cnf(c_0_159, plain, (mul(X1,mul(X4,mul(X3,X2)))=mul(X2,mul(X1,mul(X3,X4)))),inference(pm,[status(thm)],[c_0_74,c_0_156])).
    cnf(c_0_160, plain, (mul(X1,mul(X4,mul(X3,X2)))=mul(mul(X3,X4),mul(X2,X1))),inference(pm,[status(thm)],[c_0_156,c_0_156])).
    cnf(c_0_161, plain, (mul(X3,mul(X2,X1))=mul(mul(X2,X3),X1)),inference(pm,[status(thm)],[c_0_5,c_0_156])).
    cnf(c_0_162, plain, (mul(mul(X3,mul(X2,X1)),X4)=mul(X1,mul(mul(X2,X3),X4))),inference(pm,[status(thm)],[c_0_6,c_0_156])).
    cnf(c_0_163, plain, (mul(X4,mul(X3,mul(X2,X1)))=mul(X1,mul(mul(X2,X3),X4))),inference(pm,[status(thm)],[c_0_20,c_0_156])).
    cnf(c_0_164, plain, (mul(X2,mul(X1,X3))=mul(mul(X1,X2),X3)),inference(pm,[status(thm)],[c_0_5,c_0_156])).
    cnf(c_0_165, plain, (mul(X4,mul(X2,mul(X1,X3)))=mul(mul(X1,X2),mul(X3,X4))),inference(pm,[status(thm)],[c_0_156,c_0_156])).
    cnf(c_0_166, plain, (mul(X2,mul(X4,mul(X3,X1)))=mul(X1,mul(X2,mul(X3,X4)))),inference(pm,[status(thm)],[c_0_74,c_0_156])).
    cnf(c_0_167, plain, (mul(X3,mul(X2,X1))=mul(X3,mul(X1,X2))),inference(pm,[status(thm)],[c_0_20,c_0_156])).
    cnf(c_0_168, plain, (mul(X3,mul(X2,X1))=mul(X2,mul(X1,X3))),inference(pm,[status(thm)],[c_0_74,c_0_156])).
    cnf(c_0_169, plain, (mul(X2,mul(X1,X3))=mul(X1,mul(X2,X3))),inference(pm,[status(thm)],[c_0_20,c_0_156])).
    cnf(c_0_170, plain, (mul(X3,mul(X1,X2))=mul(X1,mul(X2,X3))),inference(pm,[status(thm)],[c_0_74,c_0_156])).
    cnf(c_0_171, plain, (mul(X4,mul(X3,mul(X1,X2)))=mul(X1,mul(X2,mul(X3,X4)))),inference(pm,[status(thm)],[c_0_6,c_0_156])).
    cnf(c_0_172, plain, (mul(X1,mul(X4,mul(X3,X2)))=mul(mul(X3,X4),mul(X1,X2))),inference(pm,[status(thm)],[c_0_20,c_0_156])).
    cnf(c_0_173, plain, (mul(X1,mul(X4,mul(X3,X2)))=mul(X2,mul(X1,mul(X3,X4)))),inference(pm,[status(thm)],[c_0_74,c_0_156])).
    cnf(c_0_174, plain, (mul(X1,mul(X4,mul(X3,X2)))=mul(mul(X3,X4),mul(X2,X1))),inference(pm,[status(thm)],[c_0_156,c_0_156])).
    cnf(c_0_175, plain, (mul(X3,mul(X2,X1))=mul(mul(X2,X3),X1)),inference(pm,[status(thm)],[c_0_5,c_0_156])).
    cnf(c_0_176, plain, (mul(mul(X3,mul(X2,X1)),X4)=mul(X1,mul(mul(X2,X3),X4))),inference(pm,[status(thm)],[c_0_6,c_0_156])).
    cnf(c_0_177, plain, (mul(X4,mul(X3,mul(X2,X1)))=mul(X1,mul(mul(X2,X3),X4))),inference(pm,[status(thm)],[c_0_20,c_0_156])).
    cnf(c_0_178, plain, (mul(X2,mul(X1,X3))=mul(mul(X1,X2),X3)),inference(pm,[status(thm)],[c_0_5,c_0_156])).
    cnf(c_0_179, plain, (mul(X4,mul(X2,mul(X1,X3)))=mul(mul(X1,X2),mul(X3,X4))),inference(pm,[status(thm)],[c_0_156,c_0_156])).
    cnf(c_0_180, plain, (mul(X2,mul(X4,mul(X3,X1)))=mul(X1,mul(X2,mul(X3,X4)))),inference(pm,[status(thm)],[c_0_74,c_0_156])).
    cnf(c_0_181, plain, (mul(X3,mul(X2,X1))=mul(X3,mul(X1,X2))),inference(pm,[status(thm)],[c_0_20,c_0_156])).
    cnf(c_0_182, plain, (mul(X3,mul(X2,X1))=mul(X2,mul(X1,X3))),inference(pm,[status(thm)],[c_0_74,c_0_156])).
    cnf(c_0_183, plain, (mul(X2,mul(X1,X3))=mul(X1,mul(X2,X3))),inference(pm,[status(thm)],[c_0_20,c_0_156])).
    cnf(c_0_184, plain, (mul(X3,mul(X1,X2))=mul(X1,mul(X2,X3))),inference(pm,[status(thm)],[c_0_74,c_0_156])).
    cnf(c_0_185, plain, (mul(X4,mul(X2,mul(X3,X1)))=mul(X1,mul(mul(X2,X3),X4))),inference(pm,[status(thm)],[c_0_156,c_0_6])).
    cnf(c_0_186, plain, (mul(X4,mul(X2,mul(X3,X1)))=mul(mul(X1,X2),mul(X3,X4))),inference(pm,[status(thm)],[c_0_156,c_0_20])).
    cnf(c_0_187, plain, (mul(X4,mul(X1,mul(X3,X2)))=mul(mul(X1,X2),mul(X3,X4))),inference(pm,[status(thm)],[c_0_156,c_0_74])).
    cnf(c_0_188, plain, (mul(X4,mul(X1,mul(X2,X3)))=mul(mul(X1,X2),mul(X3,X4))),inference(pm,[status(thm)],[c_0_156,c_0_20])).
    cnf(c_0_189, plain, (mul(X4,mul(X1,mul(X3,X2)))=mul(mul(X1,X2),mul(X3,X4))),inference(pm,[status(thm)],[c_0_156,c_0_74])).
    cnf(c_0_190, plain, (mul(X3,mul(X1,X2))=mul(X1,mul(X2,X3))),inference(pm,[status(thm)],[c_0_156,c_0_5])).
    cnf(c_0_191, plain, (mul(X3,mul(X1,X2))=mul(X1,mul(X2,X3))),inference(pm,[status(thm)],[c_0_156,c_0_5])).
    cnf(c_0_192, plain, (mul(X1,mul(X2,mul(X3,X4)))=mul(X4,mul(mul(X2,X3),X1))),inference(pm,[status(thm)],[c_0_156,c_0_6])).
    cnf(c_0_193, plain, (mul(X1,mul(X4,mul(X2,X3)))=mul(mul(X3,X4),mul(X2,X1))),inference(pm,[status(thm)],[c_0_156,c_0_20])).
    cnf(c_0_194, plain, (mul(X1,mul(X3,mul(X2,X4)))=mul(mul(X3,X4),mul(X2,X1))),inference(pm,[status(thm)],[c_0_156,c_0_74])).
    cnf(c_0_195, plain, (mul(X1,mul(X3,mul(X4,X2)))=mul(mul(X3,X4),mul(X2,X1))),inference(pm,[status(thm)],[c_0_156,c_0_20])).
    cnf(c_0_196, plain, (mul(X1,mul(X3,mul(X2,X4)))=mul(mul(X3,X4),mul(X2,X1))),inference(pm,[status(thm)],[c_0_156,c_0_74])).
    cnf(c_0_197, plain, (mul(X1,mul(X3,X2))=mul(X3,mul(X2,X1))),inference(pm,[status(thm)],[c_0_156,c_0_5])).
    cnf(c_0_198, plain, (mul(X1,mul(X3,X2))=mul(X3,mul(X2,X1))),inference(pm,[status(thm)],[c_0_156,c_0_5])).
    cnf(c_0_199, plain, (mul(X1,mul(X4,mul(X3,X2)))=mul(X3,mul(X4,mul(X1,X2)))),inference(rw, [status(thm)],[c_0_158,c_0_6])).
    cnf(c_0_200, plain, (mul(X1,mul(X4,mul(X3,X2)))=mul(X3,mul(X4,mul(X2,X1)))),inference(rw, [status(thm)],[c_0_160,c_0_6])).
    cnf(c_0_201, plain, (mul(X3,mul(X2,X1))=mul(X2,mul(X3,X1))),inference(rw, [status(thm)],[c_0_161,c_0_6])).
    cnf(c_0_202, plain, (mul(X3,mul(X2,mul(X1,X4)))=mul(X1,mul(mul(X2,X3),X4))),inference(rw, [status(thm)],[inference(rw, [status(thm)],[c_0_162,c_0_6]),c_0_6])).
    cnf(c_0_203, plain, (mul(X3,mul(X2,mul(X1,X4)))=mul(X1,mul(X2,mul(X3,X4)))),inference(rw, [status(thm)],[c_0_202,c_0_6])).
    cnf(c_0_204, plain, (mul(X4,mul(X3,mul(X2,X1)))=mul(X1,mul(X2,mul(X3,X4)))),inference(rw, [status(thm)],[c_0_163,c_0_6])).
    cnf(c_0_205, plain, (mul(X2,mul(X1,X3))=mul(X1,mul(X2,X3))),inference(rw, [status(thm)],[c_0_164,c_0_6])).
    cnf(c_0_206, plain, (mul(X4,mul(X2,mul(X1,X3)))=mul(X1,mul(X2,mul(X3,X4)))),inference(rw, [status(thm)],[c_0_165,c_0_6])).
    cnf(c_0_207, plain, (mul(X1,mul(X4,mul(X3,X2)))=mul(X3,mul(X4,mul(X1,X2)))),inference(rw, [status(thm)],[c_0_172,c_0_6])).
    cnf(c_0_208, plain, (mul(X1,mul(X4,mul(X3,X2)))=mul(X3,mul(X4,mul(X2,X1)))),inference(rw, [status(thm)],[c_0_174,c_0_6])).
    cnf(c_0_209, plain, (mul(X3,mul(X2,X1))=mul(X2,mul(X3,X1))),inference(rw, [status(thm)],[c_0_175,c_0_6])).
    cnf(c_0_210, plain, (mul(X3,mul(X2,mul(X1,X4)))=mul(X1,mul(mul(X2,X3),X4))),inference(rw, [status(thm)],[inference(rw, [status(thm)],[c_0_176,c_0_6]),c_0_6])).
    cnf(c_0_211, plain, (mul(X3,mul(X2,mul(X1,X4)))=mul(X1,mul(X2,mul(X3,X4)))),inference(rw, [status(thm)],[c_0_210,c_0_6])).
    cnf(c_0_212, plain, (mul(X4,mul(X3,mul(X2,X1)))=mul(X1,mul(X2,mul(X3,X4)))),inference(rw, [status(thm)],[c_0_177,c_0_6])).
    cnf(c_0_213, plain, (mul(X2,mul(X1,X3))=mul(X1,mul(X2,X3))),inference(rw, [status(thm)],[c_0_178,c_0_6])).
    cnf(c_0_214, plain, (mul(X4,mul(X2,mul(X1,X3)))=mul(X1,mul(X2,mul(X3,X4)))),inference(rw, [status(thm)],[c_0_179,c_0_6])).
    cnf(c_0_215, plain, (mul(X4,mul(X2,mul(X3,X1)))=mul(X1,mul(X2,mul(X3,X4)))),inference(rw, [status(thm)],[c_0_185,c_0_6])).
    cnf(c_0_216, plain, (mul(X4,mul(X2,mul(X3,X1)))=mul(X1,mul(X2,mul(X3,X4)))),inference(rw, [status(thm)],[c_0_186,c_0_6])).
    cnf(c_0_217, plain, (mul(X4,mul(X1,mul(X3,X2)))=mul(X1,mul(X2,mul(X3,X4)))),inference(rw, [status(thm)],[c_0_187,c_0_6])).
    cnf(c_0_218, plain, (mul(X4,mul(X1,mul(X2,X3)))=mul(X1,mul(X2,mul(X3,X4)))),inference(rw, [status(thm)],[c_0_188,c_0_6])).
    cnf(c_0_219, plain, (mul(X4,mul(X1,mul(X3,X2)))=mul(X1,mul(X2,mul(X3,X4)))),inference(rw, [status(thm)],[c_0_189,c_0_6])).
    cnf(c_0_220, plain, (mul(X1,mul(X2,mul(X3,X4)))=mul(X4,mul(X2,mul(X3,X1)))),inference(rw, [status(thm)],[c_0_192,c_0_6])).
    cnf(c_0_221, plain, (mul(X1,mul(X4,mul(X2,X3)))=mul(X3,mul(X4,mul(X2,X1)))),inference(rw, [status(thm)],[c_0_193,c_0_6])).
    cnf(c_0_222, plain, (mul(X1,mul(X3,mul(X2,X4)))=mul(X3,mul(X4,mul(X2,X1)))),inference(rw, [status(thm)],[c_0_194,c_0_6])).
    cnf(c_0_223, plain, (mul(X1,mul(X3,mul(X4,X2)))=mul(X3,mul(X4,mul(X2,X1)))),inference(rw, [status(thm)],[c_0_195,c_0_6])).
    cnf(c_0_224, plain, (mul(X1,mul(X3,mul(X2,X4)))=mul(X3,mul(X4,mul(X2,X1)))),inference(rw, [status(thm)],[c_0_196,c_0_6])).
    cnf(c_0_225, plain, (mul(X4,mul(X3,mul(X1,X2)))=mul(X1,mul(X2,mul(X3,X4)))), c_0_157,['eval']).
    cnf(c_0_226, plain, (mul(X1,mul(X4,mul(X3,X2)))=mul(X3,mul(X4,mul(X1,X2)))), c_0_199,['eval']).
    cnf(c_0_227, plain, (mul(X1,mul(X4,mul(X3,X2)))=mul(X2,mul(X1,mul(X3,X4)))), c_0_159,['eval']).
    cnf(c_0_228, plain, (mul(X1,mul(X4,mul(X3,X2)))=mul(X3,mul(X4,mul(X2,X1)))), c_0_200,['eval']).
    cnf(c_0_229, plain, (mul(X3,mul(X2,X1))=mul(X2,mul(X3,X1))), c_0_201,['eval']).
    cnf(c_0_230, plain, (mul(X3,mul(X2,mul(X1,X4)))=mul(X1,mul(X2,mul(X3,X4)))), c_0_203,['eval']).
    cnf(c_0_231, plain, (mul(X4,mul(X3,mul(X2,X1)))=mul(X1,mul(X2,mul(X3,X4)))), c_0_204,['eval']).
    cnf(c_0_232, plain, (mul(X2,mul(X1,X3))=mul(X1,mul(X2,X3))), c_0_205,['eval']).
    cnf(c_0_233, plain, (mul(X4,mul(X2,mul(X1,X3)))=mul(X1,mul(X2,mul(X3,X4)))), c_0_206,['eval']).
    cnf(c_0_234, plain, (mul(X2,mul(X4,mul(X3,X1)))=mul(X1,mul(X2,mul(X3,X4)))), c_0_166,['eval']).
    cnf(c_0_235, plain, (mul(X3,mul(X2,X1))=mul(X3,mul(X1,X2))), c_0_167,['eval']).
    cnf(c_0_236, plain, (mul(X3,mul(X2,X1))=mul(X2,mul(X1,X3))), c_0_168,['eval']).
    cnf(c_0_237, plain, (mul(X2,mul(X1,X3))=mul(X1,mul(X2,X3))), c_0_169,['eval']).
    cnf(c_0_238, plain, (mul(X3,mul(X1,X2))=mul(X1,mul(X2,X3))), c_0_170,['eval']).
    cnf(c_0_239, plain, (mul(X4,mul(X3,mul(X1,X2)))=mul(X1,mul(X2,mul(X3,X4)))), c_0_171,['eval']).
    cnf(c_0_240, plain, (mul(X1,mul(X4,mul(X3,X2)))=mul(X3,mul(X4,mul(X1,X2)))), c_0_207,['eval']).
    cnf(c_0_241, plain, (mul(X1,mul(X4,mul(X3,X2)))=mul(X2,mul(X1,mul(X3,X4)))), c_0_173,['eval']).
    cnf(c_0_242, plain, (mul(X1,mul(X4,mul(X3,X2)))=mul(X3,mul(X4,mul(X2,X1)))), c_0_208,['eval']).
    cnf(c_0_243, plain, (mul(X3,mul(X2,X1))=mul(X2,mul(X3,X1))), c_0_209,['eval']).
    cnf(c_0_244, plain, (mul(X3,mul(X2,mul(X1,X4)))=mul(X1,mul(X2,mul(X3,X4)))), c_0_211,['eval']).
    cnf(c_0_245, plain, (mul(X4,mul(X3,mul(X2,X1)))=mul(X1,mul(X2,mul(X3,X4)))), c_0_212,['eval']).
    cnf(c_0_246, plain, (mul(X2,mul(X1,X3))=mul(X1,mul(X2,X3))), c_0_213,['eval']).
    cnf(c_0_247, plain, (mul(X4,mul(X2,mul(X1,X3)))=mul(X1,mul(X2,mul(X3,X4)))), c_0_214,['eval']).
    cnf(c_0_248, plain, (mul(X2,mul(X4,mul(X3,X1)))=mul(X1,mul(X2,mul(X3,X4)))), c_0_180,['eval']).
    cnf(c_0_249, plain, (mul(X3,mul(X2,X1))=mul(X3,mul(X1,X2))), c_0_181,['eval']).
    cnf(c_0_250, plain, (mul(X3,mul(X2,X1))=mul(X2,mul(X1,X3))), c_0_182,['eval']).
    cnf(c_0_251, plain, (mul(X2,mul(X1,X3))=mul(X1,mul(X2,X3))), c_0_183,['eval']).
    cnf(c_0_252, plain, (mul(X3,mul(X1,X2))=mul(X1,mul(X2,X3))), c_0_184,['eval']).
    cnf(c_0_253, plain, (mul(X4,mul(X2,mul(X3,X1)))=mul(X1,mul(X2,mul(X3,X4)))), c_0_215,['eval']).
    cnf(c_0_254, plain, (mul(X4,mul(X2,mul(X3,X1)))=mul(X1,mul(X2,mul(X3,X4)))), c_0_216,['eval']).
    cnf(c_0_255, plain, (mul(X4,mul(X1,mul(X3,X2)))=mul(X1,mul(X2,mul(X3,X4)))), c_0_217,['eval']).
    cnf(c_0_256, plain, (mul(X4,mul(X1,mul(X2,X3)))=mul(X1,mul(X2,mul(X3,X4)))), c_0_218,['eval']).
    cnf(c_0_257, plain, (mul(X4,mul(X1,mul(X3,X2)))=mul(X1,mul(X2,mul(X3,X4)))), c_0_219,['eval']).
    cnf(c_0_258, plain, (mul(X3,mul(X1,X2))=mul(X1,mul(X2,X3))), c_0_190,['eval']).
    cnf(c_0_259, plain, (mul(X3,mul(X1,X2))=mul(X1,mul(X2,X3))), c_0_191,['eval']).
    cnf(c_0_260, plain, (mul(X1,mul(X2,mul(X3,X4)))=mul(X4,mul(X2,mul(X3,X1)))), c_0_220,['eval']).
    cnf(c_0_261, plain, (mul(X1,mul(X4,mul(X2,X3)))=mul(X3,mul(X4,mul(X2,X1)))), c_0_221,['eval']).
    cnf(c_0_262, plain, (mul(X1,mul(X3,mul(X2,X4)))=mul(X3,mul(X4,mul(X2,X1)))), c_0_222,['eval']).
    cnf(c_0_263, plain, (mul(X1,mul(X3,mul(X4,X2)))=mul(X3,mul(X4,mul(X2,X1)))), c_0_223,['eval']).
    cnf(c_0_264, plain, (mul(X1,mul(X3,mul(X2,X4)))=mul(X3,mul(X4,mul(X2,X1)))), c_0_224,['eval']).
    cnf(c_0_265, plain, (mul(X1,mul(X3,X2))=mul(X3,mul(X2,X1))), c_0_197,['eval']).
    cnf(c_0_266, plain, (mul(X1,mul(X3,X2))=mul(X3,mul(X2,X1))), c_0_198,['eval']).
    cnf(c_0_267, plain, (mul(X3,mul(X2,X1))=mul(X1,mul(X2,X3))), c_0_69,['subsumed(c_0_156)']).
    cnf(c_0_268, plain, (mul(X1,mul(X3,X2))=mul(X3,mul(X1,X2))), c_0_71,['subsumed(c_0_74)']).
    cnf(c_0_269, plain, (mul(X1,mul(X3,X2))=mul(X3,mul(X1,X2))), c_0_72,['subsumed(c_0_74)']).
    cnf(c_0_270, plain, (mul(X2,mul(X1,X3))=mul(X2,mul(X3,X1))), c_0_124,['subsumed(c_0_5)']).
    cnf(c_0_271, plain, (mul(X1,mul(X3,X2))=mul(X1,mul(X2,X3))), c_0_127,['subsumed(c_0_5)']).
    cnf(c_0_272, plain, (mul(X2,mul(X1,X3))=mul(X3,mul(X1,X2))), c_0_129,['subsumed(c_0_156)']).
    cnf(c_0_273, plain, (mul(X1,mul(X3,X2))=mul(X1,mul(X2,X3))), c_0_130,['subsumed(c_0_5)']).
    cnf(c_0_274, plain, (mul(X2,mul(X1,X3))=mul(X2,mul(X3,X1))), c_0_134,['subsumed(c_0_5)']).
    cnf(c_0_275, plain, (mul(X1,mul(X3,X2))=mul(X1,mul(X2,X3))), c_0_137,['subsumed(c_0_5)']).
    cnf(c_0_276, plain, (mul(X2,mul(X1,X3))=mul(X3,mul(X1,X2))), c_0_139,['subsumed(c_0_156)']).
    cnf(c_0_277, plain, (mul(X1,mul(X3,X2))=mul(X1,mul(X2,X3))), c_0_140,['subsumed(c_0_5)']).
    cnf(c_0_278, plain, (mul(X2,mul(X3,X1))=mul(X1,mul(X2,X3))), c_0_144,['subsumed(c_0_20)']).
    cnf(c_0_279, plain, (mul(X2,mul(X3,X1))=mul(X1,mul(X2,X3))), c_0_145,['subsumed(c_0_20)']).
    cnf(c_0_280, plain, (mul(X1,mul(X3,X2))=mul(X2,mul(X1,X3))), c_0_149,['subsumed(c_0_20)']).
    cnf(c_0_281, plain, (mul(X1,mul(X3,X2))=mul(X2,mul(X1,X3))), c_0_150,['subsumed(c_0_20)']).
    cnf(c_0_282, plain, (mul(X3,mul(X2,X1))=mul(X2,mul(X3,X1))), c_0_229,['subsumed(c_0_74)']).
    cnf(c_0_283, plain, (mul(X2,mul(X1,X3))=mul(X1,mul(X2,X3))), c_0_232,['subsumed(c_0_74)']).
    cnf(c_0_284, plain, (mul(X3,mul(X2,X1))=mul(X3,mul(X1,X2))), c_0_235,['subsumed(c_0_5)']).
    cnf(c_0_285, plain, (mul(X3,mul(X2,X1))=mul(X2,mul(X1,X3))), c_0_236,['subsumed(c_0_20)']).
    cnf(c_0_286, plain, (mul(X2,mul(X1,X3))=mul(X1,mul(X2,X3))), c_0_237,['subsumed(c_0_74)']).
    cnf(c_0_287, plain, (mul(X3,mul(X1,X2))=mul(X1,mul(X2,X3))), c_0_238,['subsumed(c_0_20)']).
    cnf(c_0_288, plain, (mul(X3,mul(X2,X1))=mul(X2,mul(X3,X1))), c_0_243,['subsumed(c_0_74)']).
    cnf(c_0_289, plain, (mul(X2,mul(X1,X3))=mul(X1,mul(X2,X3))), c_0_246,['subsumed(c_0_74)']).
    cnf(c_0_290, plain, (mul(X3,mul(X2,X1))=mul(X3,mul(X1,X2))), c_0_249,['subsumed(c_0_5)']).
    cnf(c_0_291, plain, (mul(X3,mul(X2,X1))=mul(X2,mul(X1,X3))), c_0_250,['subsumed(c_0_20)']).
    cnf(c_0_292, plain, (mul(X2,mul(X1,X3))=mul(X1,mul(X2,X3))), c_0_251,['subsumed(c_0_74)']).
    cnf(c_0_293, plain, (mul(X3,mul(X1,X2))=mul(X1,mul(X2,X3))), c_0_252,['subsumed(c_0_20)']).
    cnf(c_0_294, plain, (mul(X3,mul(X1,X2))=mul(X1,mul(X2,X3))), c_0_258,['subsumed(c_0_20)']).
    cnf(c_0_295, plain, (mul(X3,mul(X1,X2))=mul(X1,mul(X2,X3))), c_0_259,['subsumed(c_0_20)']).
    cnf(c_0_296, plain, (mul(X1,mul(X3,X2))=mul(X3,mul(X2,X1))), c_0_265,['subsumed(c_0_20)']).
    cnf(c_0_297, plain, (mul(X1,mul(X3,X2))=mul(X3,mul(X2,X1))), c_0_266,['subsumed(c_0_20)']).
    cnf(c_0_298, plain, (mul(mul(X1,X2),X3)=mul(X1,mul(X2,X3))), c_0_6,['final']).
    cnf(c_0_299, plain, (mul(X1,X2)=mul(X2,X1)), c_0_5,['final']).
    cnf(c_0_300, plain, (mul(X1,mul(X2,X3))=mul(X3,mul(X1,X2))), c_0_20,['final']).
    cnf(c_0_301, plain, (mul(X1,mul(X2,X3))=mul(X2,mul(X1,X3))), c_0_74,['final']).
    cnf(c_0_302, plain, (mul(X1,mul(X2,X3))=mul(X3,mul(X2,X1))), c_0_156,['final']).
    
    # No proof found!
    # SZS status Satisfiable
    # Processed positive unit clauses:
    cnf(c_0_298, plain, (mul(mul(X1,X2),X3)=mul(X1,mul(X2,X3)))).
    cnf(c_0_299, plain, (mul(X1,X2)=mul(X2,X1))).
    cnf(c_0_300, plain, (mul(X1,mul(X2,X3))=mul(X3,mul(X1,X2)))).
    cnf(c_0_301, plain, (mul(X1,mul(X2,X3))=mul(X2,mul(X1,X3)))).
    cnf(c_0_302, plain, (mul(X1,mul(X2,X3))=mul(X3,mul(X2,X1)))).
    
    # Processed negative unit clauses:
    
    # Processed non-unit clauses:
    
    # Unprocessed positive unit clauses:
    
    # Unprocessed negative unit clauses:
    
    # Unprocessed non-unit clauses:
    
    
    # Parsed axioms                        : 2
    # Removed by relevancy pruning/SinE    : 0
    # Initial clauses                      : 2
    # Removed in clause preprocessing      : 0
    # Initial clauses in saturation        : 2
    # Processed clauses                    : 96
    # ...of these trivial                  : 54
    # ...subsumed                          : 37
    # ...remaining for further processing  : 5
    # Other redundant clauses eliminated   : 0
    # Clauses deleted for lack of memory   : 0
    # Backward-subsumed                    : 0
    # Backward-rewritten                   : 0
    # Generated clauses                    : 97
    # ...of the previous two non-redundant : 94
    # ...aggressively subsumed             : 0
    # Contextual simplify-reflections      : 0
    # Paramodulations                      : 97
    # Factorizations                       : 0
    # NegExts                              : 0
    # Equation resolutions                 : 0
    # Disequality decompositions           : 0
    # Total rewrite steps                  : 67
    # ...of those cached                   : 50
    # Propositional unsat checks           : 0
    #    Propositional check models        : 0
    #    Propositional check unsatisfiable : 0
    #    Propositional clauses             : 0
    #    Propositional clauses after purity: 0
    #    Propositional unsat core size     : 0
    #    Propositional preprocessing time  : 0.000
    #    Propositional encoding time       : 0.000
    #    Propositional solver time         : 0.000
    #    Success case prop preproc time    : 0.000
    #    Success case prop encoding time   : 0.000
    #    Success case prop solver time     : 0.000
    # Current number of processed clauses  : 5
    #    Positive orientable unit clauses  : 1
    #    Positive unorientable unit clauses: 4
    #    Negative unit clauses             : 0
    #    Non-unit-clauses                  : 0
    # Current number of unprocessed clauses: 0
    # ...number of literals in the above   : 0
    # Current number of archived formulas  : 0
    # Current number of archived clauses   : 0
    # Clause-clause subsumption calls (NU) : 0
    # Rec. Clause-clause subsumption calls : 0
    # Non-unit clause-clause subsumptions  : 0
    # Unit Clause-clause subsumption calls : 6
    # Rewrite failures with RHS unbound    : 0
    # BW rewrite match attempts            : 12
    # BW rewrite match successes           : 12
    # Condensation attempts                : 0
    # Condensation successes               : 0
    # Termbank termtop insertions          : 662
    # Search garbage collected termcells   : 0

```python
! eprover-ho --answers=10 --term-ordering=KBO6 --literal-selection-strategy="SelectLargestNegLit" --conjectures-are-questions /tmp/eq.p
```

    # Initializing proof state
    # Scanning for AC axioms
    # mul is AC
    # AC handling enabled
    #
    #cnf(i_0_4, plain, (mul(X1,X2)=mul(X2,X1))).
    #
    #cnf(i_0_3, plain, (mul(mul(X1,X2),X3)=mul(X1,mul(X2,X3)))).
    #
    #cnf(i_0_6, plain, (mul(X1,mul(X2,X3))=mul(X3,mul(X1,X2)))).
    ##
    #cnf(i_0_9, plain, (mul(X2,mul(X1,X3))=mul(X1,mul(X2,X3)))).
    ######
    #cnf(i_0_26, plain, (mul(X3,mul(X2,X1))=mul(X1,mul(X2,X3)))).
    ################################
    #cnf(i_0_5, negated_conjecture, ($answer(esk1_3(X3,X2,X1))|mul(X1,mul(X2,X3))!=mul(X3,mul(X1,X3)))).
    ## SZS status Theorem
    # SZS answers Tuple [[X1, X1, X1]|_]
    
    #cnf(i_0_103, negated_conjecture, ($answer(esk1_3(X1,X1,X1)))).
    #
    #cnf(i_0_111, negated_conjecture, ($answer(esk1_3(X1,X2,X3))|mul(X1,mul(X1,X3))!=mul(X3,mul(X2,X1)))).
    ##
    #cnf(i_0_114, negated_conjecture, ($answer(esk1_3(X1,X2,X3))|mul(X3,mul(X1,X1))!=mul(X3,mul(X2,X1)))).
    ## SZS answers Tuple [[X1, X1, X2]|_]
    
    #cnf(i_0_173, negated_conjecture, ($answer(esk1_3(X1,X1,X2)))).
    #######
    #cnf(i_0_127, negated_conjecture, ($answer(esk1_3(X1,X2,X3))|mul(X3,mul(X1,X2))!=mul(X1,mul(X3,X1)))).
    ###
    #cnf(i_0_130, negated_conjecture, ($answer(esk1_3(X1,X2,X3))|mul(X2,mul(X1,X3))!=mul(X1,mul(X3,X1)))).
    ####
    #cnf(i_0_133, negated_conjecture, ($answer(esk1_3(X1,X2,X3))|mul(X1,mul(X3,X2))!=mul(X1,mul(X3,X1)))).
    #
    #cnf(i_0_134, negated_conjecture, ($answer(esk1_3(X1,X2,X3))|mul(X2,mul(X3,X1))!=mul(X1,mul(X3,X1)))).
    ##
    #cnf(i_0_135, negated_conjecture, ($answer(esk1_3(X1,X2,X3))|mul(X1,mul(X2,X3))!=mul(X1,mul(X3,X1)))).
    ####
    #cnf(i_0_146, negated_conjecture, ($answer(esk1_3(X1,X2,X3))|mul(X3,mul(X1,X2))!=mul(X1,mul(X1,X3)))).
    ##
    #cnf(i_0_149, negated_conjecture, ($answer(esk1_3(X1,X2,X3))|mul(X2,mul(X1,X3))!=mul(X1,mul(X1,X3)))).
    ####
    #cnf(i_0_152, negated_conjecture, ($answer(esk1_3(X1,X2,X3))|mul(X1,mul(X3,X2))!=mul(X1,mul(X1,X3)))).
    ##
    #cnf(i_0_153, negated_conjecture, ($answer(esk1_3(X1,X2,X3))|mul(X2,mul(X3,X1))!=mul(X1,mul(X1,X3)))).
    #
    #cnf(i_0_154, negated_conjecture, ($answer(esk1_3(X1,X2,X3))|mul(X1,mul(X2,X3))!=mul(X1,mul(X1,X3)))).
    ###############
    #cnf(i_0_181, negated_conjecture, ($answer(esk1_3(X1,X2,X3))|mul(X3,mul(X1,X2))!=mul(X3,mul(X1,X1)))).
    ##
    #cnf(i_0_184, negated_conjecture, ($answer(esk1_3(X1,X2,X3))|mul(X2,mul(X1,X3))!=mul(X3,mul(X1,X1)))).
    ####
    #cnf(i_0_187, negated_conjecture, ($answer(esk1_3(X1,X2,X3))|mul(X1,mul(X3,X2))!=mul(X3,mul(X1,X1)))).
    ##
    #cnf(i_0_188, negated_conjecture, ($answer(esk1_3(X1,X2,X3))|mul(X2,mul(X3,X1))!=mul(X3,mul(X1,X1)))).
    #
    #cnf(i_0_189, negated_conjecture, ($answer(esk1_3(X1,X2,X3))|mul(X1,mul(X2,X3))!=mul(X3,mul(X1,X1)))).
    ##############################################################################################################################################################################################################################################################################################################################################
    #cnf(i_0_120, negated_conjecture, ($answer(esk1_3(X1,mul(X2,X3),X4))|mul(X4,mul(X2,mul(X3,X1)))!=mul(X1,mul(X4,X1)))).
    #
    #cnf(i_0_139, negated_conjecture, ($answer(esk1_3(X1,mul(X2,X3),X4))|mul(X4,mul(X2,mul(X3,X1)))!=mul(X1,mul(X1,X4)))).
    #
    #cnf(i_0_174, negated_conjecture, ($answer(esk1_3(X1,mul(X2,X3),X4))|mul(X4,mul(X2,mul(X3,X1)))!=mul(X4,mul(X1,X1)))).
    ##
    #cnf(i_0_229, negated_conjecture, ($answer(esk1_3(X1,mul(X2,X3),X4))|mul(X4,mul(X3,mul(X1,X2)))!=mul(X1,mul(X4,X1)))).
    #
    #cnf(i_0_230, negated_conjecture, ($answer(esk1_3(X1,mul(X2,X3),X4))|mul(X4,mul(X2,mul(X1,X3)))!=mul(X1,mul(X4,X1)))).
    #
    #cnf(i_0_231, negated_conjecture, ($answer(esk1_3(X1,mul(X2,X3),X4))|mul(X4,mul(X3,mul(X2,X1)))!=mul(X1,mul(X4,X1)))).
    ###
    #cnf(i_0_271, negated_conjecture, ($answer(esk1_3(X1,mul(X2,X3),X4))|mul(X2,mul(X3,mul(X1,X4)))!=mul(X1,mul(X4,X1)))).
    #
    #cnf(i_0_298, negated_conjecture, ($answer(esk1_3(X1,mul(X2,X3),X4))|mul(X1,mul(X2,mul(X3,X4)))!=mul(X1,mul(X4,X1)))).
    ## SZS answers Tuple [[mul(X1,X2), mul(X2,X1), X2]|_]
    
    #cnf(i_0_1048, negated_conjecture, ($answer(esk1_3(mul(X1,X2),mul(X2,X1),X2)))).
    ## SZS answers Tuple [[mul(X1,mul(X2,X3)), mul(X2,mul(X3,X1)), X3]|_]
    
    #cnf(i_0_1094, negated_conjecture, ($answer(esk1_3(mul(X1,mul(X2,X3)),mul(X2,mul(X3,X1)),X3)))).
    ## SZS answers Tuple [[mul(X1,mul(X2,X3)), mul(X1,mul(X3,X2)), X3]|_]
    
    #cnf(i_0_1095, negated_conjecture, ($answer(esk1_3(mul(X1,mul(X2,X3)),mul(X1,mul(X3,X2)),X3)))).
    ## SZS answers Tuple [[mul(X1,mul(X2,X3)), mul(X2,mul(X1,X3)), X3]|_]
    
    #cnf(i_0_1096, negated_conjecture, ($answer(esk1_3(mul(X1,mul(X2,X3)),mul(X2,mul(X1,X3)),X3)))).
    #### SZS answers Tuple [[mul(X1,mul(X2,X3)), mul(X3,mul(X1,X2)), X3]|_]
    
    #cnf(i_0_1101, negated_conjecture, ($answer(esk1_3(mul(X1,mul(X2,X3)),mul(X3,mul(X1,X2)),X3)))).
    ####### SZS answers Tuple [[mul(X1,mul(X2,X3)), mul(X3,mul(X2,X1)), X3]|_]
    
    #cnf(i_0_1124, negated_conjecture, ($answer(esk1_3(mul(X1,mul(X2,X3)),mul(X3,mul(X2,X1)),X3)))).
    ##### SZS answers Tuple [[mul(X1,mul(X3,X2)), mul(X2,mul(X3,X1)), X3]|_]
    
    #cnf(i_0_1135, negated_conjecture, ($answer(esk1_3(mul(X1,mul(X3,X2)),mul(X2,mul(X3,X1)),X3)))).
    ### SZS answers Tuple [[mul(X3,mul(X1,X2)), mul(X2,mul(X3,X1)), X3]|_]
    
    # Proof found!

## Prolog

```python
%%file /tmp/prolog.p

cnf(add_succ, axiom, add(s(X),Y,s(Z)) | ~add(X, Y, Z)).
cnf(add_z, axiom, add(z, Y, Y)).
fof(add_g, conjecture, ?[X,Y]: add(X,Y,s(s(z)))).

```

    Writing /tmp/prolog.p

```python
! eprover-ho --output-level=6 /tmp/prolog.p
```

    cnf(add_succ, axiom, (add(s(X1),X2,s(X3))|~add(X1,X2,X3)), file('/tmp/prolog.p', add_succ)).
    cnf(add_z, axiom, (add(z,X1,X1)), file('/tmp/prolog.p', add_z)).
    fof(add_g, conjecture, ?[X2, X1]:(add(X2,X1,s(s(z)))), file('/tmp/prolog.p', add_g)).
    fof(c_0_4, negated_conjecture, ~(?[X2, X1]:(add(X2,X1,s(s(z))))),inference(assume_negation, [status(cth)],[c_0_3])).
    cnf(c_0_5, plain, (add(s(X1),X2,s(X3))|~add(X1,X2,X3)),inference(fof_simplification, [status(thm)],[c_0_1])).
    fof(c_0_6, negated_conjecture, ![X2, X1]:(~add(X2,X1,s(s(z)))),inference(fof_nnf, [status(thm)],[c_0_4])).
    fof(c_0_7, negated_conjecture, ![X4, X5]:(~add(X4,X5,s(s(z)))),inference(variable_rename, [status(thm)],[c_0_6])).
    fof(c_0_8, negated_conjecture, ![X4, X5]:(~add(X4,X5,s(s(z)))),inference(fof_nnf, [status(thm)],[c_0_7])).
    cnf(c_0_9, negated_conjecture, (~add(X1,X2,s(s(z)))),inference(split_conjunct, [status(thm)],[c_0_8])).
    # Initializing proof state
    cnf(c_0_10, plain, (add(z,X1,X1)), c_0_-9223372036854775801,['eval']).
    cnf(c_0_11, negated_conjecture, (~add(X1,X2,s(s(z)))), c_0_9,['eval']).
    cnf(c_0_12, plain, (add(s(X1),X2,s(X3))|~add(X1,X2,X3)), c_0_-9223372036854775802,['eval']).
    # Scanning for AC axioms
    cnf(c_0_13, plain, (add(z,X1,X1)), c_0_10,['new_given']).
    cnf(c_0_14, plain, (add(s(X1),X2,s(X3))|~add(X1,X2,X3)), c_0_12,['new_given']).
    cnf(c_0_15, negated_conjecture, (~add(X1,X2,s(s(z)))), c_0_11,['new_given']).
    cnf(c_0_16, negated_conjecture, ($false),inference(pm,[status(thm)],[c_0_15,c_0_13])).
    cnf(c_0_17, negated_conjecture, (~add(X1,X2,s(z))),inference(pm,[status(thm)],[c_0_15,c_0_14])).
    cnf(c_0_18, negated_conjecture, ($false), c_0_16,['proof']).
    
    # Proof found!
    # SZS status Theorem
    # Parsed axioms                        : 3
    # Removed by relevancy pruning/SinE    : 0
    # Initial clauses                      : 3
    # Removed in clause preprocessing      : 0
    # Initial clauses in saturation        : 3
    # Processed clauses                    : 3
    # ...of these trivial                  : 0
    # ...subsumed                          : 0
    # ...remaining for further processing  : 3
    # Other redundant clauses eliminated   : 0
    # Clauses deleted for lack of memory   : 0
    # Backward-subsumed                    : 0
    # Backward-rewritten                   : 0
    # Generated clauses                    : 2
    # ...of the previous two non-redundant : 0
    # ...aggressively subsumed             : 0
    # Contextual simplify-reflections      : 0
    # Paramodulations                      : 2
    # Factorizations                       : 0
    # NegExts                              : 0
    # Equation resolutions                 : 0
    # Disequality decompositions           : 0
    # Total rewrite steps                  : 0
    # ...of those cached                   : 0
    # Propositional unsat checks           : 0
    #    Propositional check models        : 0
    #    Propositional check unsatisfiable : 0
    #    Propositional clauses             : 0
    #    Propositional clauses after purity: 0
    #    Propositional unsat core size     : 0
    #    Propositional preprocessing time  : 0.000
    #    Propositional encoding time       : 0.000
    #    Propositional solver time         : 0.000
    #    Success case prop preproc time    : 0.000
    #    Success case prop encoding time   : 0.000
    #    Success case prop solver time     : 0.000
    # Current number of processed clauses  : 3
    #    Positive orientable unit clauses  : 1
    #    Positive unorientable unit clauses: 0
    #    Negative unit clauses             : 1
    #    Non-unit-clauses                  : 1
    # Current number of unprocessed clauses: 0
    # ...number of literals in the above   : 0
    # Current number of archived formulas  : 0
    # Current number of archived clauses   : 0
    # Clause-clause subsumption calls (NU) : 0
    # Rec. Clause-clause subsumption calls : 0
    # Non-unit clause-clause subsumptions  : 0
    # Unit Clause-clause subsumption calls : 0
    # Rewrite failures with RHS unbound    : 0
    # BW rewrite match attempts            : 0
    # BW rewrite match successes           : 0
    # Condensation attempts                : 0
    # Condensation successes               : 0
    # Termbank termtop insertions          : 111
    # Search garbage collected termcells   : 14

```python
! eprover-ho --conjectures-are-questions  --answers=3 /tmp/prolog.p
```

    # Initializing proof state
    # Scanning for AC axioms
    #
    #cnf(i_0_4, plain, (add(z,X1,X1))).
    #
    #cnf(i_0_3, plain, (add(s(X1),X2,s(X3))|~add(X1,X2,X3))).
    #
    #cnf(i_0_5, negated_conjecture, ($answer(esk1_2(X1,X2))|~add(X1,X2,s(s(z))))).
    ## SZS status Theorem
    # SZS answers Tuple [[z, s(s(z))]|_]
    
    #cnf(i_0_6, negated_conjecture, ($answer(esk1_2(z,s(s(z)))))).
    #
    #cnf(i_0_7, negated_conjecture, ($answer(esk1_2(s(X1),X2))|~add(X1,X2,s(z)))).
    ## SZS answers Tuple [[s(z), s(z)]|_]
    
    #cnf(i_0_8, negated_conjecture, ($answer(esk1_2(s(z),s(z))))).
    #
    #cnf(i_0_9, negated_conjecture, ($answer(esk1_2(s(s(X1)),X2))|~add(X1,X2,z))).
    ## SZS answers Tuple [[s(s(z)), z]|_]
    
    # Proof found!

## Simplifier

```python
%%file /tmp/simp.p
cnf(mul_zero, axiom, mul(X,zero) = zero).
cnf(mul_comm, axiom, mul(X,Y) = mul(Y,X)).
cnf(mul_assoc, axiom, mul(X,mul(Y,Z)) = mul(mul(X,Y),Z)).
cnf(add_comm, axiom, add(X,Y) = add(Y,X)).
cnf(add_assoc, axiom, add(X,add(Y,Z)) = add(add(X,Y),Z)).
cnf(add_zero, axiom, add(X,zero) = X).
cnf(abc, axiom, add(a,b) = c).

cnf(goal_expr, axiom, t = add(add(a, mul(a,zero)), add(zero, b))).

```

    Overwriting /tmp/simp.p

 --processed-clauses-limit=100

```python
! eprover-ho --print-saturated --unprocessed-limit=100 --output-level=6 /tmp/simp.p
```

## Functional programs

Constructors should come less in the precendence.
LPO is more like functional programming.
KBO is more like simplification

Without the precendence annotations, eprover is not terminating

```python
%%file /tmp/add.p

cnf(add_succ, axiom, add(s(X),Y) = s(add(X,Y))).
cnf(add_z, axiom, add(z, Y) = Y).
cnf(addn, axiom, add())
```

    Writing /tmp/add.p

```python
! eprover-ho --print-saturated  /tmp/add.p % non terminating
```

auto is not better?

```python
! eprover-ho --print-saturated --auto-schedule /tmp/add.p
```

    # Preprocessing class: FSSSSMSSSSSNFFN.
    # Scheduled 1 strats onto 1 cores with 300 seconds (300 total)
    # Starting G-E--_302_C18_F1_URBAN_RG_S04BN with 300s (1) cores
    ^C

```python
! eprover-ho --print-saturated --term-ordering=LPO4 --precedence="add>s>z" /tmp/add.p
```

    # Initializing proof state
    # Scanning for AC axioms
    #
    #cnf(i_0_4, plain, (add(z,X1)=X1)).
    #
    #cnf(i_0_3, plain, (add(s(X1),X2)=s(add(X1,X2)))).
    
    # No proof found!
    # SZS status Satisfiable
    # Processed positive unit clauses:
    cnf(i_0_4, plain, (add(z,X1)=X1)).
    cnf(i_0_3, plain, (add(s(X1),X2)=s(add(X1,X2)))).
    
    # Processed negative unit clauses:
    
    # Processed non-unit clauses:
    
    # Unprocessed positive unit clauses:
    
    # Unprocessed negative unit clauses:
    
    # Unprocessed non-unit clauses:
    
    

Older notes
E prover
enormalizer is an interesting sounding program. Give it a pile of unit equalities and it will normalize with respect to thm EPR grounder to DIMACS The e calculus is a bit puzzling. I haven’t seen the analog for vampire

2.6 manual It’s also in the github repo if you make doc

I like how –answer mode works a little better for e.

Database printing feature -S. Doesn’t print stuff I would expect though? Kind of prints everything by default right? Early stopping conditions clause size

eprover --help | less
--watchlist - “constructive” proofs that aren’t seeded by refuation training - you can train it if you have a database of indicative theorems. This might be useful if you have a sequence of increasingly hard theorems, or if you are making a tool that spits out formula. -S print saturated clause set -W literaeelection stretagory NoGeneration will inhibit all generating instances “Each of the strategies that do actually select negative literals has a corresponding counterpart starting with P that additionally allows paramodulation into maximal positive literals”

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
--generated-limit=100 Ok this basically did what i wanted. I’m not sure what it is though?

“The most natural clause representation for E is probably a literal disjunction: a=
true;c!=$true.”

## Equality Saturation

Somewhat like datalog, but it's worse here. The ordering is really important to get fair search.

We want the goal term in immediately.

%%file /tmp/eq.p
cnf(goalterm, axiom, t = div(mul(a, two), two)).
cnf(mulcomm, axiom, mul(X,Y) = mul(Y,X)).
cnf(mulassoc, axiom, mul(X,mul(Y,Z)) = mul(mul(X,Y),Z)).
cnf(mulunit, axiom, mul(X, one) = X).
cnf(mulinv, axiom, div(mul(X,Y), Y) = X | Y = zero).
cnf(shiftmul, axiom, mul(X, two) = shift(X, one)).

# Vampire

Maybe I should play with these.
--memory
--cores

--selection (-s)
        Selection methods 2,3,4,10,11 are complete by virtue of extending Maximal
        i.e. they select the best among maximal. Methods 1002,1003,1004,1010,1011
        relax this restriction and are therefore not complete.
         0     - Total (select everything)
         1     - Maximal
         2     - ColoredFirst, MaximalSize then Lexicographical
         3     - ColoredFirst, NoPositiveEquality, LeastTopLevelVariables,
                  LeastDistinctVariables then Lexicographical
         4     - ColoredFirst, NoPositiveEquality, LeastTopLevelVariables,
                  LeastVariables, MaximalSize then Lexicographical
         10    - ColoredFirst, NegativeEquality, MaximalSize, Negative then Lexicographical
         11    - Lookahead
         666   - Random
         1002  - Incomplete version of 2
         1003  - Incomplete version of 3
         1004  - Incomplete version of 4
         1010  - Incomplete version of 10
         1011  - Incomplete version of 11
         1666  - Incomplete version of 666
        Or negated, which means that reversePolarity is true i.e. for selection
        we treat all negative non-equality literals as positive and vice versa
        (can only apply to non-equality literals).

        default: 10

--symbol_precedence (-sp)
        Vampire uses term orderings which require a precedence relation between
        symbols.
        Arity orders symbols by their arity (and reverse_arity takes the reverse
        of this) and occurrence orders symbols by the order they appear in the
        problem. Then we have a few precedence generating schemes adopted from
        E: frequency - sort by frequency making rare symbols large, reverse does
        the opposite, (For the weighted versions, each symbol occurrence counts
        as many times as is the length of the clause in which it occurs.) unary_first
        is like arity, except that unary symbols are maximal (and ties are broken
        by frequency), unary_frequency is like frequency, except that unary symbols
        are maximal, const_max makes constants the largest, then falls back to
        arity, const_min makes constants the smallest, then falls back to reverse_arity,
        const_frequency makes constants the smallest, then falls back to frequency.
        default: arity
        values: arity,occurrence,reverse_arity,unary_first,const_max,const_min,scramble,
                frequency,unary_frequency,const_frequency,reverse_frequency,
                weighted_frequency,reverse_weighted_frequency
--term-rdering kbo lpo
--induction = none, stuct, int,both

default on rules

--backward_demodulation (-bd)
        Oriented rewriting of kept clauses by newly derived unit equalities
        s = t     L[sθ] \/ C
        ---------------------   where sθ > tθ (replaces RHS)
         L[tθ] \/ C

        default: all
        values: all,off,preordered
--binary_resolution (-br)
        Standard binary resolution i.e.
        C \/ t     D \/ s
        ---------------------
        (C \/ D)θ
        where θ = mgu(t,-s) and t selected
        default: on
--demodulation_redundancy_check (-drc)
        The following cases of backward and forward demodulation do not preserve
        completeness:
        s = t     s = t1 \/ C    s = t     s != t1 \/ C
        ---------------------    ---------------------
        t = t1 \/ C              t != t1 \/ C
        where t > t1 and s = t > C (RHS replaced)
        With `on`, we check this condition and don't demodulate if we could violate
        completeness.
        With `encompass`, we treat demodulations (both forward and backward) as
        encompassment demodulations (as defined by Duarte and Korovin in 2022's
        IJCAR paper).
        With `off`, we skip the checks, save time, but become incomplete.
        default: on
        values: off,encompass,on
    --forward_demodulation (-fd)
        Oriented rewriting of newly derived clauses by kept unit equalities
        s = t     L[sθ] \/ C
        ---------------------  where sθ > tθ
         L[tθ] \/ C
        If 'preordered' is set, only equalities s = t where s > t are used for
        rewriting.
        default: all
        values: all,off,preordered
--forward_subsumption (-fs)
        Perform forward subsumption deletion.
        default: on
--forward_subsumption_resolution (-fsr)
        Perform forward subsumption resolution.
        default: on
--simultaneous_superposition (-sims)
        Rewrite the whole RHS clause during superposition, not just the target
        literal.
        default: on
--superposition (-sup)
        Control superposition. Turning off this core inference leads to an incomplete
        calculus on equational problems.
        default: on
--superposition_from_variables (-sfv)
        Perform superposition from variables.
        default: on

--unit_resulting_resolution (-urr)
        Uses unit resulting resolution only to derive empty clauses (may be useful
        for splitting). 'ec_only' only derives empty clauses, 'on' does everything
        (but implements a heuristic to skip deriving more than one empty clause),
        'full' ignores this heuristic and is thus complete also under AVATAR.
        default: off
        values: ec_only,off,on,full

--show_ordering
--show_induction
--manual_cs clause select manually
--show_everything

Pretty interesting

```python
! vampire --show_everything on --manual_cs on /tmp/path.p
```
