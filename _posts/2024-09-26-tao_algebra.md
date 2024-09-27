---
title: Knuckledragger Solvers for Terence Tao's Equational Reasoning Challenge
date: 2024-09-26
---

Terence Tao has put forward an interesting equational reasoning challenge.

- <https://mathstodon.xyz/@tao/110736805384878353>
- <https://terrytao.wordpress.com/2024/09/25/a-pilot-project-in-universal-algebra-to-explore-new-ways-to-collaborate-and-use-machine-assistance/>
- <https://mathoverflow.net/questions/450890/is-there-an-identity-between-the-commutative-identity-and-the-constant-identity/450905#450905>
- <https://github.com/teorth/equational_theories>

It is reminiscent of a famous success story of automated theorem proving, proving the robbins algebras are boolean <https://www.cs.unm.edu/~mccune/papers/robbins/> a previously unsolved conjecture which was shown by Bill McCune's EQP solver in 1996. Hopefully solvers are a lot more powerful now.

I've been fiddling with building a semi-automated proof assistant in python called Knuckledragger.  <https://github.com/philzook58/knuckledragger>

Knuckledragger is structured around Z3, but recently I've been bolting in the various automated solvers. Z3 is excellent at many things (first class at the grounded problems one often encoutners in software verification), but weaker at quantifier reasoning or equational reasoning.

For these, Vampire, eprover, Twee, Zipperposition, and Prover9 are good candidates. I judge this somewhat by examining the CASC <https://tptp.org/CASC/J12/> results

What I've done is built a pretty printer to the first order and higher order TPTP format. This printer is wrapper around by a Solver object that mimics exactly Z3's python api so that I can swap it in.

Even if you don't buy into what I'm generally doing in Knuckledragger (a system to weave these results kind of Hilbert style into larger proofs), I think having easy installation and programmatic access to the solvers in python could be quite useful.

Access to the solvers is not new. Isabelle <https://isabelle.in.tum.de/> and Why3 <https://www.why3.org/>   also both have these solvers accessible if you prefer.

The TPTP organization <https://www.tptp.org/> , largely orchestrated by Geoff Sutcliffe, has many resources, but especially System on TPTP <https://tptp.org/cgi-bin/SystemOnTPTP> , which lets you submit problem files online without installing these solvers.

One big advantage of python is the massive preexisting ecosystem and infrastructure. Case in point. You can try this blog post out on Google collab quite easily by clicking this link <https://colab.research.google.com/github/philzook58/philzook58.github.io/blob/master/pynb/2024-09-26-tao_algebra.ipynb>

Running this cell will install Knuckledragger and the external solvers. It'll take a good 5 minutes to do all that compiling. Have faith. It could ber better when I ship a binary for eprover.

```bash
%%bash
git clone https://github.com/philzook58/knuckledragger.git
cd knuckledragger
python3 -m pip install -e .
```

```python
! cd knuckledragger && ./install.sh # get and build external solvers
```

I had to restart the jupyter kernel on colab for the `kdrag` package to be found.

```python
import os
os._exit(00)
```

Alright! Now we're ready to go!

Currently I have:

- Vampire using SMTlib input <https://vprover.github.io/>
- Higher Order Vampire
- Eprover-HO <https://github.com/eprover/eprover>
- Twee <https://nick8325.github.io/twee/>
- Zipperposition - <https://github.com/sneeuwballen/zipperposition>
- nanoCoP-i - an intuitionstic prover. I'm excited for this one
- Leo-III

I've always been rather impressed by Twee's proof output ,so let us show that.

```python
import kdrag as kd
import kdrag.solvers as solvers
import kdrag.smt as smt # Literally a reexporting of z3

T = smt.DeclareSort("T")
x,y,z = smt.Consts("x y z", T)
mul = smt.Function("mul", T, T, T)
kd.notation.mul.define([x,y], mul(x,y)) # This gives us multiplication notation.

s = solvers.TweeSolver()
s.add(smt.ForAll([x,y,z], (x * x) * y == y * x))
s.add(smt.Not(smt.ForAll([x,y], x * y == y * x))) # Negate the theorem to be proved for a refutation
s.set("timeout", 1000)
print(s.check())
print(s.proof().decode())
```

    unsat
    Here is the input problem:
      Axiom 1 (flattening): mul_8e3 = mul_8e(y_91, x_92).
      Axiom 2 (flattening): mul_8e2 = mul_8e(x_92, y_91).
      Axiom 3 (ax_0): mul_8e(mul_8e(X, X), Y) = mul_8e(Y, X).
      Goal 1 (ax_1): mul_8e(x_92, y_91) = mul_8e(y_91, x_92).
    
    1. mul_8e(y_91, x_92) -> mul_8e3
    2. mul_8e(x_92, y_91) -> mul_8e2
    3. mul_8e(mul_8e(X, X), Y) -> mul_8e(Y, X)
    4. mul_8e(X, mul_8e(Y, Y)) -> mul_8e(X, Y)
    5. mul_8e(X, Y) <-> mul_8e(Y, X)
    6. mul_8e2 -> mul_8e3
    
    % SZS status Unsatisfiable
    
    % SZS output start Proof
    Axiom 1 (ax_0): mul_8e(mul_8e(X, X), Y) = mul_8e(Y, X).
    
    Goal 1 (ax_1): mul_8e(x_92, y_91) = mul_8e(y_91, x_92).
    Proof:
      mul_8e(x_92, y_91)
    = { by axiom 1 (ax_0) R->L }
      mul_8e(mul_8e(y_91, y_91), x_92)
    = { by axiom 1 (ax_0) R->L }
      mul_8e(mul_8e(x_92, x_92), mul_8e(y_91, y_91))
    = { by axiom 1 (ax_0) R->L }
      mul_8e(mul_8e(mul_8e(y_91, y_91), mul_8e(y_91, y_91)), mul_8e(x_92, x_92))
    = { by axiom 1 (ax_0) }
      mul_8e(mul_8e(mul_8e(y_91, y_91), y_91), mul_8e(x_92, x_92))
    = { by axiom 1 (ax_0) }
      mul_8e(mul_8e(y_91, y_91), mul_8e(x_92, x_92))
    = { by axiom 1 (ax_0) }
      mul_8e(mul_8e(x_92, x_92), y_91)
    = { by axiom 1 (ax_0) }
      mul_8e(y_91, x_92)
    % SZS output end Proof
    
    RESULT: Unsatisfiable (the axioms are contradictory).
    

You can see the file actually being generated. I have not yet turned on mangling the filename. You can see the constants do need to be mangled with a unique identifier

```python
! cat /tmp/twee.p
```

    % TPTP file generated by Knuckledragger
    tff(t_type, type, t : $tType ).
    % Declarations
    tff(mul_decl, type, mul_8e : t * t > t).
    % Axioms and assertions
    tff(ax_0, axiom, (![Z_90:t, Y_91:t, X_92:t] : (mul_8e(mul_8e(X_92, X_92), Y_91) = mul_8e(Y_91, X_92)))).
    tff(ax_1, axiom, ~((![Y_91:t, X_92:t] : (mul_8e(X_92, Y_91) = mul_8e(Y_91, X_92))))).

I also added the ability to access the solver directly. This has been useful for debugging and testing, but could be useful for other purposes

```python
! python3 -m kdrag.solvers twee /tmp/twee.p
```

    Here is the input problem:
      Axiom 1 (flattening): mul_8e3 = mul_8e(y_91, x_92).
      Axiom 2 (flattening): mul_8e2 = mul_8e(x_92, y_91).
      Axiom 3 (ax_0): mul_8e(mul_8e(X, X), Y) = mul_8e(Y, X).
      Goal 1 (ax_1): mul_8e(x_92, y_91) = mul_8e(y_91, x_92).
    
    1. mul_8e(y_91, x_92) -> mul_8e3
    2. mul_8e(x_92, y_91) -> mul_8e2
    3. mul_8e(mul_8e(X, X), Y) -> mul_8e(Y, X)
    4. mul_8e(X, mul_8e(Y, Y)) -> mul_8e(X, Y)
    5. mul_8e(X, Y) <-> mul_8e(Y, X)
    6. mul_8e2 -> mul_8e3
    
    The conjecture is true! Here is a proof.
    
    Axiom 1 (ax_0): mul_8e(mul_8e(X, X), Y) = mul_8e(Y, X).
    
    Goal 1 (ax_1): mul_8e(x_92, y_91) = mul_8e(y_91, x_92).
    Proof:
      [32mmul_8e(x_92, y_91)[m
    = [1m{ by axiom 1 (ax_0) R->L }[m
      [32mmul_8e(mul_8e(y_91, y_91), x_92)[m
    = [1m{ by axiom 1 (ax_0) R->L }[m
      [32mmul_8e(mul_8e(x_92, x_92), mul_8e(y_91, y_91))[m
    = [1m{ by axiom 1 (ax_0) R->L }[m
      mul_8e([32mmul_8e(mul_8e(y_91, y_91), mul_8e(y_91, y_91))[m, mul_8e(x_92, x_92))
    = [1m{ by axiom 1 (ax_0) }[m
      mul_8e([32mmul_8e(mul_8e(y_91, y_91), y_91)[m, mul_8e(x_92, x_92))
    = [1m{ by axiom 1 (ax_0) }[m
      [32mmul_8e(mul_8e(y_91, y_91), mul_8e(x_92, x_92))[m
    = [1m{ by axiom 1 (ax_0) }[m
      [32mmul_8e(mul_8e(x_92, x_92), y_91)[m
    = [1m{ by axiom 1 (ax_0) }[m
      mul_8e(y_91, x_92)
    
    RESULT: Unsatisfiable (the axioms are contradictory).

# Vampire

Vampire very often wins many categories of the CASC competition. It is one of the best automated solvers of it's kind.

```python
# This one actually uses the smt printer
s = solvers.VampireSolver()
s.add(smt.ForAll([x,y,z], (x * x) * y == y * x))
s.add(smt.Not(smt.ForAll([x,y], x * y == y * x)))
s.set("timeout", 1000)
print(s.check())
```

    unsat

```python
!cat /tmp/vampire.smt2
```

    (set-logic ALL)
    (declare-sort T 0)
    ;;declarations
    (declare-fun mul (T T) T)
    ;;axioms
    (assert (forall ((x T) (y T) (z T)) (= (mul (mul x x) y) (mul y x))))
    (assert (not (forall ((x T) (y T)) (= (mul x y) (mul y x)))))
    (check-sat)

# Higher Order

The next two solvers also support higher order reasoning (they accept lambda terms in their input). The recent progress in that direction is very exciting. I've  got blog posts to write on how to use these sorts of things.

```python
s = solvers.VampireTHFSolver()
s.add(smt.ForAll([x,y,z], (x * x) * y == y * x))
s.add(smt.Not(smt.ForAll([x,y], x * y == y * x)))
s.set("timeout", 1000)
print(s.check())
print(s.proof().decode())
```

    unsat
    % WARNING: time unlimited strategy and instruction limiting not in place - attemping to translate instructions to time
    % lrs+1002_1:1_au=on:av=off:fd=off:fde=unused:ntd=on:sos=on:sp=frequency:ss=axioms:i=782:si=on:rtra=on_0 on vampire for (3ds/782Mi)
    % Refutation not found, incomplete strategy
    % ------------------------------
    % Version: Vampire 4.8 HO - Sledgehammer schedules (2023-10-19)
    % Termination reason: Refutation not found, incomplete strategy
    
    
    % Memory used [KB]: 895
    % Time elapsed: 0.001 s
    % ------------------------------
    % ------------------------------
    % WARNING: time unlimited strategy and instruction limiting not in place - attemping to translate instructions to time
    % lrs+1002_2:3_avsq=on:fde=none:nwc=3.0:prag=on:sac=on:sd=2:sgt=32:sos=on:sp=unary_frequency:ss=axioms:i=754:si=on:rtra=on_0 on vampire for (3ds/754Mi)
    % Refutation not found, incomplete strategy
    % ------------------------------
    % Version: Vampire 4.8 HO - Sledgehammer schedules (2023-10-19)
    % Termination reason: Refutation not found, incomplete strategy
    
    
    % Memory used [KB]: 5373
    % Time elapsed: 0.0000 s
    % ------------------------------
    % ------------------------------
    % WARNING: time unlimited strategy and instruction limiting not in place - attemping to translate instructions to time
    % lrs+2_1:1_au=on:cnfonf=off:e2e=on:piset=small_set:sac=on:sd=1:sos=all:ss=axioms:st=5.0:i=810:si=on:rtra=on_0 on vampire for (4ds/810Mi)
    % Refutation not found, incomplete strategy
    % ------------------------------
    % Version: Vampire 4.8 HO - Sledgehammer schedules (2023-10-19)
    % Termination reason: Refutation not found, incomplete strategy
    
    
    % Memory used [KB]: 5373
    % Time elapsed: 0.001 s
    % ------------------------------
    % ------------------------------
    % WARNING: time unlimited strategy and instruction limiting not in place - attemping to translate instructions to time
    % lrs+10_1:1_au=on:av=off:cnfonf=off:sd=1:sos=all:ss=axioms:st=1.5:i=617:si=on:rtra=on_0 on vampire for (3ds/617Mi)
    % Refutation not found, incomplete strategy
    % ------------------------------
    % Version: Vampire 4.8 HO - Sledgehammer schedules (2023-10-19)
    % Termination reason: Refutation not found, incomplete strategy
    
    
    % Memory used [KB]: 895
    % Time elapsed: 0.001 s
    % ------------------------------
    % ------------------------------
    % WARNING: time unlimited strategy and instruction limiting not in place - attemping to translate instructions to time
    % lrs+1010_1:1_e2e=on:ntd=on:nwc=5.0:sac=on:sd=1:sgt=16:spb=units:ss=axioms:i=660:si=on:rtra=on_0 on vampire for (3ds/660Mi)
    % Refutation not found, incomplete strategy
    % ------------------------------
    % Version: Vampire 4.8 HO - Sledgehammer schedules (2023-10-19)
    % Termination reason: Refutation not found, incomplete strategy
    
    
    % Memory used [KB]: 5373
    % Time elapsed: 0.001 s
    % ------------------------------
    % ------------------------------
    % WARNING: time unlimited strategy and instruction limiting not in place - attemping to translate instructions to time
    % lrs+1002_1:1_au=on:bd=off:e2e=on:ins=3:sos=on:ss=axioms:i=707:si=on:rtra=on_0 on vampire for (3ds/707Mi)
    % Refutation not found, incomplete strategy
    % ------------------------------
    % Version: Vampire 4.8 HO - Sledgehammer schedules (2023-10-19)
    % Termination reason: Refutation not found, incomplete strategy
    
    
    % Memory used [KB]: 5373
    % Time elapsed: 0.0000 s
    % ------------------------------
    % ------------------------------
    % WARNING: time unlimited strategy and instruction limiting not in place - attemping to translate instructions to time
    % lrs+1002_1:1_e2e=on:fd=off:fe=off:prag=on:sos=on:i=826:si=on:rtra=on_0 on vampire for (4ds/826Mi)
    % Refutation not found, incomplete strategy
    % ------------------------------
    % Version: Vampire 4.8 HO - Sledgehammer schedules (2023-10-19)
    % Termination reason: Refutation not found, incomplete strategy
    
    
    % Memory used [KB]: 5373
    % Time elapsed: 0.001 s
    % ------------------------------
    % ------------------------------
    % WARNING: time unlimited strategy and instruction limiting not in place - attemping to translate instructions to time
    % lrs+21_1:1_au=on:e2e=on:fd=off:sos=on:sp=unary_frequency:ss=axioms:i=835:si=on:rtra=on_0 on vampire for (4ds/835Mi)
    % Refutation not found, incomplete strategy
    % ------------------------------
    % Version: Vampire 4.8 HO - Sledgehammer schedules (2023-10-19)
    % Termination reason: Refutation not found, incomplete strategy
    
    
    % Memory used [KB]: 5373
    % Time elapsed: 0.001 s
    % ------------------------------
    % ------------------------------
    % WARNING: time unlimited strategy and instruction limiting not in place - attemping to translate instructions to time
    % dis+1010_3:1_acc=on:au=on:chr=on:cnfonf=off:fd=preordered:nwc=10.0:s2a=on:i=705:si=on:rtra=on_0 on vampire for (3ds/705Mi)
    % Refutation found. Thanks to Tanya!
    % SZS status Unsatisfiable for vampire
    % SZS output start Proof for vampire
    1. ! [X0 : t,X2 : t,X1 : t] : ((mul_8e @ (mul_8e @ X2 @ X2) @ X1) = (mul_8e @ X1 @ X2)) [input]
    2. ~! [X1 : t,X2 : t] : ((mul_8e @ X1 @ X2) = (mul_8e @ X2 @ X1)) [input]
    4. ! [X1 : t,X2 : t] : ((mul_8e @ X2 @ X1) = (mul_8e @ (mul_8e @ X1 @ X1) @ X2)) [rectify 1]
    5. ! [X1 : t,X2 : t] : ((mul_8e @ X2 @ X1) = (mul_8e @ (mul_8e @ X1 @ X1) @ X2)) [fool elimination 4]
    6. ~! [X0 : t,X1 : t] : ((mul_8e @ X0 @ X1) = (mul_8e @ X1 @ X0)) [rectify 2]
    7. ~! [X0 : t,X1 : t] : ((mul_8e @ X0 @ X1) = (mul_8e @ X1 @ X0)) [fool elimination 6]
    8. ! [X0 : t,X1 : t] : ((mul_8e @ (mul_8e @ X0 @ X0) @ X1) = (mul_8e @ X1 @ X0)) [rectify 5]
    9. ? [X0 : t,X1 : t] : ((mul_8e @ X0 @ X1) != (mul_8e @ X1 @ X0)) [ennf transformation 7]
    10. ? [X0 : t,X1 : t] : ((mul_8e @ X0 @ X1) != (mul_8e @ X1 @ X0)) => ((mul_8e @ sK0 @ sK1) != (mul_8e @ sK1 @ sK0)) [choice axiom]
    11. ((mul_8e @ sK0 @ sK1) != (mul_8e @ sK1 @ sK0)) [skolemisation 9,10]
    12. ((mul_8e @ sK0 @ sK1) != (mul_8e @ sK1 @ sK0)) [cnf transformation 11]
    13. ((mul_8e @ (mul_8e @ X0 @ X0) @ X1) = (mul_8e @ X1 @ X0)) [cnf transformation 8]
    15. 1 <=> ((mul_8e @ sK0 @ sK1) = (mul_8e @ sK1 @ sK0)) [avatar definition]
    17. ((mul_8e @ sK0 @ sK1) != (mul_8e @ sK1 @ sK0)) <- (~1) [avatar component clause 15]
    18. ~1 [avatar split clause 12,15]
    24. ((mul_8e @ (mul_8e @ (mul_8e @ X0 @ X0) @ X0) @ X1) = (mul_8e @ X1 @ (mul_8e @ X0 @ X0))) [superposition 13,13]
    25. ((mul_8e @ (mul_8e @ X0 @ X0) @ X1) = (mul_8e @ X1 @ (mul_8e @ X0 @ X0))) [forward demodulation 24,13]
    26. ((mul_8e @ X1 @ X0) = (mul_8e @ X1 @ (mul_8e @ X0 @ X0))) [forward demodulation 25,13]
    29. ((mul_8e @ (mul_8e @ X0 @ X0) @ X1) = (mul_8e @ (mul_8e @ X1 @ X1) @ X0)) [superposition 26,13]
    32. ((mul_8e @ X0 @ X1) = (mul_8e @ (mul_8e @ X0 @ X0) @ X1)) [forward demodulation 29,13]
    43. ((mul_8e @ X0 @ X1) = (mul_8e @ X1 @ X0)) [superposition 32,13]
    67. ((mul_8e @ sK0 @ sK1) != (mul_8e @ sK0 @ sK1)) <- (~1) [superposition 17,43]
    77. $false <- (~1) [trivial inequality removal 67]
    78. 1 [avatar contradiction clause 77]
    79. $false [avatar sat refutation 18,78]
    % SZS output end Proof for vampire
    % ------------------------------
    % Version: Vampire 4.8 HO - Sledgehammer schedules (2023-10-19)
    % Termination reason: Refutation
    
    % Memory used [KB]: 5500
    % Time elapsed: 0.002 s
    % ------------------------------
    % ------------------------------
    % Success in time 0.039 s
    

```python
! cat /tmp/vampire.p
```

    % TPTP file generated by Knuckledragger
    thf(t_type, type, t : $tType ).
    % Declarations
    thf(mul_decl, type, mul_8e : t > t > t).
    % Axioms and assertions
    thf(ax_0, axiom, (![Z_90:t, Y_91:t, X_92:t] : ((mul_8e @ (mul_8e @ X_92 @ X_92) @ Y_91) = (mul_8e @ Y_91 @ X_92)))).
    thf(ax_1, axiom, ~((![Y_91:t, X_92:t] : ((mul_8e @ X_92 @ Y_91) = (mul_8e @ Y_91 @ X_92))))).

```python
s = solvers.EProverTHFSolver()
s.add(smt.ForAll([x,y,z], (x * x) * y == y * x))
s.add(smt.Not(smt.ForAll([x,y], x * y == y * x)))
s.set("timeout", 1000)
print(s.check())
print(s.proof().decode())
```

    unsat
    # Preprocessing class: HSSSSMSSSSSNFFN.
    # Scheduled 4 strats onto 8 cores with 2 seconds (16 total)
    # Starting new_ho_10 with 10s (5) cores
    # Starting ho_unfolding_6 with 2s (1) cores
    # Starting sh4l with 2s (1) cores
    # Starting ehoh_best_nonlift_rwall with 2s (1) cores
    # sh4l with pid 2515392 completed with status 0
    # Result found by sh4l
    # Preprocessing class: HSSSSMSSSSSNFFN.
    # Scheduled 4 strats onto 8 cores with 2 seconds (16 total)
    # Starting new_ho_10 with 10s (5) cores
    # Starting ho_unfolding_6 with 2s (1) cores
    # Starting sh4l with 2s (1) cores
    # No SInE strategy applied
    # Search class: HUUPF-FFSF22-SFFFFFNN
    # Scheduled 1 strats onto 1 cores with 2 seconds (2 total)
    # Starting new_ho_10 with 2s (1) cores
    # new_ho_10 with pid 2515394 completed with status 0
    # Result found by new_ho_10
    # Preprocessing class: HSSSSMSSSSSNFFN.
    # Scheduled 4 strats onto 8 cores with 2 seconds (16 total)
    # Starting new_ho_10 with 10s (5) cores
    # Starting ho_unfolding_6 with 2s (1) cores
    # Starting sh4l with 2s (1) cores
    # No SInE strategy applied
    # Search class: HUUPF-FFSF22-SFFFFFNN
    # Scheduled 1 strats onto 1 cores with 2 seconds (2 total)
    # Starting new_ho_10 with 2s (1) cores
    # Initializing proof state
    # Scanning for AC axioms
    #
    #thf(i_0_4, plain, ((mul_8e @ esk1_0 @ esk2_0)!=(mul_8e @ esk2_0 @ esk1_0))).
    #
    #thf(i_0_3, plain, ![X2:t, X1:t]:(((mul_8e @ (mul_8e @ X1 @ X1) @ X2)=(mul_8e @ X2 @ X1)))).
    # Presaturation interreduction done
    #
    #thf(i_0_4, plain, ((mul_8e @ esk1_0 @ esk2_0)!=(mul_8e @ esk2_0 @ esk1_0))).
    #
    #thf(i_0_3, plain, ![X2:t, X1:t]:(((mul_8e @ (mul_8e @ X1 @ X1) @ X2)=(mul_8e @ X2 @ X1)))).
    #
    #thf(i_0_5, plain, ![X2:t, X1:t]:(((mul_8e @ X2 @ (mul_8e @ X1 @ X1))=(mul_8e @ X2 @ X1)))).
    ## mul_8e is commutative
    # AC handling enabled dynamically
    
    #thf(i_0_6, plain, ![X1:t, X2:t]:(((mul_8e @ X2 @ X1)=(mul_8e @ X1 @ X2)))).
    
    # Proof found!
    # SZS status Unsatisfiable
    

```python
! cat /tmp/eprover.p
```

    % TPTP file generated by Knuckledragger
    thf(t_type, type, t : $tType ).
    % Declarations
    thf(mul_decl, type, mul_8e : t > t > t).
    % Axioms and assertions
    thf(ax_0, axiom, (![Z_90:t, Y_91:t, X_92:t] : ((mul_8e @ (mul_8e @ X_92 @ X_92) @ Y_91) = (mul_8e @ Y_91 @ X_92)))).
    thf(ax_1, axiom, ~((![Y_91:t, X_92:t] : ((mul_8e @ X_92 @ Y_91) = (mul_8e @ Y_91 @ X_92))))).

# What's Next

It seems there is already code to enumerate possible axioms made of a multiplication operation. Should do that.
