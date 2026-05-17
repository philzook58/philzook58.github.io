---
title: Reading Proof Objects and Completed Rewrite Systems from eprover into Knuckledragger
date : 2026-05-17
---

Automated reasoning is fun.

E-prover <https://github.com/eprover/eprover> is a pure C [superposition](https://en.wikipedia.org/wiki/Superposition_calculus) theorem prover. It's quite nice. [Superposition](https://www.tcs.ifi.lmu.de/teaching/courses-ws-2024-25/automated-theorem-proving/slides12-superposition.pdf) provers has strengths and weaknesses that complement those of SMT solvers.

I was poking around at exporting problems from z3py by printing cnf formulas and reading back in the results using scryerpy, some light bindings I've made for [scryer prolog](https://github.com/mthom/scryer-prolog), a embeddable rust prolog I've made available at `pip install kdrag-scryer` <https://github.com/philzook58/scryerpy> . This paper pointed out that post processing TPTP stuff via prolog is nice <https://arxiv.org/abs/2602.18844> . It is kind of overkill, but it works.

# Completion via Eprover

As time has gone on, I've come to understand some of the knobs. It is particularly interesting to me to `--print-saturated` as this can be used an off the shelf [knuth bendix completion](https://en.wikipedia.org/wiki/Knuth%E2%80%93Bendix_completion_algorithm) engine.

The equations can be printed in oriented form using the recently added option `--print-oriented-eqlits-as-rules`. You can also pick the weights `--order-weights`, precedence of symbols `--precedence` , and LPO vs KBO term ordering `--term-ordering` via command line options.

Knuth bendix completion can be used as a egraph engine <https://www.philipzucker.com/egraph2024_talk/> or egraph modulo theory prototyping engine, so that's pretty intriguing too. The completion of ground equations _is_ an egraph. Throwing some rules on top of your ground equations with the right ordering can sometimes get you an egraph modulo that theory. eprover has has some special smarts for AC. I don't know that anyone has thoroughly investigated using this.

Here is the classic example of completing the rewrites describing a group

```python
%%file /tmp/group.p

cnf(mul_assoc, axiom, mul(X, mul(Y,Z)) = mul(mul(X,Y), Z)).
cnf(mul_id_left, axiom, mul(id,X) = X).
cnf(mul_inv, axiom, mul(inv(X), X) = id).
```

    Writing /tmp/group.p

With the following command line, we print the completed saturated set as oriented rewrites

```python
! eprover-ho --auto --silent --print-saturated --print-oriented-eqlits-as-rules /tmp/group.p
```

    % Preprocessing class: FSSSSMSSSSSNFFN.
    % Configuration: G-E--_302_C18_F1_URBAN_RG_S04BN
    % (lift_lambdas = 1, lambda_to_forall = 1,unroll_only_formulas = 1, sine = Auto)
    % No SInE strategy applied
    % Search class: FUUPS-FFSF21-SFFFFFNN
    % Configuration: G-E--_208_C12_00_F1_SE_CS_PI_SP_PS_S5PRR_RG_S04AN
    % Presaturation interreduction done
    
    % No proof found!
    % SZS status Satisfiable
    % Processed positive unit clauses:
    cnf(i_0_5, plain, (mul(id,X1)->X1)).
    cnf(i_0_6, plain, (mul(inv(X1),X1)->id)).
    cnf(i_0_4, plain, (mul(mul(X1,X2),X3)->mul(X1,mul(X2,X3)))).
    cnf(i_0_8, plain, (mul(inv(X1),mul(X1,X2))->X2)).
    cnf(i_0_23, plain, (inv(id)->id)).
    cnf(i_0_29, plain, (inv(inv(X1))->X1)).
    cnf(i_0_12, plain, (mul(X1,id)->X1)).
    cnf(i_0_32, plain, (mul(X1,inv(X1))->id)).
    cnf(i_0_33, plain, (mul(X1,mul(inv(X1),X2))->X2)).
    cnf(i_0_75, plain, (inv(mul(X1,X2))->mul(inv(X2),inv(X1)))).
    
    % Processed negative unit clauses:
    
    % Processed non-unit clauses:
    
    % Unprocessed positive unit clauses:
    
    % Unprocessed negative unit clauses:
    
    % Unprocessed non-unit clauses:
    
    
It is jumping through hoops, but the full loop from z3py expressions into a CNF file, and then parsing back using scyrer prolog and turning back into z3py expressions is in this code <https://github.com/philzook58/knuckledragger/blob/101dbcef06fbcc214b90615be752ee070b23b1f0/src/kdrag/solvers/scryer.py> .

I used the operator precedences file from leancop as prelude, as prolog by default does not parse some tptp operators.

Scryer is kind of overkill for this, but if it works it works. I may want to do some light elabrational theorem proving inside scryer to help me reconstruct certificates.

One tricky bit is coming from untyped prolog back into typed z3. I can store all the funcdecls, which helps a lot with the type inference problem. I did kind of super lite bidirectional typing in the form of an optional `sort=None` keyword paramater for what sort is expected. This helps propagate sort information downwards. Generally speaking, this was simple, but a more declarative or constraint producing approach will be able to infer types for more expressions.

```python
from kdrag.all import *
import kdrag.solvers.scryer as scryer_
import scryer 
import kdrag.printers.tptp as tptp
import subprocess

tptp_prelude = """
% TPTP syntax
:- op(1130, xfy, <~>).  % negated equivalence
:- op(1110, xfy, <=).   % implication
:- op(1100, xfy, '|').  % disjunction
:- op(1100, xfy, '~|'). % negated disjunction
:- op(1000, xfy, &).    % conjunction
:- op(1000, xfy, ~&).   % negated conjunction
:- op( 500, fy, !).     % universal quantifier
:- op( 500, fy, ?).     % existential quantifier
:- op( 400, xfx, =).    % equality
:- op( 300, xf, !).     % negated equality (for !=) Very annoying
:- op( 299, fx, $).     % for $true/$false
"""

def complete(eqs : list[smt.BoolRef]):
    res = subprocess.run(["eprover-ho", "--auto", "--soft-cpu-limit=1", "--silent", "--print-saturated"], capture_output=True, input=tptp.cnf_file(eqs,nnf=True).encode())
    if len(res.stderr) > 0:
        raise Exception(res.stderr.decode())
    m = scryer.Machine()
    m.load_module_string("mymodule", tptp_prelude + res.stdout.decode())
    rules = []
    decls = {d.name(): d for d in kd.utils.decls(smt.And(eqs))}
    for res in m.query("cnf(Id, Status, Formula)."):
        rules.append(scryer_.from_scryer(res["Formula"], decls))
    return rules


T = smt.DeclareSort("AbstractGroup")
x,y,z = smt.Consts("x y z", T)
e = smt.Const("e", T)
inv = smt.Function("inv", T, T)
mul = smt.Function("mul", T, T, T)
kd.notation.mul.register(T, mul)
kd.notation.invert.register(T, inv)
eqs = [
    axiom(ForAll([x], e * x == x)),
    axiom(ForAll([x], inv(x) * x == e)),
    axiom(ForAll([x,y,z], (x * y) * z == x * (y * z))),
]

complete([eq.thm for eq in eqs])



```

    [([_A], mul(e, _A) == _A),
     ([_A], mul(inv(_A), _A) == e),
     ([_A, _B, _C], mul(mul(_A, _B), _C) == mul(_A, mul(_B, _C))),
     ([_A, _B], mul(inv(_A), mul(_A, _B)) == _B),
     ([], inv(e) == e),
     ([_A], inv(inv(_A)) == _A),
     ([_A], mul(_A, e) == _A),
     ([_A], mul(_A, inv(_A)) == e),
     ([_A, _B], mul(_A, mul(inv(_A), _B)) == _B),
     ([_A, _B], inv(mul(_A, _B)) == mul(inv(_B), inv(_A)))]

Note this is outrageuosly faster than my homegrown KB in python <https://www.philipzucker.com/knuth_bendix_knuck/> . This problem is baby shit, but even for this my solver took about 1s after I tuned quite a bit. eprover eats it instantaneously. Probably all the time is in making a subprocess etc.

# Replaying Proof Objects

In Knuckederagger, I maintain the right to just trust eprover as an oracle.

But it is cool to reconstruct the proof object in order to reduce reliance on trust in my tptp serializers and deserializers. I try to code defensively, but they are definitely buggy. There is probably also some semantics gap between what even in principle what TPTP thinks is true and SMT/z3. I'd also like to work towards converting these proofs (and mine) into exportable metamath 0. Graham's been firing off on that <https://grahamlk.me/Aufbau/#hilbert>

Here is a problem proving the identity right from the left identity law for a group.

```python
%%file /tmp/group.p

cnf(mul_assoc, axiom, mul(X, mul(Y,Z)) = mul(mul(X,Y), Z)).
cnf(mul_id_left, axiom, mul(id,X) = X).
cnf(mul_inv, axiom, mul(inv(X), X) = id).
cnf(goal, negated_conjecture, mul(x, id) = x).
```

    Overwriting /tmp/group.p

It is similar to the above. `--proof-object` outputs a proof object.

The proof object is basically a listing of intermediate provable formulas. The inference rules in the fourth field don't seem worth trying to take much out of except just the references to the previous theorems.

```python
! eprover-ho --auto --silent --proof-object /tmp/group.p
```

    % Preprocessing class: FSSSSMSSSSSNFFN.
    % Configuration: G-E--_302_C18_F1_URBAN_RG_S04BN
    % (lift_lambdas = 1, lambda_to_forall = 1,unroll_only_formulas = 1, sine = Auto)
    % No SInE strategy applied
    % Search class: FUUPS-FFSF21-SFFFFFNN
    % Configuration: G-E--_208_C12_00_F1_SE_CS_PI_SP_PS_S5PRR_RG_S04AN
    % Presaturation interreduction done
    
    % No proof found!
    % SZS status Satisfiable
    % SZS output start Saturation
    cnf(mul_assoc, axiom, (mul(X1,mul(X2,X3))=mul(mul(X1,X2),X3)), file('/tmp/group.p', mul_assoc)).
    cnf(mul_inv, axiom, (mul(inv(X1),X1)=id), file('/tmp/group.p', mul_inv)).
    cnf(mul_id_left, axiom, (mul(id,X1)=X1), file('/tmp/group.p', mul_id_left)).
    cnf(c_0_3, axiom, (mul(X1,mul(X2,X3))=mul(mul(X1,X2),X3)), mul_assoc, ['final']).
    cnf(c_0_4, axiom, (mul(inv(X1),X1)=id), mul_inv, ['final']).
    cnf(c_0_5, axiom, (mul(id,X1)=X1), mul_id_left, ['final']).
    cnf(c_0_6, plain, (mul(inv(X1),mul(X1,X2))=X2), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_3, c_0_4]), c_0_5]), ['final']).
    cnf(c_0_7, plain, (mul(inv(inv(X1)),id)=X1), inference(spm,[status(thm)],[c_0_6, c_0_4])).
    cnf(c_0_8, plain, (mul(inv(inv(inv(X1))),X1)=id), inference(spm,[status(thm)],[c_0_6, c_0_7])).
    cnf(c_0_9, plain, (inv(inv(X1))=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_6, c_0_8]), c_0_7]), ['final']).
    cnf(c_0_10, plain, (mul(X1,inv(X1))=id), inference(spm,[status(thm)],[c_0_4, c_0_9]), ['final']).
    cnf(c_0_11, plain, (mul(X1,mul(X2,inv(mul(X1,X2))))=id), inference(spm,[status(thm)],[c_0_3, c_0_10])).
    cnf(c_0_12, plain, (mul(X1,id)=X1), inference(rw,[status(thm)],[c_0_7, c_0_9]), ['final']).
    cnf(c_0_13, plain, (mul(inv(id),X1)=X1), inference(spm,[status(thm)],[c_0_6, c_0_5])).
    cnf(c_0_14, plain, (mul(X1,inv(mul(X2,X1)))=inv(X2)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_6, c_0_11]), c_0_12])).
    cnf(c_0_15, plain, (mul(inv(inv(id)),X1)=X1), inference(spm,[status(thm)],[c_0_6, c_0_13])).
    cnf(c_0_16, plain, (inv(mul(X1,X2))=mul(inv(X2),inv(X1))), inference(spm,[status(thm)],[c_0_6, c_0_14]), ['final']).
    cnf(c_0_17, plain, (mul(X1,mul(inv(X1),X2))=X2), inference(spm,[status(thm)],[c_0_6, c_0_9]), ['final']).
    cnf(c_0_18, plain, (inv(id)=id), inference(spm,[status(thm)],[c_0_4, c_0_15]), ['final']).
    % SZS output end Saturation

So really the proof object from my perspective is just a DAG of formulas which point back to previous nodes.

Reconstructing this take a few moments thought because the goal really has a different status than the `by` information (being currently unproven). What I need to do is weaken the incoming axioms to `goal |= ax` or  really `|= goal -> ax`. Then I can have a reflexive proof object for the goal as `goal |= goal`. As a final step once I have `goal |= false`, I can turn this into `|= not goal`

It is important to skolemize yourself before handing it off to the prover. I think there is some format for getting information about how the prover skolemized, but skoemization isn't a theorem, it's a equisatisfiability / conservative extension thing.

`|= exists a, foo(a)` does not imply by logical reasoning that `|= foo(biz)`. It's kind of a meta move that you can create a new constant and assert as a new axiom that `foo(biz)` holds. This is different from `|= p /\ q` actually can derive `|= p` without any meta playing or `|= forall a, foo(a)` can derive `|= foo(bar)` without any metaplay.

```python
def eprove(goal : smt.BoolRef, by : list[kd.Proof] =[]) -> kd.Proof:
    prob = [pf.thm for pf in by] + [goal]
    res = subprocess.run(["eprover-ho", "--auto", "--soft-cpu-limit=1", "--silent", "--proof-object"], capture_output=True, input=tptp.cnf_file(prob,nnf=True).encode())
    if len(res.stderr) > 0:
        raise Exception(res.stderr.decode())
    m = scryer.Machine()
    m.load_module_string("mymodule", tptp_prelude + res.stdout.decode())
    #print(res.stdout.decode())
    decls = {d.name(): d for d in kd.utils.decls(smt.And(prob))}
    proof = {scryer.Term.Integer(i) : prove(Implies(goal, pf.thm),by=[pf]) for i,pf in enumerate(by)}
    proof[scryer.Term.Integer(len(by)+1)] = prove(Implies(goal,goal))
    for step in m.query("cnf(Id, Status, Formula, Reason) ; cnf(Id, Status, Formula, Reason, ['proof']) ."):
        if step["Id"] in proof:
            continue
        vs, body = scryer_.from_scryer(step["Formula"], decls)
        if len(vs) == 0:
            thm = body
        else:
            thm = ForAll(vs, body)
        by1 = [proof[r] for r in scryer_.subterms(step["Reason"]) if r in proof]
        proof[step["Id"]] = prove(Implies(goal, thm), by=by1)
    return prove(Not(goal), by=list(proof.values()))

eprove(x * inv(x)!= e, by=eqs) 

```

&#x22A8;Not(mul(x, inv(x)) != e)

If I give the same problem to z3 raw, it does not solve, so we are getting some delta here. The incomplete e-matching is not sufficient for this problem. It needs the clue terms in the eprover proof trace or a more fine grained manual proof.

```python
prove(x * inv(x) == e, by=eqs)
```

    ---------------------------------------------------------------------------

    LemmaError                                Traceback (most recent call last)

    File ~/vibe_coding/knuck_anal/knuckledragger/src/kdrag/tactics.py:315, in prove(thm, fixes, assumes, by, admit, timeout, dump, solver, contracts, unfold)
        314 try:
    --> 315     pf = kd.kernel.prove(
        316         thm, by=by_list, timeout=timeout, dump=dump, solver=solver, admit=admit
        317     )
        318     if fixes:


    File ~/vibe_coding/knuck_anal/knuckledragger/src/kdrag/kernel.py:181, in prove(thm, by, admit, timeout, dump, solver, fvs)
        180         smtfile.write(s.sexpr())
    --> 181     raise LemmaError("prove", thm, res, smtfile.name)
        182 else:


    LemmaError: ('prove', mul(x, inv(x)) == e, unknown, '/tmp/tmp7u4jhr_k.smt2')

    
    During handling of the above exception, another exception occurred:


    TimeoutError                              Traceback (most recent call last)

    Cell In[26], line 1
    ----> 1 prove(x * inv(x) == e, by=eqs)


    File ~/vibe_coding/knuck_anal/knuckledragger/src/kdrag/tactics.py:324, in prove(thm, fixes, assumes, by, admit, timeout, dump, solver, contracts, unfold)
        322 except kd.kernel.LemmaError as e:
        323     if time.perf_counter() - start_time > timeout / 1000:
    --> 324         raise TimeoutError(
        325             "Timeout. Maybe you have given `prove` too many or not enough lemmas?"
        326         )
        327     elif isinstance(thm, smt.QuantifierRef):
        328         while isinstance(thm, smt.QuantifierRef) and thm.is_forall():


    TimeoutError: Timeout. Maybe you have given `prove` too many or not enough lemmas?

# Bits and Bobbles

Vampire and eprover are two top tier automated theorem provers.

Isabelle's sledgehammer is crazy good. I should try to understand it better. A funny thing is basically you need a native automated theorem prover in order to digest proofs from others systems. They'll only ever really give you breadcrumbs. I may want to use scryer to make some leantap or leancop variants to assist proof reconstruction <https://formal.kastel.kit.edu/beckert/leantap/> <https://jens-otten.de/tutorial_tableaux19/>

I also think it's interesting to explore proof by saturation / inductionless induction in eprover. The mere fact of saturation proves consistency of a statement and therefore it is true in the initial term model or something like that. I dunno how I'd even replay those proofs. I think eprover could be used for unbounded bitvector proofs in the manner.

sick <https://vprover.github.io/vampireGuide/> vampire's getting good docs. Getting out vampire proof objects should be quite similar. Vampire seems less straightforward to understand it's saturated objects.

Someone is making rust bindings to vampire <https://docs.rs/vampire-sys/latest/vampire_sys/> ? Hellllllo nurse.

I've been playing with eprover again recently because of my increased understanding of the concepts behind it's command line knobs and the new `--print-eqlists-as-oriented-rules` flag.

Knuth bendix and e-graphs are intimately related.

In this vampire for agda paper <https://arxiv.org/abs/2602.18844> , they suggest that one should use a prolog to read out the proof objects. Indeed, the TPTP format is prolog syntax, which is useful for those using prolog and non-useful for everyone else.

I made some simple python bindings to scryer-prolog, a rust based prolog. My impression is that scryer is conceptually tighter that swi, but swi is much more feature rich. swi already has python bindings in the form of pyswip <https://github.com/yuce/pyswip> and `janus-swi` package. However, it's not quite self contained enough to install these as python packages. You need to install swi separately to get these to work. As stupid as that sounds, that is important to me. Giants stumbling on pebbles.

I also do not like how janus is set up. I really wanted it to be my solution. It clearly to my mind has the python access of prolog as a second class concern. My big gripe is basically how shipping terms back over with variables in them is a no go. You need to ground them first on the prolog side. For my preferences, prolog is the second class citizen. I want prolog for specialized solver-like situations and do not consider it a good general purpose programming language replacement. This is partially due to my relative familiarity, but not entirely.

No one has a gun to my head for many of the things I do, so the approach needs to spark joy in me.

In a strange way, despite the CNF format seeming so primitive, it is the better one to be using for some purposes. It is "closer to the metal" in some respects and kind of more constructive. The very helpful skolemization and normal form routines make getting a proof object out more confusing.

I have found e-prover's knobs to be less confusing if I am not after refutational theorem proving.

```python
%%file /tmp/path.p

cnf(edge_path, axiom, path(X,Y) | ~edge(X,Y)).
cnf(path_trans, axiom, path(X,Z) | ~edge(X,Y) | ~path(Y,Z)).
cnf(edge12, axiom, edge(a,b)).
cnf(edge23, axiom, edge(b,c)).
cnf(edge23, axiom, edge(c,d)).
fof(query, conjecture, ?[X,Y] : path(X,Y)).


```

    Overwriting /tmp/path.p

```python
! eprover-ho /tmp/path.p --auto --silent --answers=5 --conjectures-are-questions
```

    % Preprocessing class: FSSSSMSSSSSNFFN.
    % Configuration: G-E--_302_C18_F1_URBAN_RG_S04BN
    % (lift_lambdas = 1, lambda_to_forall = 1,unroll_only_formulas = 1, sine = Auto)
    % No SInE strategy applied
    % Search class: FHUNF-FFSS22-SFFFFFNN
    % partial match(1): FGUNF-FFSS22-SFFFFFNN
    % Configuration: SAT001_MinMin_p005000_rr_RG
    % Presaturation interreduction done
    % SZS status Theorem
    % SZS answers Tuple [[c, d]|_]
    % SZS answers Tuple [[b, c]|_]
    % SZS answers Tuple [[a, b]|_]
    % SZS answers Tuple [[a, c]|_]
    % SZS answers Tuple [[b, d]|_]
    
    % Proof found!

```python
%%file /tmp/path.p

cnf(edge_path, axiom, path(X,Y) | ~edge(X,Y)).
cnf(path_trans, axiom, path(X,Z) | ~edge(X,Y) | ~path(Y,Z)).
cnf(edge12, axiom, edge(a,b)).
cnf(edge23, axiom, edge(b,c)).
cnf(edge23, axiom, edge(c,d)).
```

    Overwriting /tmp/path.p

a little sad from a datalog perspective, but it ain't wrong. I haven't really figured out how to

```python
! eprover-ho --print-saturated  --silent --auto /tmp/path.p
```

    % Preprocessing class: FSSSSMSSSSSNFFN.
    % Configuration: G-E--_302_C18_F1_URBAN_RG_S04BN
    % (lift_lambdas = 1, lambda_to_forall = 1,unroll_only_formulas = 1, sine = Auto)
    % No SInE strategy applied
    % Search class: FHUNF-FFSS00-SFFFFFNN
    % Configuration: SAT001_MinMin_p005000_rr_RG
    % Presaturation interreduction done
    
    % No proof found!
    % SZS status Satisfiable
    % Processed positive unit clauses:
    cnf(i_0_8, plain, (edge(a,b))).
    cnf(i_0_9, plain, (edge(b,c))).
    cnf(i_0_10, plain, (edge(c,d))).
    
    % Processed negative unit clauses:
    
    % Processed non-unit clauses:
    cnf(i_0_6, plain, (path(X1,X2)|~edge(X1,X2))).
    cnf(i_0_7, plain, (path(X1,X2)|~edge(X1,X3)|~path(X3,X2))).
    cnf(i_0_11, plain, (path(c,X1)|~path(d,X1))).
    cnf(i_0_12, plain, (path(b,X1)|~path(c,X1))).
    cnf(i_0_13, plain, (path(a,X1)|~path(b,X1))).
    cnf(i_0_14, plain, (path(c,X1)|~edge(d,X1))).
    cnf(i_0_15, plain, (path(b,X1)|~edge(c,X1))).
    cnf(i_0_16, plain, (path(b,X1)|~edge(d,X1))).
    
    % Unprocessed positive unit clauses:
    
    % Unprocessed negative unit clauses:
    
    % Unprocessed non-unit clauses:
    
    

```python
def question(query, axioms):
    
```

```python
def question_answer(query, axioms): ...
    

def to_prolog(vs : list[smt.ExprRef], e : smt.ExprRef):
    if smt.is_eq(e):
        return f"{to_prolog(vs,e.arg(0))} = {to_prolog(vs, e.arg(1))}"
    elif smt.is_const(e):
        if
        return e.decl().name()
    elif smt.is_app(e):
        return f"{e.decl().name()}({', '.join(to_prolog(a) for a in e.args())})"


def prolog(query, rules):

```

```python
from kdrag.all import *

T = DeclareSort("T")
mul = Function("mul", T, T, T)
zero = Const("zero", T)
id = Const("id", T)
x,y,z = Consts("x y z", T)
import kdrag.printers.tptp as tptp

tptp.expr_to_cnf(ForAll([x], mul(zero,x) == zero))
dir(tptp)
tptp.expr_to_tptp(ForAll([x], mul(zero,x) == zero), format="cnf")
#help(tptp.expr_to_tptp)

e = ForAll([x], mul(zero,x) == zero)
Tactic("nnf")(e)
Tactic("tseitin-cnf")(e)
#With(Tactic("nnf"), skolem=True)(e)

def cnf_file(axioms, nnf=False):
    if nnf:
        g = Goal()
        g.add(axioms)
        axioms = Tactic("nnf")(g)[0]
    res = []
    for i, axiom in enumerate(axioms):
        res.append(f"cnf({i},axiom,{tptp.expr_to_cnf(axiom)}).")
    return "\n".join(res)

axs = [
    ForAll([x,y,z], mul(x, mul(y,z)) == mul(mul(x,y), z)),
    ForAll([x], mul(id,x) == x),
    ForAll([x], mul(x,id) == x),
    ForAll([x,y], mul(x,y) == mul(y,x)),
    mul(id,x) != x
]


g = Goal()
g.add(axs)
list(Tactic("nnf")(g)[0])
print(cnf_file(axs, nnf=True))
tptp_prelude = """
% TPTP syntax
:- op(1130, xfy, <~>).  % negated equivalence
:- op(1110, xfy, <=).   % implication
:- op(1100, xfy, '|').  % disjunction
:- op(1100, xfy, '~|'). % negated disjunction
:- op(1000, xfy, &).    % conjunction
:- op(1000, xfy, ~&).   % negated conjunction
:- op( 500, fy, !).     % universal quantifier
:- op( 500, fy, ?).     % existential quantifier
:- op( 400, xfx, =).    % equality
:- op( 300, xf, !).     % negated equality (for !=) Very annoying
:- op( 299, fx, $).     % for $true/$false
"""
import subprocess
def _from_scryer(term : scryer.Term, decls : dict[str, smt.FuncDeclRef], vars, sort=None):
    match term:
        case scryer.Term.Var(name):
            if name in vars:
                if sort is not None:
                    assert vars[name].sort() == sort
                return vars[name]
            else:
                assert sort is not None, f"Variable sort is not inferrable {name}"
                v = smt.Const(name, sort)
                vars[name] = v
                return v
        case scryer.Term.Atom(name):
            if name in decls:
                return decls[name]()
            else:
                assert sort is not None
                return smt.Const(name, sort)
        case scryer.Term.Compound("=", [scryer.Term.Compound("!", [lhs]), rhs]):
            lhs = _from_scryer(lhs, decls, vars)
            return lhs != _from_scryer(rhs, decls, vars, sort=lhs.sort())
        case scryer.Term.Compound("$", [t]):
            match t:
                case scryer.Term.Atom("true"):
                    return smt.BoolVal(True)
                case scryer.Term.Atom("false"):
                    return smt.BoolVal(False)
                case _:
                    raise Exception(f"Untranslatable term: {term}")
        case scryer.Term.Compound(name, args):
            if name == "=":
                assert len(args) == 2
                lhs = _from_scryer(args[0], decls, vars)
                return lhs == _from_scryer(args[1], decls, vars, sort=lhs.sort())
            if name in decls:
                decl = decls[name]
                args = [_from_scryer(arg, decls, vars, sort=decl.domain(i)) for i, arg in enumerate(args)]
                return decl(*args)
        case _:
            raise Exception(f"Untranslatable constructor: {term}")
        #case scryer.Term.List(values):

def from_scryer(term, decls):
    vars = {}
    res = _from_scryer(term, decls, vars)
    if len(vars) == 0:
        return res
    else:
        return smt.ForAll(list(vars.values()), res)



def in_term(term, tags):
    todo = [term]
    res = set()
    while todo:
        term = todo.pop()
        if term in tags:
            res.add(term)
        if isinstance(term, scryer.Term.Compound):
            todo.extend(term.args)
        elif isinstance(term, scryer.Term.List):
            todo.extend(term.values)
    return res

def eprover(axs):
    res = subprocess.run(["eprover-ho", "--auto", "--cpu-limit=1", "--silent", "--proof-object"], capture_output=True, input=cnf_file(axs,nnf=True).encode())
    if len(res.stderr) > 0:
        raise Exception(res.stderr.decode())
    output = res.stdout.decode()
    if "SZS status Unsatisfiable" in output:
        m = scryer.Machine()
        m.load_module_string("proof", tptp_prelude + output)
        proof = m.query("cnf(Id, Status, Formula, Reason) ; cnf(Id, Status, Formula, Reason, ['proof']) .")
        tags = set()
        res = []
        decls = {d.name(): d for d in kd.utils.decls(smt.And(axs))}
        print(decls)
        for step in proof:
            res.append((step["Id"], from_scryer(step["Formula"], decls) , in_term(step["Reason"], tags)))#, str(step["Formula"])))
            #print(tags)
            tags.add(step["Id"])
        return res
import pprint
pprint.pprint(eprover(axs))
```

```python
# a more iterative fixpoint thing
    from_scryer(term0, decls):
    terms = [(None, t) for t in subterms(term0)]
    todo = []
    trans = {}
    while True:
        for sort, term in terms:
            if term in trans:
                continue
            match term:
                case scryer.Term.Atom(name):
                    if name in decls:
                        trans[term] = decls[name]()
                    elif sort is not None:
                        trans[term] = smt.Const(name, sort)
                    else:
                        todo.append((None, term))
                case scryer.Term.Compound("=", [scryer.Term.Compound("!", [lhs]), rhs]):
                    if (None, lhs) in trans and (None


        terms = todo
    return trans[term0]

```

<https://docs.rs/vampire-prover/latest/vampire_prover/> whoa

```python
%%file /tmp/test.p

%--------------------------------------------------------------------------
% File     : SYN075-1 : TPTP v9.2.1. Released v1.0.0.
% Domain   : Syntactic
% Problem  : Pelletier Problem 52
% Version  : Especial.
% English  :

% Refs     : [Pel86] Pelletier (1986), Seventy-five Problems for Testing Au
% Source   : [Pel86]
% Names    : Pelletier 52 [Pel86]

% Status   : Unsatisfiable
% Rating   : 0.05 v9.0.0, 0.10 v8.1.0, 0.00 v7.5.0, 0.05 v7.4.0, 0.06 v7.3.0, 0.08 v7.1.0, 0.00 v7.0.0, 0.13 v6.4.0, 0.07 v6.3.0, 0.09 v6.2.0, 0.00 v6.1.0, 0.07 v6.0.0, 0.00 v5.5.0, 0.20 v5.3.0, 0.22 v5.2.0, 0.12 v5.1.0, 0.06 v5.0.0, 0.07 v4.1.0, 0.08 v4.0.1, 0.18 v4.0.0, 0.09 v3.7.0, 0.00 v3.3.0, 0.14 v3.2.0, 0.08 v3.1.0, 0.09 v2.7.0, 0.08 v2.6.0, 0.00 v2.5.0, 0.08 v2.4.0, 0.11 v2.2.1, 0.11 v2.2.0, 0.22 v2.1.0, 0.33 v2.0.0
% Syntax   : Number of clauses     :   10 (   0 unt;   4 nHn;   8 RR)
%            Number of literals    :   31 (  17 equ;  17 neg)
%            Maximal clause size   :    4 (   3 avg)
%            Maximal term depth    :    2 (   1 avg)
%            Number of predicates  :    2 (   1 usr;   0 prp; 2-2 aty)
%            Number of functors    :    5 (   5 usr;   2 con; 0-2 aty)
%            Number of variables   :   23 (   2 sgn)
% SPC      : CNF_UNS_RFO_SEQ_NHN

% Comments :
%--------------------------------------------------------------------------
cnf(clause_1,axiom,
    ( ~ big_f(X,Y)
    | X = a ) ).

cnf(clause_2,axiom,
    ( ~ big_f(X,Y)
    | Y = b ) ).

cnf(clause_3,axiom,
    ( X != a
    | Y != b
    | big_f(X,Y) ) ).

cnf(clause_4,negated_conjecture,
    ( ~ big_f(Y,f(X))
    | Y != g(X)
    | f(X) = X ) ).

cnf(clause_5,negated_conjecture,
    ( ~ big_f(Y,f(X))
    | Y = g(X)
    | big_f(h(X,Z),f(X))
    | ~ big_f(h(X,Z),f(X)) ) ).

cnf(clause_6,negated_conjecture,
    ( Y != g(X)
    | big_f(Y,f(X))
    | f(X) = X ) ).

cnf(clause_7,negated_conjecture,
    ( Y != g(X)
    | big_f(Y,f(X))
    | big_f(h(X,Z),f(X))
    | h(X,Z) = Z ) ).

cnf(clause_8,negated_conjecture,
    ( Y != g(X)
    | big_f(Y,f(X))
    | h(X,Z) != Z
    | ~ big_f(h(X,Z),f(X)) ) ).

cnf(clause_9,negated_conjecture,
    ( f(X) != X
    | big_f(h(X,Z),f(X))
    | h(X,Z) = Z ) ).

cnf(clause_10,negated_conjecture,
    ( f(X) != X
    | h(X,Z) != Z
    | ~ big_f(h(X,Z),f(X)) ) ).

%--------------------------------------------------------------------------

```

    Overwriting /tmp/test.p

```python
! vampire --mode casc -t 1 --input_syntax tptp /tmp/test.p
```

    % Input is clausal, will run a generic CNF schedule.
    % WARNING: time unlimited strategy and instruction limiting not in place - attempting to translate instructions to time
    % dis+1002_3:1_sil=8000:urr=ec_only:flr=on:random_seed=1107239751:st=5:i=104:sd=1:ep=RST:ss=axioms_1 on test for (1ds/104Mi)
    % Refutation not found, incomplete strategy
    % ------------------------------
    % Version: Vampire 5.0.1 (Release build, commit 1b13eaf on 2026-01-18 12:14:50 +0000)
    % Linked with Z3 4.14.0.0 3c47fd96cf5645d0c42b2c819d9e9a84380aa721 NOTFOUND
    % CaDiCaL version: 2.1.3
    % Termination reason: Refutation not found, incomplete strategy
    % Time elapsed: 0.008 s
    % Peak memory usage: 11 MB
    % ------------------------------
    % ------------------------------
    % WARNING: time unlimited strategy and instruction limiting not in place - attempting to translate instructions to time
    % lrs-1002_1_sil=2000:random_seed=3682962797:i=118:sd=20:ss=axioms:sgt=8_1 on test for (1ds/118Mi)
    % Refutation not found, incomplete strategy
    % ------------------------------
    % Version: Vampire 5.0.1 (Release build, commit 1b13eaf on 2026-01-18 12:14:50 +0000)
    % Linked with Z3 4.14.0.0 3c47fd96cf5645d0c42b2c819d9e9a84380aa721 NOTFOUND
    % CaDiCaL version: 2.1.3
    % Termination reason: Refutation not found, incomplete strategy
    % Time elapsed: 0.001 s
    % Peak memory usage: 11 MB
    % ------------------------------
    % ------------------------------
    % WARNING: time unlimited strategy and instruction limiting not in place - attempting to translate instructions to time
    % dis+10_2:3_to=lpo:sil=2000:sp=unary_first:acc=on:urr=ec_only:fd=off:sac=on:random_seed=803463828:i=132:fgj=on:fsr=off_1 on test for (1ds/132Mi)
    % Solution written to "/tmp/vampire-proof-1368719"
    % Refutation found. Thanks to Tanya!
    % SZS status Unsatisfiable for test
    % SZS output start Proof for test
    fof(f1,axiom,(
      ( ! [X0,X1] : (~big_f(X0,X1) | X0 = a) )),
      file('/tmp/test.p',unknown)).
    fof(f2,plain,(
      ( ! [X0,X1] : (~big_f(X0,X1) | a = X0) )),
      inference(reorient_equations,[],[f1])).
    fof(f5,axiom,(
      ( ! [X0,X1] : (X0 != a | X1 != b | big_f(X0,X1)) )),
      file('/tmp/test.p',unknown)).
    fof(f6,plain,(
      ( ! [X0,X1] : (a != X0 | b != X1 | big_f(X0,X1)) )),
      inference(reorient_equations,[],[f5])).
    fof(f7,negated_conjecture,(
      ( ! [X0,X1] : (~big_f(X0,f(X1)) | X0 != g(X1) | f(X1) = X1) )),
      file('/tmp/test.p',unknown)).
    fof(f8,plain,(
      ( ! [X0,X1] : (~big_f(X0,f(X1)) | g(X1) != X0 | f(X1) = X1) )),
      inference(reorient_equations,[],[f7])).
    fof(f11,negated_conjecture,(
      ( ! [X0,X1] : (X0 != g(X1) | big_f(X0,f(X1)) | f(X1) = X1) )),
      file('/tmp/test.p',unknown)).
    fof(f12,plain,(
      ( ! [X0,X1] : (g(X1) != X0 | big_f(X0,f(X1)) | f(X1) = X1) )),
      inference(reorient_equations,[],[f11])).
    fof(f17,negated_conjecture,(
      ( ! [X0,X1] : (f(X0) != X0 | big_f(h(X0,X1),f(X0)) | h(X0,X1) = X1) )),
      file('/tmp/test.p',unknown)).
    fof(f18,negated_conjecture,(
      ( ! [X0,X1] : (h(X0,X1) != X1 | f(X0) != X0 | ~big_f(h(X0,X1),f(X0))) )),
      file('/tmp/test.p',unknown)).
    fof(f19,plain,(
      ( ! [X1] : (b != X1 | big_f(a,X1)) )),
      inference(equality_resolution,[],[f6])).
    fof(f20,plain,(
      big_f(a,b)),
      inference(equality_resolution,[],[f19])).
    fof(f21,plain,(
      ( ! [X1] : (~big_f(g(X1),f(X1)) | f(X1) = X1) )),
      inference(equality_resolution,[],[f8])).
    fof(f22,plain,(
      ( ! [X1] : (big_f(g(X1),f(X1)) | f(X1) = X1) )),
      inference(equality_resolution,[],[f12])).
    fof(f25,plain,(
      ( ! [X0] : (f(X0) = X0 | f(X0) = X0) )),
      inference(resolution,[],[f22,f21])).
    fof(f26,plain,(
      ( ! [X0] : (f(X0) = X0) )),
      inference(duplicate_literal_removal,[],[f25])).
    fof(f27,plain,(
      ( ! [X0,X1] : (X0 != X0 | big_f(h(X0,X1),X0) | h(X0,X1) = X1) )),
      inference(superposition,[],[f17,f26])).
    fof(f28,plain,(
      ( ! [X0,X1] : (big_f(h(X0,X1),X0) | h(X0,X1) = X1) )),
      inference(trivial_inequality_removal,[],[f27])).
    fof(f33,definition,(
      spl0_1 <=> big_f(a,b)),
      introduced(definition,[new_symbols(naming,[spl0_1])],[avatar_definition])).
    fof(f35,plain,(
      big_f(a,b) | ~spl0_1),
      inference(avatar_component_clause,[],[f33])).
    fof(f36,plain,(
      spl0_1),
      inference(avatar_split_clause,[],[f20,f33])).
    fof(f39,plain,(
      ( ! [X0,X1] : (a = h(X0,X1) | h(X0,X1) = X1) )),
      inference(resolution,[],[f2,f28])).
    fof(f75,plain,(
      ( ! [X0,X1] : (a != X1 | h(X0,X1) = X1) )),
      inference(equality_factoring,[],[f39])).
    fof(f84,plain,(
      ( ! [X0] : (a = h(X0,a)) )),
      inference(equality_resolution,[],[f75])).
    fof(f85,plain,(
      ( ! [X0] : (a != a | f(X0) != X0 | ~big_f(a,f(X0))) )),
      inference(superposition,[],[f18,f84])).
    fof(f88,plain,(
      ( ! [X0] : (f(X0) != X0 | ~big_f(a,f(X0))) )),
      inference(trivial_inequality_removal,[],[f85])).
    fof(f91,plain,(
      ( ! [X0] : (X0 != X0 | ~big_f(a,X0)) )),
      inference(superposition,[],[f88,f26])).
    fof(f92,plain,(
      ( ! [X0] : (~big_f(a,X0)) )),
      inference(trivial_inequality_removal,[],[f91])).
    fof(f93,plain,(
      $false | ~spl0_1),
      inference(unit_resulting_resolution,[],[f35,f92])).
    fof(f96,plain,(
      ~spl0_1),
      inference(avatar_contradiction_clause,[],[f93])).
    cnf(s1, plain, spl0_1, inference(sat_conversion,[],[f36])).
    cnf(s3, plain, ~spl0_1, inference(sat_conversion,[],[f96])).
    cnf(s4, plain, $false, inference(rat,[],[s1,s3])).
    fof(f97,plain,(
      $false),
      inference(avatar_sat_refutation,[],[s4])).
    % SZS output end Proof for test
    % ------------------------------
    % Version: Vampire 5.0.1 (Release build, commit 1b13eaf on 2026-01-18 12:14:50 +0000)
    % Linked with Z3 4.14.0.0 3c47fd96cf5645d0c42b2c819d9e9a84380aa721 NOTFOUND
    % CaDiCaL version: 2.1.3
    % Termination reason: Refutation
    % Time elapsed: 0.005 s
    % Peak memory usage: 12 MB
    % ------------------------------
    % ------------------------------
    % Success in time 0.036 s

```python
import scryer
m = scryer.Machine()
m.load_module_string("test",
"""
% (lift_lambdas = 1, lambda_to_forall = 1,unroll_only_formulas = 1, sine = (null))

% No proof found!
% SZS status Satisfiable
% Processed positive unit clauses:
cnf(i_0_16, plain, (zero->e2)).
cnf(i_0_12, plain, (e0->l(e2))).
cnf(i_0_14, plain, (mul(id,id)->e1)).
cnf(i_0_15, plain, (mul(e2,e2)->e2)).
cnf(i_0_11, plain, (mul(id,l(e2))->l(e2))).
cnf(i_0_20, plain, (mul(l(X1),l(X2))->l(mul(X1,X2)))).
cnf(i_0_17, plain, (mul(l(e2),id)->l(e2))).
cnf(i_0_18, plain, (mul(e1,l(e2))->l(e2))).

"""
)
m.query("cnf(X,Y,Z).")
```

    [{'Y': Atom { value: "plain" },
      'X': Atom { value: "i_0_16" },
      'Z': Compound { functor: "->", args: [Atom { value: "zero" }, Atom { value: "e2" }] }},
     {'Y': Atom { value: "plain" },
      'X': Atom { value: "i_0_12" },
      'Z': Compound { functor: "->", args: [Atom { value: "e0" }, Compound { functor: "l", args: [Atom { value: "e2" }] }] }},
     {'Z': Compound { functor: "->", args: [Compound { functor: "mul", args: [Atom { value: "id" }, Atom { value: "id" }] }, Atom { value: "e1" }] },
      'Y': Atom { value: "plain" },
      'X': Atom { value: "i_0_14" }},
     {'Z': Compound { functor: "->", args: [Compound { functor: "mul", args: [Atom { value: "e2" }, Atom { value: "e2" }] }, Atom { value: "e2" }] },
      'Y': Atom { value: "plain" },
      'X': Atom { value: "i_0_15" }},
     {'Z': Compound { functor: "->", args: [Compound { functor: "mul", args: [Atom { value: "id" }, Compound { functor: "l", args: [Atom { value: "e2" }] }] }, Compound { functor: "l", args: [Atom { value: "e2" }] }] },
      'X': Atom { value: "i_0_11" },
      'Y': Atom { value: "plain" }},
     {'Z': Compound { functor: "->", args: [Compound { functor: "mul", args: [Compound { functor: "l", args: [Var { name: "_A" }] }, Compound { functor: "l", args: [Var { name: "_B" }] }] }, Compound { functor: "l", args: [Compound { functor: "mul", args: [Var { name: "_A" }, Var { name: "_B" }] }] }] },
      'X': Atom { value: "i_0_20" },
      'Y': Atom { value: "plain" }},
     {'X': Atom { value: "i_0_17" },
      'Y': Atom { value: "plain" },
      'Z': Compound { functor: "->", args: [Compound { functor: "mul", args: [Compound { functor: "l", args: [Atom { value: "e2" }] }, Atom { value: "id" }] }, Compound { functor: "l", args: [Atom { value: "e2" }] }] }},
     {'X': Atom { value: "i_0_18" },
      'Y': Atom { value: "plain" },
      'Z': Compound { functor: "->", args: [Compound { functor: "mul", args: [Atom { value: "e1" }, Compound { functor: "l", args: [Atom { value: "e2" }] }] }, Compound { functor: "l", args: [Atom { value: "e2" }] }] }}]

```python
from kdrag.all import *
from IPython.display import display
x,y,z = smt.Ints("x y z")

pprint(If(x > 17, And(x > 7, ForAll(x, x + y >= y)), If(False, True, False)))


l = kd.Lemma(ForAll(x, x > 17, y > 24, And(x > 7, ForAll(x, x + y >= y))))
l.fix()
l.intros()
l.split(at=-1)
#l.intros()
display(pprint(l))
#l
```

$\displaystyle \begin{array}{ll} \text{fix} & x_{125} : \mathsf{Int} \\ h_{0} & x_{125} > 17 \\ h_{1} & y > 24 \\ \hline \vdash & (x_{125} > 7) \wedge (\forall x. x + y \geq y) \end{array}$

```python
from kdrag.all import *
from IPython.display import display

latex.to_latex(kd.seq(1,2,3))
pprint(kd.seq(1,2,3))

eps = Real("eps")
pprint(eps + 1)

x = smt.BitVec("x", 16)
pprint(x + 7)
#latex.to_latex(x + 7)
pprint(Concat(x,x,x))
pprint(Extract(6,5, x) + 2)
pprint(Implies(x > 7, x > 4))

```

$\displaystyle (\text{x} >_s \texttt{0x0007}) \rightarrow (\text{x} >_s \texttt{0x0004})$
