---
title: Knuth Bendix Solver on Z3 AST
date : 2025-03-11
---

Knuth bendix completion takes in a set of equational axioms and a term ordering (defining which side is "simpler"), and tries to produce a rewrite rule system that is confluent. You can read more here

- Term Rewriting and All That
- Harrison's Handbook of Practical Logic and Automated Reasoning
- <https://www.researchgate.net/publication/220460160_An_Introduction_to_Knuth-Bendix_Completion>
- <https://en.wikipedia.org/wiki/Knuth%E2%80%93Bendix_completion_algorithm>
- Handbook of Automated Reasoning chapter <https://www.cs.tau.ac.il/~nachum/papers/hand-final.pdf>

Pragmatically, confluent and terminating means the order of application of the rules ultimately doesn't matter. Greedy usage of the rules will find the "smallest" term under that theory.

If your system is non confluent but terminating, you need to add some kind of backtracking or search if you want this guarantee.

Knuth Bendix can fail when it fails to be able to orient an equation. Term orderings on non ground terms are necessarily partial orders. A demon can always pick a way to fill in the variables of `X * Y -> Y * X` to make any ordering choice fail. It's too symmetric.

Knuth Bendix is not quite a "complete" equational theorem proving mechanism because of this (unnecessary) failure. It's close though, and I tend to think of it as one.

Paramodulation is a name for brute force equational search, ordering be damned. Unfailing completion is a loosening of ordinary knuth bendix, but more restricted than brute paramodulation that nevertheless is complete for equational theorem proving. Unfailing completion and superposition are kind of synonyms in the unit clause context (?) although superposition implies the ability to hand non unit clauses like a resolution prover.

Paramodulation is kind of finding all critical pairs on all sides of equations. Knuth bendix restricts to just critical pairs of left hand sides of rules but also enables simplification by rules. Unfailing completion has a pruning mechanism for which critical pairs are necessary to consider and retains the simplification mechanism of KB.

I have found it useful to use Z3's ast as a centralized intercommunication way of building up a library of useful stuff. Z3 offers a nice api, a good fast hash cons, de bruijn binder manipulations and not the mention the smt solving itself.

All the fiddling with variables is kind of what makes completion complicated. String knuth bendix is more straightforward <https://www.philipzucker.com/string_knuth/> , likewise ground term knuth bendix.

They all follow the same pattern though. Pick an ordering.

Find "overlaps" of the left hand sides of two rules. These overlaps may get written two different directions. Infer that as a new equation to be processed.

The critical pair <https://en.wikipedia.org/wiki/Critical_pair_(term_rewriting)> refers to the two terms resulting from being rewritten by the two rules. The critical pair is the two terms that are equal in the rewrite system.

For terms with variables, we actually need to use unification rather than pattern matching to do our rewriting. This is called narrowing. It's a bit fiddly.

```python
import kdrag as kd
import kdrag.smt as smt
import kdrag.rewrite as rw


def critical_pair_helper(
    vs: list[smt.ExprRef], t: smt.ExprRef, lhs: smt.ExprRef, rhs: smt.ExprRef
) -> list[tuple[smt.ExprRef, dict[smt.ExprRef, smt.ExprRef]]]:
    """
    Look for pattern lhs to unify with a subterm of t.
    returns a list of all of those lhs -> rhs applied + the substitution resulting from the unification.
    The substitution is so that we can apply the other `t -> s` rule once we return.


    This helper is asymmettric between t and lhs. You need to call it twice to get all critical pairs.
    """
    res = []
    if any(t.eq(v) for v in vs): # Non trivial overlap only `X ~ lhs` is not interesting.
        return res
    subst = kd.utils.unify(vs, t, lhs)
    if subst is not None:
        res.append((rhs, subst))
    f, children = t.decl(), t.children()
    for n, arg in enumerate(children):
        # recurse into subterms and lift result under f if found something
        for s, subst in critical_pair_helper(vs, arg, lhs, rhs):
            args = children[:n] + [s] + children[n + 1 :]
            res.append((f(*args), subst))
    return res

x,y,z = smt.Reals("x y z")
critical_pair_helper([x,y], -(-(-(x))), -(-(y)), y)

```

    [(y, {y: -x}), (-y, {x: y}), (--y, {x: -y})]

```python
def all_pairs(rules):
    """
    Find all the ways the left hand side of two rules can overlap.
    Return a derived equation
    
    """
    # TODO. I'm not treating encompassment correctly
    res = []
    for rule1 in rules:
        for rule2 in rules:
            # we're double counting when rule1 = rule2 but whatever
            if any(v1.eq(v2) for v1 in rule1.vs for v2 in rule2.vs):
                rule2 = rule2.freshen()
            vs = rule1.vs + rule2.vs
            for t, subst in critical_pair_helper(vs, rule1.lhs, rule2.lhs, rule2.rhs):
                #print(rule1, rule2, t, subst)
                apply_rule1 = smt.substitute(rule1.rhs, *subst.items())
                apply_rule2 = smt.substitute(t, *subst.items())
                vs1 = list(set(vs) - set(subst.keys()))
                if len(vs1) == 0:
                    res.append(apply_rule1 == apply_rule2)
                else:
                    res.append(
                        smt.ForAll(vs1, apply_rule1 == apply_rule2)
                )  # new derived equation
    return res

a,b,c,d = smt.Reals("a b c d")
all_pairs([rw.RewriteRule(vs=[], lhs=x, rhs=y) for x,y in [(a,b), (b,c), (a,c), (a,d)]])

```

    [b == b,
     b == c,
     b == d,
     c == c,
     c == b,
     c == c,
     c == d,
     d == b,
     d == c,
     d == d]

You also want to orient rewrite rules. `RewriteRule` is a helper namedtuple to hold the pieces of a rule. It's kind of parsing well formed rules out of arbitrary z3 expressions.

```python
rw.rewrite_of_expr(smt.ForAll([x,y], x * 0 == x))
```

    RewriteRule(vs=[X!0, Y!1], lhs=X!0*0, rhs=X!0, pf=None)

```python
def orient(eq : smt.BoolRef | smt.QuantifierRef, order=rw.kbo) -> rw.RewriteRule:
    r = rw.rewrite_of_expr(eq)
    if order(r.vs, r.lhs, r.rhs) == rw.Order.GR:
        return r
    elif order(r.vs, r.rhs, r.lhs) == rw.Order.GR:
        return r._replace(lhs=r.rhs, rhs=r.lhs)
    else:
        raise Exception("Cannot orient: " + str(eq))

x,y,z = smt.Reals("x y z")
print(orient(smt.ForAll([x], -(-x) == x)))
print(orient(smt.ForAll([x], x == -(-x))))
print(orient(smt.ForAll([x,y,z], x + z == x + y + z + x + y)))
```

    RewriteRule(vs=[X!2], lhs=--X!2, rhs=X!2, pf=None)
    RewriteRule(vs=[X!3], lhs=--X!3, rhs=X!3, pf=None)
    RewriteRule(vs=[X!4, Y!5, Z!6], lhs=X!4 + Y!5 + Z!6 + X!4 + Y!5, rhs=X!4 + Z!6, pf=None)

You also want to simplify equations according to the current set of rewrite rules. I use my helper function `rewrite` from knuckledragger to do this. This part is not doing narrowing, you actually want regular pattern matching.

```python
def simplify(t : smt.BoolRef | smt.QuantifierRef, rules : list[rw.RewriteRule]) -> smt.ExprRef:
    r = rw.rewrite_of_expr(t)
    lhs = rw.rewrite(r.lhs, rules)
    rhs = rw.rewrite(r.rhs, rules)
    return r._replace(lhs=lhs, rhs=rhs).to_expr()

simplify(smt.ForAll([x], -(-(-(-(-x)))) == -x), [rw.rewrite_of_expr(smt.ForAll([x], -(-x) == x))])
```

&forall;X!8 : -X!8 = -X!8

This detects trivial `t = t` equations

```python
def is_trivial(t):
    r = rw.rewrite_of_expr(t)
    return r.lhs.eq(r.rhs)

assert is_trivial(x == x)
assert not is_trivial(x == -(-x))
```

The basic completion method just sprays creating critical pairs until all of them can be reduced to trivial by the current rules. It's a very brute force almost obvious way of attempting to complete (repair confluence) of the rules.

```python
def basic(E, order=rw.kbo):
    R = []
    for eq in E:
        R.append(orient(eq, order=order))
        #print("new", R[-1])
    i = 0
    done = False
    #print("pairing")
    while not done:
        done = True
        #print(R)
        for eq in all_pairs(R):
            #print(eq)
            eq1 = simplify(eq, R)
            if not is_trivial(eq1):
                #print("orig", eq,  "\nsimp", eq1)
                R.append(orient(eq1))
                #print("new", R[-1])
                done = False
        i += 1
    return R

# TRaaT 7.1.1 Central Groupoid example
T = smt.DeclareSort("CentralGroupoid")
x,y,z = smt.Consts("x y z", T)
mul = smt.Function("mul", T, T, T)
kd.notation.mul.register(T, mul)
E = [smt.ForAll([x,y,z], (x * y) * (y * z) == y)]

basic(E)
```

    [RewriteRule(vs=[X!9, Y!10, Z!11], lhs=mul(mul(X!9, Y!10), mul(Y!10, Z!11)), rhs=Y!10, pf=None),
     RewriteRule(vs=[X!29, Z!30, Z!31, Y!32], lhs=mul(Y!32, mul(mul(Y!32, Z!31), Z!30)), rhs=mul(Y!32, Z!31), pf=None),
     RewriteRule(vs=[X!41, Z!42, X!43, Y!44], lhs=mul(mul(X!43, mul(X!41, Y!44)), Y!44), rhs=mul(X!41, Y!44), pf=None)]

This is some variation of the Huet strategy of completion. It enables rules to be removed when they are being subsumed.

```python
def huet(E, order=rw.kbo):
    E = E.copy()
    R = []
    while True:
        while E:
            eq = E.pop()
            eq = simplify(eq, R)
            if is_trivial(eq):
                continue
            r = orient(eq, order=order)
            Rnew = [r]
            for r1 in R:
                lhs1 = rw.rewrite(r1.lhs , [r])
                if lhs1.eq(r1.lhs):
                    rhs1 = rw.rewrite(r1.rhs, R + [r])
                    Rnew.append(r1._replace(rhs=rhs1))
                else:
                    E.append(r1._replace(lhs=lhs1).to_expr())
            R = Rnew
        #print(R)
        for eq in all_pairs(R):
            # by marking rules, we can prune the critical pair search, but I haven't done that
            # This is something like a semi-naive or given clause optimization
            # Always smash against at least 1 fresh new thing (rule in this case).
            # It might help a lot. Perfomance benchmarking suggests simplify is the bottleneck
            eq1 = simplify(eq, R)
            if not is_trivial(eq1):
                E.append(eq1)
                #break
        if len(E) == 0:
            return R
        #print(E[-1])

huet(E)
```

    [RewriteRule(vs=[Y!320, Z!321, Z!322, X!323], lhs=mul(Y!320, mul(mul(Y!320, Z!321), Z!322)), rhs=mul(Y!320, Z!321), pf=None),
     RewriteRule(vs=[Y!308, Z!309, X!310, X!311], lhs=mul(mul(X!311, mul(X!310, Y!308)), Y!308), rhs=mul(X!310, Y!308), pf=None),
     RewriteRule(vs=[X!272, Y!273, Z!274], lhs=mul(mul(X!272, Y!273), mul(Y!273, Z!274)), rhs=Y!273, pf=None)]

I've implemented both knuth bendix (KBO) and lexicographic path ordering (LPO) by trying to just copy them out of TRaaT

I don't find term orderings very intuitive at all.

The basic intuition of KBO is that small size is better. You break size ties by recursing into the subtrees <https://www.philipzucker.com/ground_kbo/>

The basic intuition of LPO is that you want to push some symbols inside other symbols (`add` gets pushed inside `succ` for `add(succ(X), Y)) -> succ(add(X,Y))` whereas the sizes are kind of the same) and also that pushing complexity to right children is better than to the left children (like orienting associativity). A related intuition is that the symbol precedence ordering has some relation to the call graph ordering. A good precedence for things that are functional programming-like is often similar to the call graph / definitional ordering of those functions.

However, these intuitions get pretty mangled in order to deal with variables correctly.

A commonly used example is completing the axioms of an abstract group. I think this needs LPO and not KBO. At least KBO isn't terminating in reasonable time for me.

Adding in redundant axioms can make it go much faster. It shortcuts deriving them itself. It's kind of cool actually that the thing is proving theorems like the left identity from the right identity law and other such things.

```python
T = smt.DeclareSort("AbstractGroup")
x,y,z = smt.Consts("x y z", T)
e = smt.Const("a_e", T)
inv = smt.Function("c_inv", T, T)
mul = smt.Function("b_mul", T, T, T)
kd.notation.mul.register(T, mul)
kd.notation.invert.register(T, inv)
E = [
    smt.ForAll([x], e * x == x),
    # adding in these other redundant axioms makes it easier on the system
    #smt.ForAll([x], x * e == x),
    #smt.ForAll([x], x * inv(x) == e),
    smt.ForAll([x], inv(x) * x == e),
    smt.ForAll([x,y,z], (x * y) * z == x * (y * z)),
    #smt.ForAll([x,y], inv(x * y) == inv(y) * inv(x))
]
#basic(E, order=rw.lpo)
huet(E, order=rw.lpo)

```

    [RewriteRule(vs=[Z!7317, X!7318], lhs=c_inv(b_mul(X!7318, Z!7317)), rhs=b_mul(c_inv(Z!7317), c_inv(X!7318)), pf=None),
     RewriteRule(vs=[Z!4647, X!4648], lhs=b_mul(X!4648, b_mul(c_inv(X!4648), Z!4647)), rhs=Z!4647, pf=None),
     RewriteRule(vs=[X!4638], lhs=c_inv(c_inv(X!4638)), rhs=X!4638, pf=None),
     RewriteRule(vs=[], lhs=c_inv(a_e), rhs=a_e, pf=None),
     RewriteRule(vs=[X!4633], lhs=b_mul(X!4633, c_inv(X!4633)), rhs=a_e, pf=None),
     RewriteRule(vs=[X!4364], lhs=b_mul(X!4364, a_e), rhs=X!4364, pf=None),
     RewriteRule(vs=[X!4282, Z!4283], lhs=b_mul(c_inv(X!4282), b_mul(X!4282, Z!4283)), rhs=Z!4283, pf=None),
     RewriteRule(vs=[X!4246], lhs=b_mul(a_e, X!4246), rhs=X!4246, pf=None),
     RewriteRule(vs=[X!4243], lhs=b_mul(c_inv(X!4243), X!4243), rhs=a_e, pf=None),
     RewriteRule(vs=[X!4238, Y!4239, Z!4240], lhs=b_mul(b_mul(X!4238, Y!4239), Z!4240), rhs=b_mul(X!4238, b_mul(Y!4239, Z!4240)), pf=None)]

# Bits and Bobbles

So it's kind of slow.

Takes about 4 seconds for the group problem. A lot of time is in the simplifier, which in turn may be slow because of all the wrapping and unwrapping of going into and out of z3 for trivial-ish stuff. Worrying.

<https://smimram.github.io/ocaml-alg/kb/> This webpage is instantaneous for the group problem

eprover is also ludicrously faster. I do believe the saturated clause set represents something like the same data as knuth bendix completion. eprover is a more complicated beast, so it's hard for me to always interpret what it is returning when I'm using it off label from refutational theorem proving.

```python
%%file /tmp/group.p

cnf(id_left, axiom, mul(e, X) = X).
cnf(inv_left, axiom, mul(inv(X), X) = e).
cnf(assoc, axiom, mul(mul(X, Y), Z) = mul(X, mul(Y, Z))).

```

    Overwriting /tmp/group.p

```python
! time eprover-ho --print-saturated /tmp/group.p # you can also fiddle with the term ordering --term-ordering=KBO6  --order-weights or --precedence
```

    # Initializing proof state
    # Scanning for AC axioms
    # mul is associative
    #
    #cnf(i_0_4, plain, (mul(e,X1)=X1)).
    #
    #cnf(i_0_5, plain, (mul(inv(X1),X1)=e)).
    #
    #cnf(i_0_6, plain, (mul(mul(X1,X2),X3)=mul(X1,mul(X2,X3)))).
    #
    #cnf(i_0_8, plain, (mul(inv(X1),mul(X1,X2))=X2)).
    #
    #cnf(i_0_14, plain, (mul(inv(e),X1)=X1)).
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
    #cnf(i_0_41, plain, (mul(X1,mul(X2,inv(mul(X1,X2))))=e)).
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
    cnf(i_0_4, plain, (mul(e,X1)=X1)).
    cnf(i_0_5, plain, (mul(inv(X1),X1)=e)).
    cnf(i_0_6, plain, (mul(mul(X1,X2),X3)=mul(X1,mul(X2,X3)))).
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
    
    
    
    real 0m0.003s
    user 0m0.001s
    sys 0m0.002s

Some other links to look at

<https://www.philipzucker.com/string_knuth/>

<https://github.com/codyroux/knuth-bendix>

- Twee
- Waldmeister <https://www.mpi-inf.mpg.de/departments/automation-of-logic/software/waldmeister/download> a fast C knuth bendix. Where's the source though?

Superposition provers are quite related. E prover, zipperposition, SPASS

mkbtt <https://github.com/bytekid/mkbtt>

<https://www.metalevel.at/trs/> prolog knuth bendix

<https://github.com/smimram/ocaml-alg>

<https://github.com/brandonwillard/mk-rewrite-completion>

<https://rg1-teaching.mpi-inf.mpg.de/autrea-ss11/script-4.7.pdf>

Just implement paramodulation.

```python
import z3
z3.Z3_DEBUG = False
smt.z3_debug()
smt.z3.Z3_DEBUG = False
smt.z3.z3_debug()
# turning off debug sanity checks shaves about 1s off, 25% speedup
```

    False

Some ideas for speeding up

- Maybe pmatch to traverse the term t for multiple patterns
- Cache calls to t.arg. ExprRef.cache_arg() that'll look it up in a dict.
- Doing proper marking of rules out to prune critical pairs considered. `speed = number of time called * speed of 1 call` after all
- Could "precompile" patterns either by currying pmatch or by codegen
- Being lazier about arg calls in pmatch might help if pmatch fails often
- pmatch is churning, creating and immediately deleting python nodes

It is somewhat surprising that unification and the unnecessary binder opening I'm doing isnt the problem

```python
%%prun 
huet(E, order=rw.lpo)
```

             39345171 function calls (39247118 primitive calls) in 10.420 seconds
    
       Ordered by: internal time
    
       ncalls  tottime  percall  cumtime  percall filename:lineno(function)
      3905417    1.420    0.000    1.595    0.000 z3core.py:1567(Check)
    654671/654428    0.482    0.000    0.820    0.000 z3core.py:2979(Z3_func_decl_to_ast)
       559621    0.425    0.000    0.714    0.000 z3core.py:3124(Z3_get_ast_kind)
       544941    0.408    0.000    1.739    0.000 z3.py:345(__init__)
       544941    0.405    0.000    0.680    0.000 z3core.py:1637(Z3_inc_ref)
       544705    0.396    0.000    1.389    0.000 z3.py:350(__del__)
      8355539    0.385    0.000    0.385    0.000 z3types.py:24(from_param)
      2120782    0.380    0.000    0.496    0.000 z3.py:400(ctx_ref)
        35444    0.328    0.000    7.737    0.000 utils.py:48(pmatch)
       544705    0.320    0.000    0.373    0.000 z3core.py:1641(Z3_dec_ref)
       339799    0.307    0.000    0.525    0.000 z3core.py:3094(Z3_is_eq_ast)
       234008    0.297    0.000    1.723    0.000 z3.py:1158(_to_expr_ref)
       339799    0.283    0.000    1.337    0.000 z3.py:404(eq)
      4526811    0.249    0.000    0.249    0.000 z3.py:218(ref)
       337128    0.248    0.000    0.419    0.000 z3core.py:2874(Z3_get_sort_kind)
       322577    0.240    0.000    0.401    0.000 z3core.py:3109(Z3_get_sort)
       293366    0.222    0.000    0.372    0.000 z3core.py:3079(Z3_get_app_decl)
    654671/654428    0.211    0.000    1.175    0.000 z3.py:748(as_ast)
       325613    0.207    0.000    0.731    0.000 z3.py:491(_ast_kind)
       209012    0.201    0.000    0.308    0.000 z3core.py:3089(Z3_get_app_arg)
    3413754/3411483    0.198    0.000    0.210    0.000 z3types.py:64(from_param)
       200747    0.187    0.000    1.312    0.000 z3.py:1061(decl)
       209012    0.180    0.000    2.100    0.000 z3.py:1099(arg)
       223829    0.172    0.000    0.290    0.000 z3core.py:2864(Z3_sort_to_ast)
      1992882    0.123    0.000    0.123    0.000 z3.py:990(as_ast)
       326816    0.111    0.000    0.865    0.000 z3.py:1290(is_app)
       139271    0.104    0.000    0.331    0.000 z3.py:1083(num_args)
       139271    0.103    0.000    0.175    0.000 z3core.py:3084(Z3_get_app_num_args)
    991331/991327    0.084    0.000    0.084    0.000 {built-in method builtins.isinstance}
       103120    0.081    0.000    0.678    0.000 z3.py:660(_to_sort_ref)
      1121613    0.080    0.000    0.080    0.000 z3.py:62(z3_debug)
        92619    0.079    0.000    0.362    0.000 z3.py:1076(kind)
       223829    0.075    0.000    0.416    0.000 z3.py:562(as_ast)
        90663    0.070    0.000    0.117    0.000 z3core.py:3104(Z3_get_ast_hash)
        92619    0.069    0.000    0.116    0.000 z3core.py:2999(Z3_get_decl_kind)
    145880/143693    0.056    0.000    0.761    0.000 {built-in method builtins.any}
       255325    0.053    0.000    0.543    0.000 utils.py:63(<genexpr>)
        90663    0.050    0.000    0.275    0.000 z3.py:440(hash)
        88569    0.048    0.000    0.750    0.000 z3.py:691(_sort)
        35444    0.048    0.000    8.013    0.000 rewrite.py:281(rewrite1_rule)
       325613    0.047    0.000    0.068    0.000 z3.py:451(is_ast)
    772676/772479    0.046    0.000    0.047    0.000 z3types.py:56(from_param)
        13990    0.044    0.000    0.345    0.000 z3.py:837(__call__)
    12159/2134    0.042    0.000    8.853    0.004 rewrite.py:404(worker)
        53759    0.041    0.000    0.690    0.000 z3.py:1120(children)
       550792    0.040    0.000    0.040    0.000 z3.py:260(_get_ctx)
        96960    0.038    0.000    0.622    0.000 utils.py:62(is_var)
        92619    0.038    0.000    0.651    0.000 z3.py:1393(is_app_of)
       635290    0.038    0.000    0.039    0.000 z3types.py:48(from_param)
       103120    0.036    0.000    0.173    0.000 z3.py:555(_sort_kind)
        35444    0.033    0.000    0.053    0.000 z3core.py:2869(Z3_is_eq_sort)
        88569    0.033    0.000    0.788    0.000 z3.py:996(sort)
         2134    0.030    0.000    9.351    0.004 rewrite.py:380(rewrite)
    34383/17765    0.029    0.000    0.454    0.000 utils.py:65(check_escape)
       106360    0.026    0.000    0.698    0.000 z3.py:364(__eq__)
        13990    0.023    0.000    0.032    0.000 z3core.py:1861(Z3_mk_app)
        90663    0.021    0.000    0.296    0.000 z3.py:367(__hash__)
        77445    0.020    0.000    0.561    0.000 z3.py:4939(is_select)
         4863    0.019    0.000    0.080    0.000 z3.py:8986(substitute)
        35444    0.015    0.000    0.077    0.000 z3.py:631(__ne__)
       117467    0.014    0.000    0.014    0.000 {method 'append' of 'list' objects}
         4863    0.014    0.000    0.017    0.000 z3core.py:3359(Z3_substitute)
         1710    0.013    0.000    0.346    0.000 utils.py:140(unify)
      34648/1    0.013    0.000    0.001    0.001 {built-in method builtins.all}
        44394    0.013    0.000    0.119    0.000 z3.py:1036(__hash__)
        11198    0.012    0.000    0.018    0.000 z3core.py:3014(Z3_get_domain)
       101101    0.012    0.000    0.012    0.000 {method 'pop' of 'list' objects}
         5863    0.011    0.000    0.192    0.000 z3.py:1227(_coerce_exprs)
         1203    0.011    0.000    0.012    0.000 z3core.py:2819(Z3_mk_quantifier_const_ex)
         1203    0.011    0.000    0.040    0.000 z3.py:2244(_mk_quantifier)
    51001/28143    0.010    0.000    0.209    0.000 utils.py:69(<genexpr>)
         3445    0.010    0.000    0.014    0.000 z3core.py:1876(Z3_mk_fresh_const)
         5863    0.010    0.000    0.251    0.000 z3.py:1019(__eq__)
         4580    0.009    0.000    0.245    0.000 z3.py:373(__bool__)
         1349    0.009    0.000    0.169    0.000 utils.py:15(open_binder)
         5863    0.009    0.000    0.012    0.000 z3core.py:1900(Z3_mk_eq)
        19189    0.008    0.000    0.126    0.000 {method 'get' of 'dict' objects}
         1349    0.008    0.000    0.009    0.000 z3core.py:3364(Z3_substitute_vars)
        18853    0.008    0.000    0.012    0.000 z3.py:144(_get_args)
            6    0.007    0.001    0.710    0.118 1089511573.py:1(all_pairs)
        11198    0.007    0.000    0.103    0.000 z3.py:778(domain)
     3160/610    0.007    0.000    0.469    0.001 3721489288.py:6(critical_pair_helper)
        74820    0.007    0.000    0.007    0.000 {built-in method builtins.len}
         1349    0.006    0.000    0.026    0.000 z3.py:9019(substitute_vars)
        11726    0.006    0.000    0.154    0.000 z3.py:1208(_coerce_expr_merge)
         1434    0.006    0.000    0.231    0.000 rewrite.py:320(rewrite_of_expr)
        27312    0.005    0.000    0.067    0.000 utils.py:148(<genexpr>)
         5863    0.005    0.000    0.341    0.000 notation.py:80(__call__)
        34383    0.005    0.000    0.006    0.000 utils.py:66(<genexpr>)
         3551    0.005    0.000    0.010    0.000 z3core.py:2844(Z3_get_symbol_string)
         5863    0.005    0.000    0.366    0.000 notation.py:173(<lambda>)
        22924    0.005    0.000    0.007    0.000 z3.py:593(cast)
    3512/1434    0.004    0.000    0.061    0.000 utils.py:204(occurs)
         3353    0.004    0.000    0.005    0.000 z3core.py:3319(Z3_get_quantifier_bound_sort)
         5851    0.003    0.000    0.006    0.000 z3core.py:88(_str_to_bytes)
         3353    0.003    0.000    0.005    0.000 z3core.py:3314(Z3_get_quantifier_bound_name)
         2406    0.003    0.000    0.007    0.000 z3core.py:1750(Z3_mk_string_symbol)
    1893/1750    0.003    0.000    0.054    0.000 utils.py:262(alpha_eq)
          448    0.003    0.000    0.006    0.000 ipkernel.py:775(_clean_thread_parent_frames)
         3551    0.003    0.000    0.005    0.000 z3core.py:2834(Z3_get_symbol_kind)
        18792    0.003    0.000    0.004    0.000 z3.py:1267(is_expr)
         3445    0.003    0.000    0.044    0.000 z3.py:1489(FreshConst)
         3551    0.003    0.000    0.018    0.000 z3.py:132(_symbol2py)
         3353    0.003    0.000    0.026    0.000 z3.py:2186(var_name)
         3353    0.003    0.000    0.032    0.000 z3.py:2202(var_sort)
         6466    0.003    0.000    0.073    0.000 utils.py:147(is_var)
          700    0.003    0.000    8.860    0.013 1833036872.py:1(simplify)
         2406    0.002    0.000    0.011    0.000 z3.py:124(to_symbol)
        10412    0.002    0.000    0.027    0.000 3721489288.py:18(<genexpr>)
    5273/2557    0.002    0.000    0.047    0.000 utils.py:218(<genexpr>)
         3551    0.002    0.000    0.003    0.000 z3core.py:95(_to_pystr)
         5863    0.002    0.000    0.252    0.000 smt.py:153(Eq)
         1101    0.002    0.000    0.004    0.000 __init__.py:457(_replace)
         5863    0.002    0.000    0.027    0.000 z3.py:642(__hash__)
         1349    0.002    0.000    0.002    0.000 z3core.py:3259(Z3_is_quantifier_forall)
         6014    0.002    0.000    0.045    0.000 z3.py:1716(is_eq)
          224    0.001    0.000    0.002    0.000 threading.py:1533(enumerate)
         2586    0.001    0.000    0.001    0.000 {built-in method __new__ of type object at 0xa43b40}
         4580    0.001    0.000    0.036    0.000 z3.py:1636(is_true)
         1349    0.001    0.000    0.002    0.000 z3core.py:3309(Z3_get_quantifier_num_bound)
         1349    0.001    0.000    0.002    0.000 z3core.py:3324(Z3_get_quantifier_body)
          724    0.001    0.000    0.074    0.000 rewrite.py:261(to_expr)
         4580    0.001    0.000    0.034    0.000 z3.py:1654(is_false)
         5851    0.001    0.000    0.001    0.000 {method 'encode' of 'str' objects}
         1203    0.001    0.000    0.041    0.000 z3.py:2279(ForAll)
          700    0.001    0.000    0.120    0.000 1269168809.py:1(is_trivial)
         1568    0.001    0.000    0.001    0.000 threading.py:1196(ident)
        339/0    0.001    0.000    0.000          rewrite.py:523(lpo)
         1349    0.001    0.000    0.013    0.000 z3.py:2163(body)
         1349    0.001    0.000    0.003    0.000 z3.py:2174(num_vars)
         9402    0.001    0.000    0.001    0.000 {built-in method sys.getdefaultencoding}
         1203    0.001    0.000    0.001    0.000 z3.py:523(_to_ast_array)
         1349    0.001    0.000    0.004    0.000 z3.py:2050(is_forall)
         3353    0.001    0.000    0.001    0.000 {method 'split' of 'str' objects}
         2535    0.001    0.000    0.001    0.000 {method 'extend' of 'list' objects}
         3551    0.001    0.000    0.001    0.000 {method 'decode' of 'bytes' objects}
         2226    0.001    0.000    0.006    0.000 1089511573.py:12(<genexpr>)
         3617    0.001    0.000    0.001    0.000 {method 'items' of 'dict' objects}
         9508    0.001    0.000    0.001    0.000 z3types.py:40(from_param)
         1101    0.001    0.000    0.002    0.000 __init__.py:447(_make)
         1485    0.001    0.000    0.001    0.000 <string>:1(<lambda>)
         3360    0.001    0.000    0.001    0.000 {method 'upper' of 'str' objects}
           51    0.001    0.000    0.007    0.000 rewrite.py:245(freshen)
         2406    0.000    0.000    0.001    0.000 z3.py:71(_is_int)
       376/96    0.000    0.000    0.012    0.000 utils.py:230(is_subterm)
          584    0.000    0.000    0.004    0.000 rewrite.py:530(is_var)
         1594    0.000    0.000    0.004    0.000 rewrite.py:531(<genexpr>)
          7/2    0.000    0.000    0.001    0.001 events.py:86(_run)
         1298    0.000    0.000    0.000    0.000 z3.py:2230(is_quantifier)
         1455    0.000    0.000    0.000    0.000 {method 'keys' of 'dict' objects}
          198    0.000    0.000    0.000    0.000 z3core.py:2994(Z3_get_decl_name)
         2406    0.000    0.000    0.000    0.000 z3.py:2038(as_ast)
          198    0.000    0.000    0.002    0.000 z3.py:757(name)
       143/95    0.000    0.000    0.006    0.000 utils.py:296(<genexpr>)
       273/85    0.000    0.000    0.014    0.000 rewrite.py:545(<genexpr>)
          448    0.000    0.000    0.000    0.000 {method 'values' of 'dict' objects}
         33/0    0.000    0.000    0.000          45952297.py:1(orient)
          225    0.000    0.000    0.000    0.000 {method '__exit__' of '_thread.RLock' objects}
      441/152    0.000    0.000    0.007    0.000 utils.py:237(<genexpr>)
          106    0.000    0.000    0.000    0.000 z3core.py:3099(Z3_get_ast_id)
            1    0.000    0.000    0.001    0.001 zmqstream.py:624(_handle_recv)
            1    0.000    0.000    0.000    0.000 {method 'disable' of '_lsprof.Profiler' objects}
          106    0.000    0.000    0.000    0.000 z3.py:751(get_id)
            7    0.000    0.000    0.000    0.000 attrsettr.py:66(_get_attr_opt)
         77/3    0.000    0.000    0.000    0.000 rewrite.py:547(<genexpr>)
            7    0.000    0.000    0.002    0.000 base_events.py:1910(_run_once)
            7    0.000    0.000    0.000    0.000 socket.py:626(send)
        43/41    0.000    0.000    0.005    0.000 rewrite.py:558(<genexpr>)
            1    0.000    0.000    0.000    0.000 iostream.py:127(_event_pipe_gc)
           63    0.000    0.000    0.000    0.000 enum.py:1544(_get_value)
            7    0.000    0.000    0.000    0.000 attrsettr.py:43(__getattr__)
          6/2    0.000    0.000    0.000    0.000 selectors.py:451(select)
           11    0.000    0.000    0.000    0.000 enum.py:1562(__and__)
            3    0.000    0.000    0.000    0.000 socket.py:236(close)
          6/2    0.000    0.000    0.000    0.000 {method 'poll' of 'select.epoll' objects}
            1    0.000    0.000    0.000    0.000 inspect.py:3102(_bind)
          6/5    0.000    0.000    0.001    0.000 {method 'run' of '_contextvars.Context' objects}
           29    0.000    0.000    0.000    0.000 enum.py:726(__call__)
            1    0.000    0.000    0.000    0.000 queues.py:225(get)
           10    0.000    0.000    0.000    0.000 enum.py:1551(__or__)
            1    0.000    0.000    0.000    0.000 history.py:845(writeout_cache)
            2    0.000    0.000    0.000    0.000 typing.py:1194(__instancecheck__)
            1    0.000    0.000    0.000    0.000 {method 'recv' of '_socket.socket' objects}
            3    0.000    0.000    0.001    0.000 zmqstream.py:583(_handle_events)
            4    0.000    0.000    0.000    0.000 zmqstream.py:663(_rebuild_io_state)
            1    0.000    0.000    0.000    0.000 traitlets.py:1512(_notify_trait)
            1    0.000    0.000    0.000    0.000 iostream.py:276(<lambda>)
            1    0.000    0.000    0.000    0.000 zmqstream.py:556(_run_callback)
           29    0.000    0.000    0.000    0.000 enum.py:1129(__new__)
            6    0.000    0.000    0.000    0.000 threading.py:1220(is_alive)
            1    0.000    0.000    0.000    0.000 kernelbase.py:302(poll_control_queue)
            1    0.000    0.000    0.000    0.000 {method 'execute' of 'sqlite3.Connection' objects}
            1    0.000    0.000    0.000    0.000 iostream.py:118(_run_event_pipe_gc)
            2    0.000    0.000    0.000    0.000 traitlets.py:3631(set)
           12    0.000    0.000    0.000    0.000 {built-in method builtins.hasattr}
            4    0.000    0.000    0.000    0.000 events.py:36(__init__)
            4    0.000    0.000    0.000    0.000 queue.py:97(empty)
            2    0.000    0.000    0.000    0.000 traitlets.py:718(_validate)
           12    0.000    0.000    0.000    0.000 {built-in method builtins.max}
            2    0.000    0.000    0.000    0.000 tasks.py:653(sleep)
            4    0.000    0.000    0.000    0.000 zmqstream.py:686(_update_handler)
            1    0.000    0.000    0.000    0.000 decorator.py:199(fix)
            3    0.000    0.000    0.000    0.000 base_events.py:814(_call_soon)
            7    0.000    0.000    0.000    0.000 <frozen importlib._bootstrap>:1390(_handle_fromlist)
            2    0.000    0.000    0.000    0.000 traitlets.py:3474(validate)
            1    0.000    0.000    0.000    0.000 traitlets.py:1527(_notify_observers)
            2    0.000    0.000    0.000    0.000 traitlets.py:689(set)
            6    0.000    0.000    0.000    0.000 traitlets.py:676(__get__)
            2    0.000    0.000    0.000    0.000 traitlets.py:727(_cross_validate)
          9/3    0.000    0.000    0.000    0.000 {method 'acquire' of '_thread.lock' objects}
            1    0.000    0.000    0.000    0.000 socket.py:774(recv_multipart)
            2    0.000    0.000    0.000    0.000 traitlets.py:3624(validate_elements)
            2    0.000    0.000    0.000    0.000 {method '__exit__' of 'sqlite3.Connection' objects}
           10    0.000    0.000    0.000    0.000 {built-in method builtins.getattr}
            3    0.000    0.000    0.000    0.000 threading.py:299(__enter__)
            6    0.000    0.000    0.000    0.000 threading.py:1153(_wait_for_tstate_lock)
            1    0.000    0.000    0.000    0.000 {method 'send' of '_socket.socket' objects}
           11    0.000    0.000    0.000    0.000 base_events.py:734(time)
            6    0.000    0.000    0.000    0.000 selector_events.py:750(_process_events)
            1    0.000    0.000    0.000    0.000 queues.py:256(get_nowait)
            2    0.000    0.000    0.000    0.000 {built-in method builtins.issubclass}
            2    0.000    0.000    0.000    0.000 typing.py:1465(__subclasscheck__)
            1    0.000    0.000    0.000    0.000 events.py:155(cancel)
            2    0.000    0.000    0.000    0.000 traitlets.py:2304(validate)
            3    0.000    0.000    0.000    0.000 _weakrefset.py:115(discard)
            6    0.000    0.000    0.000    0.000 traitlets.py:629(get)
            1    0.000    0.000    0.000    0.000 futures.py:311(_set_result_unless_cancelled)
            1    0.000    0.000    0.000    0.000 asyncio.py:225(add_callback)
            1    0.000    0.000    0.000    0.000 base_events.py:447(create_future)
            1    0.000    0.000    0.000    0.000 inspect.py:3237(bind)
            1    0.000    0.000    0.000    0.000 traitlets.py:1523(notify_change)
            1    0.000    0.000    0.000    0.000 inspect.py:2918(apply_defaults)
            3    0.000    0.000    0.000    0.000 threading.py:1079(_stop)
            2    0.000    0.000    0.000    0.000 traitlets.py:708(__set__)
            1    0.000    0.000    0.000    0.000 threading.py:308(_release_save)
            1    0.000    0.000    0.000    0.000 base_events.py:743(call_later)
            1    0.000    0.000    0.000    0.000 iostream.py:157(_handle_event)
            9    0.000    0.000    0.000    0.000 {method '__exit__' of '_thread.lock' objects}
            1    0.000    0.000    0.000    0.000 base_events.py:767(call_at)
            1    0.000    0.000    0.000    0.000 iostream.py:278(_really_send)
            6    0.000    0.000    0.000    0.000 {method 'discard' of 'set' objects}
            3    0.000    0.000    0.000    0.000 context.py:285(_rm_socket)
            1    0.000    0.000    0.000    0.000 base_events.py:838(call_soon_threadsafe)
            4    0.000    0.000    0.000    0.000 zmqstream.py:542(sending)
            1    0.000    0.000    0.000    0.000 {method 'set_result' of '_asyncio.Future' objects}
            1    0.000    0.000    0.000    0.000 history.py:839(_writeout_output_cache)
            3    0.000    0.000    0.000    0.000 threading.py:302(__exit__)
           11    0.000    0.000    0.000    0.000 {built-in method time.monotonic}
            1    0.000    0.000    0.000    0.000 threading.py:311(_acquire_restore)
            8    0.000    0.000    0.000    0.000 {method 'append' of 'collections.deque' objects}
            1    0.000    0.000    0.000    0.000 inspect.py:2865(args)
            3    0.000    0.000    0.000    0.000 typing.py:392(inner)
            2    0.000    0.000    0.000    0.000 asyncio.py:200(_handle_events)
            1    0.000    0.000    0.000    0.000 _base.py:537(set_result)
            2    0.000    0.000    0.000    0.000 {built-in method _abc._abc_subclasscheck}
            2    0.000    0.000    0.000    0.000 base_events.py:785(call_soon)
            4    0.000    0.000    0.000    0.000 {built-in method math.ceil}
            1    0.000    0.000    0.000    0.000 threading.py:424(notify_all)
           23    0.000    0.000    0.000    0.000 typing.py:2154(cast)
            2    0.000    0.000    0.000    0.000 traitlets.py:3486(validate_elements)
            4    0.000    0.000    0.000    0.000 {built-in method builtins.min}
            4    0.000    0.000    0.000    0.000 queue.py:209(_qsize)
            1    0.000    0.000    0.000    0.000 history.py:55(only_when_enabled)
            3    0.000    0.000    0.000    0.000 socket.py:175(__del__)
            1    0.000    0.000    0.000    0.000 futures.py:394(_call_set_state)
            1    0.000    0.000    0.000    0.000 history.py:833(_writeout_input_cache)
            1    0.000    0.000    0.001    0.001 zmqstream.py:694(<lambda>)
            2    0.000    0.000    0.000    0.000 <frozen abc>:121(__subclasscheck__)
            6    0.000    0.000    0.000    0.000 {built-in method builtins.next}
            1    0.000    0.000    0.000    0.000 selector_events.py:141(_write_to_self)
            1    0.000    0.000    0.000    0.000 queues.py:173(qsize)
            2    0.000    0.000    0.000    0.000 {built-in method _asyncio.get_running_loop}
            1    0.000    0.000    0.000    0.000 _base.py:337(_invoke_callbacks)
            2    0.000    0.000    0.000    0.000 typing.py:1258(__hash__)
            1    0.000    0.000    0.000    0.000 socket.py:703(send_multipart)
            3    0.000    0.000    0.000    0.000 {built-in method _contextvars.copy_context}
            1    0.000    0.000    0.000    0.000 threading.py:394(notify)
            1    0.000    0.000    0.000    0.000 decorator.py:229(fun)
            3    0.000    0.000    0.000    0.000 _weakrefset.py:39(_remove)
            7    0.000    0.000    0.000    0.000 {method 'popleft' of 'collections.deque' objects}
            1    0.000    0.000    0.000    0.000 threading.py:627(clear)
            1    0.000    0.000    0.000    0.000 {built-in method _thread.allocate_lock}
            1    0.000    0.000    0.000    0.000 inspect.py:2888(kwargs)
            1    0.000    0.000    0.001    0.001 ioloop.py:742(_run_callback)
            5    0.000    0.000    0.000    0.000 zmqstream.py:538(receiving)
            7    0.000    0.000    0.000    0.000 base_events.py:2005(get_debug)
            1    0.000    0.000    0.000    0.000 events.py:111(__init__)
            1    0.000    0.000    0.000    0.000 iostream.py:213(_is_master_process)
            1    0.000    0.000    0.000    0.000 queues.py:322(_consume_expired)
            1    0.000    0.000    0.000    0.000 {method 'values' of 'mappingproxy' objects}
            3    0.000    0.000    0.000    0.000 threading.py:1234(daemon)
            4    0.000    0.000    0.000    0.000 base_events.py:539(_check_closed)
            1    0.000    0.000    0.000    0.000 events.py:72(cancel)
           10    0.000    0.000    0.000    0.000 inspect.py:2777(kind)
            3    0.000    0.000    0.000    0.000 {method 'items' of 'mappingproxy' objects}
            6    0.000    0.000    0.000    0.000 threading.py:601(is_set)
            4    0.000    0.000    0.000    0.000 {method 'release' of '_thread.lock' objects}
            2    0.000    0.000    0.000    0.000 {method '__enter__' of '_thread.lock' objects}
            1    0.000    0.000    0.000    0.000 threading.py:314(_is_owned)
            1    0.000    0.000    0.000    0.000 unix_events.py:81(_process_self_data)
            2    0.000    0.000    0.000    0.000 selectors.py:275(_key_from_fd)
            2    0.000    0.000    0.000    0.000 base_events.py:1895(_add_callback)
            1    0.000    0.000    0.000    0.000 {built-in method _heapq.heappop}
            2    0.000    0.000    0.000    0.000 {method 'cancelled' of '_asyncio.Future' objects}
            1    0.000    0.000    0.000    0.000 iostream.py:216(_check_mp_mode)
            1    0.000    0.000    0.000    0.000 {method 'copy' of 'list' objects}
            2    0.000    0.000    0.000    0.000 {built-in method builtins.iter}
            1    0.000    0.000    0.000    0.000 {method '__enter__' of '_thread.RLock' objects}
            4    0.000    0.000    0.000    0.000 inspect.py:3058(parameters)
            1    0.000    0.000    0.000    0.000 {built-in method posix.getpid}
            1    0.000    0.000    0.000    0.000 queues.py:59(_set_timeout)
            1    0.000    0.000    0.000    0.000 base_events.py:1905(_timer_handle_cancelled)
            2    0.000    0.000    0.000    0.000 {built-in method builtins.hash}
            1    0.000    0.000    0.000    0.000 {built-in method _heapq.heappush}
            3    0.000    0.000    0.000    0.000 {method 'locked' of '_thread.lock' objects}
            4    0.000    0.000    0.000    0.000 inspect.py:2765(name)
            1    0.000    0.000    0.000    0.000 base_events.py:720(is_closed)
            1    0.000    0.000    0.000    0.000 inspect.py:2857(__init__)
            1    0.000    0.000    0.000    0.000 iostream.py:255(closed)
            1    0.000    0.000    0.000    0.000 {method '_is_owned' of '_thread.RLock' objects}

```python
T = smt.DeclareSort("AbstractGroup")
x,y,z = smt.Consts("x y z", T)
e = smt.Const("a_e", T)
inv = smt.Function("c_inv", T, T)
mul = smt.Function("b_mul", T, T, T)
kd.notation.mul.register(T, mul)
E = [
    smt.ForAll([x,y], inv(x * y) == inv(y) * inv(x)), #k28
    smt.ForAll([x,y], x * (inv(x) * y) == y), # k 16
    smt.ForAll([x], x * inv(x) == e), # k12
    smt.ForAll([x], inv(e) == e), # k11
    smt.ForAll([x], inv(inv(x)) == x), #k9
    smt.ForAll([x], x * e == x), # k2
    smt.ForAll([x,y], inv(x) * (x * y) == y), #k1
    #smt.ForAll([x], x * e == x),
    #smt.ForAll([x], x * inv(x) == e),
    smt.ForAll([x,y,z], (x * y) * z == x * (y * z)), #R1
    smt.ForAll([x], inv(x) * x == e),
    smt.ForAll([x], e * x == x),
]

basic(E, order=rw.lpo)
#huet(E, order=rw.lpo)
```

    [RewriteRule(vs=[X!3990, Y!3991], lhs=c_inv(b_mul(X!3990, Y!3991)), rhs=b_mul(c_inv(Y!3991), c_inv(X!3990)), pf=None),
     RewriteRule(vs=[X!3992, Y!3993], lhs=b_mul(X!3992, b_mul(c_inv(X!3992), Y!3993)), rhs=Y!3993, pf=None),
     RewriteRule(vs=[X!3994], lhs=b_mul(X!3994, c_inv(X!3994)), rhs=a_e, pf=None),
     RewriteRule(vs=[X!3995], lhs=c_inv(a_e), rhs=a_e, pf=None),
     RewriteRule(vs=[X!3996], lhs=c_inv(c_inv(X!3996)), rhs=X!3996, pf=None),
     RewriteRule(vs=[X!3997], lhs=b_mul(X!3997, a_e), rhs=X!3997, pf=None),
     RewriteRule(vs=[X!3998, Y!3999], lhs=b_mul(c_inv(X!3998), b_mul(X!3998, Y!3999)), rhs=Y!3999, pf=None),
     RewriteRule(vs=[X!4000, Y!4001, Z!4002], lhs=b_mul(b_mul(X!4000, Y!4001), Z!4002), rhs=b_mul(X!4000, b_mul(Y!4001, Z!4002)), pf=None),
     RewriteRule(vs=[X!4003], lhs=b_mul(c_inv(X!4003), X!4003), rhs=a_e, pf=None),
     RewriteRule(vs=[X!4004], lhs=b_mul(a_e, X!4004), rhs=X!4004, pf=None)]

```python
T = smt.DeclareSort("AbstractGroup")
x,y,z = smt.Consts("x y z", T)
e = smt.Const("a_e", T)
inv = smt.Function("c_inv", T, T)
mul = smt.Function("b_mul", T, T, T)
kd.notation.mul.register(T, mul)

print(rw.lpo([x,y], inv(x * y),  inv(y) * inv(x)))
print(rw.lpo([x,y],  inv(y) * inv(x), inv(x * y)))
print([x,y], inv(x * y),  inv(y) * inv(x))
print(orient(smt.ForAll([x,y], inv(x * y) == inv(y) * inv(x)), order=rw.lpo))

inv.name() < mul.name()
```

    Order.GR
    Order.NGE
    [x, y] c_inv(b_mul(x, y)) b_mul(c_inv(y), c_inv(x))
    RewriteRule(vs=[X!4230, Y!4231], lhs=c_inv(b_mul(X!4230, Y!4231)), rhs=b_mul(c_inv(Y!4231), c_inv(X!4230)), pf=None)





    False

```python

from dataclasses import dataclass
@dataclass
class KBState:
    E: list[smt.BoolRef | smt.QuantifierRef]
    R: list[rw.RewriteRule]
```

```python

```
