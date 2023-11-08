---
layout: post
title: Unification
---
- [First Order](#first-order)
  - [Occurs Check](#occurs-check)
  - [Union Find](#union-find)
- [E-unification](#e-unification)
  - [Narrowing](#narrowing)
- [Unification Hints](#unification-hints)
- [Higher Order Unification](#higher-order-unification)
- [Nominal Unification](#nominal-unification)
- [Boolean Unification](#boolean-unification)
- [Pattern Matching](#pattern-matching)
- [Anti unification](#anti-unification)
- [Resources](#resources)

<https://en.wikipedia.org/wiki/Unification_(computer_science)>

# First Order

First order is the good stuff.
The first part in straightforward. zip down two thing

Unification as a solving a set of equations. multiequations. We can extend unification to work on a system of equations. Doesn't really change much.

Unification as a proof system (see term rewriting and all that or snyder baader)

[Efficient representations for triangular substitutions: A comparison in miniKanren](https://users.soe.ucsc.edu/~lkuper/papers/walk.pdf)
[Harrison unification](https://www.cl.cam.ac.uk/~jrh13/atp/OCaml/unif.ml)

```ocaml
(* Copyright (c) 2003-2007, John Harrison. (See "LICENSE.txt" for details.)  *)
let rec istriv env x t =
  match t with
    Var y -> y = x or defined env y & istriv env x (apply env y)
  | Fn(f,args) -> exists (istriv env x) args & failwith "cyclic";;

let rec unify env eqs =
  match eqs with
    [] -> env
  | (Fn(f,fargs),Fn(g,gargs))::oth ->
        if f = g & length fargs = length gargs
        then unify env (zip fargs gargs @ oth)
        else failwith "impossible unification"
  | (Var x,t)::oth | (t,Var x)::oth ->
        if defined env x then unify env ((apply env x,t)::oth)
        else unify (if istriv env x t then env else (x|->t) env) oth;;

let rec solve env =
  let env' = mapf (tsubst env) env in
  if env' = env then env else solve env';;

(* Unification reaching a final solved form (often this isn't needed).       *)
let fullunify eqs = solve (unify undefined eqs);;
```

[Correcting A Widespread Error in Unification Algorithms PETER NORVIG](https://norvig.com/unify-bug.pdf) [endersky blog](https://eli.thegreenplace.net/2018/unification/)
unification-fd
[a python package](https://github.com/pythological/unification)
[Conor mcbride first order unification by structural recursion](https://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.25.1516)

Cody comments unification is an instance of completion?

```python

def lookup(subst, x):
    if isinstance(x,int):
        if x in subst:
            return lookup(subst, subst[x])
        else:
            return x
    elif isinstance(x,tuple):
        return tuple(lookup(subst, y) for y in x)
    else:
        return x

def unify(t1,t2):
    subst = {}
    eqs = [(t1,t2)]
    while len(eqs) != 0:
        t1,t2 = eqs.pop()
    if isinstance(t1, int):
        if t1 == t2:
            continue
        else:
            if t1 in subst:
                eqs.append((lookup(subst,t1), t2))
            else:
                subst[t1] = t2
    elif isinstance(t1, int):
        if t2 in subst:
            return unify(t1, subst[t2])
        else:
            return {t2:t1}
    elif isinstance(t1, tuple) and isinstance(t2, tuple):
        if len(t1) != len(t2):
            raise Exception("mismatched tuple lengths")
        else:
            return unify(t1[1:], t2[1:]).unify(t1[0], t2[0])
    else:
        raise Exception("mismatched types")

```

```rust
enum Term {
    Var(usize),
    Const(String, Vec<usize>)
}

type RecTerm = Vec<Term>
type Subst = Vec<Term>

while let t1,t2 = eqs.pop() {
    match t1 {
        Var(x) => {
            if t1 == t2 {
                continue
            } else {
                if let Some(t) = subst.get(x) {
                    eqs.push((t, t2))
                } else {
                    subst.push(t2)
                }
            }
        }
        Const(f, args) => {
            if let Const(g, args2) = t2 {
                if f == g && args.len() == args2.len() {
                    for i in 0..args.len() {
                        eqs.push((args[i], args2[i]))
                    }
                } else {
                    panic!("mismatched constants")
                }
            } else {
                panic!("mismatched types")
            }
        }
    }
}

```

## Occurs Check

The occurs check is a curious phenomenon. Loopy infinite terms are not a priori disallowable.

## Union Find

# E-unification

It is a natural (?) question to ask how to unify equations in the presence of equations.

Unification is a raw equation solving algorithm. From our mathematics experience, we know that it isn't always easy to solve equations.

For associativity and commutativity, you can brute force expand into every combination of AC and use regular unification. This can be expensive.

A different approach is to try to normalize with respect to the underlying theory.

It is not clear to me that e-unification is a very good idea, since it seems pretty hard.

Unification modulo a group action is doable using the group union find. That's interesting.

## Narrowing

Unification under a convergent rewrite system. Unification modulo egraph is an example since egraphs are ground equation systems which can always be completed (into the egraph).

Narrowing and functional logic programming. See note on functional logic programming

# Unification Hints

[Hints in unification Andrea Asperti, Wilmer Ricciotti, Claudio Sacerdoti Coen, and Enrico Tassi](https://www.cs.unibo.it/~sacerdot/PAPERS/tphol09.pdf) interesting paper. Describes how typeclasses and canonical structures can be put under a similar umbrella as extesnible unification mechanisms.

# Higher Order Unification

Generate and test is the naive algorithm. What would generate and test look like for first order? We could enumerate every first order term

```prolog
%unify(const(F,Args))
%unify(var(X),const(F,Args))

% enumerate all first order terms of constants x/0 f/2
% term(X). Allow variable to stay ungrounded
term(const(x,[])).
term(const(f, [X,Y])) :- term(X), term(Y).

% guess (ground) and check. Using X metavariable as unguarded.
unify(T1,T2,[]) :- T1 == T2. % don't use `=`` ?
unify(T1,T2,[X | Vars]) :- term(X), unify(T1,T2,Vars).

unify-eqs([T1-T2 | Eqs], []) :- T1 == T2, unify-eqs(Eqs, []). % really map(==, Eqs)

```

This is bottom up E-unification.

The fact we're working in simply typed is important? It guarantees normal forms and gives clues to the appropriate shapes.

Enumerate all "normal" forms. I need to lookup which normal forms I mean. I've always been shaky

```
% normal(Tm , Type).
normal(lam(E)  , arr(A,B)) :- normal(E, B, [A | Ctx] ).
normal( var(N), Ty, Ctx) :- lookup(N,Ty,Ctx).
normal(app(F,X), Ty, Ctx) :- normal(F, arr(A,B), Ctx), normal(X, A, Ctx).

unify() :- guess(), eval(), check().

```

Eta long form.

Huet's algorithm takes advantage of some observations.

Gilles dowek - handbook automated reasning article <https://dl.acm.org/doi/abs/10.5555/778522.778525>

Huet's paper

Graham's carnap <https://philarchive.org/archive/LEACAO-2v1> <https://github.com/Carnap/Carnap/blob/master/Carnap/src/Carnap/Core/Unification/Huet.hs>

Lambda kanren <https://www.youtube.com/watch?v=iUZasa7wzW4&ab_channel=ACMSIGPLAN> <http://minikanren.org/workshop/2021/minikanren-2021-final8.pdf>

[efficient full higher order unification](https://arxiv.org/abs/2011.09507) zipperposition

[Unification Under a Mixed Prefix  - miller](https://repository.upenn.edu/cgi/viewcontent.cgi?article=1470&context=cis_reports)

equality over lambda terms is similar to universalc quantification
[unification of stlc as logic programming](https://www.lix.polytechnique.fr/Labo/Dale.Miller/papers/iclp91.pdf)
This is really interesting. Interpretting lambda unificatsion as a harrop program. This is similar to what I was suggesting in harrop egglog. forall ((x = y) -> p = q) -> \x p = \y q
structural vs generic equality.

Anti abstracting - if F is only applied to things it can't contain.

[Functions-as-constructors higher-order uniﬁcation:extended pattern uniﬁcatio](https://www.researchgate.net/publication/354972147_Functions-as-constructors_higher-order_unification_extended_pattern_unification)
DSP mathing. FCU unification
hamana sol <https://www.cs.gunma-u.ac.jp/~hamana/>

What is the problem with pure alpha matching? de Bruijn indexing makes it feel like it should just be ordinary structural matching.
Here's the problem though. What is the scope of the pattern variables?
If you only use the pattern variable once, maybe not a problem. Ok linear patterns. But then if you're matching in order to instantiate this variable into something

match `\ F` with `\0`. If we make `F = 0` that's ok
`\ F F` with `\ 0 0` is ok also becaoue both instances of F are in scope of the same thing
The rewrite rule
`\ F -> \ F` is highly fishy though.  
Perhaps it is best to use named variables
rule : `\x F -> \y F`
matched with `\z. z`
First off match fails since `\x. _ != \z. _`
ok but then what about alpha renaming matchee to
`\x. x`
Then we get `F = x`. Fine.
But then the other side gets \y. x where x wasn't even in scope?

If everything is under the binder somehow (and it isn't entirely clear what this means. We internalize rules as bodies of lambdas? Rules here are not implications. Maybe they are pseudo equalities?)
\x. (F -> F)

Logically, the pattern variables could be considered existentially quantified on the exterior of the rule
ex F. \x F -> \y F. This is possibly to match. F can only match things that already are around (in the signature) as the point of ex F.

Raising

[A Logic Programming Language with Lambda-Abstraction,  Function Variables, and Simple Unification - Miller](http://citeseerx.ist.psu.edu/viewdoc/download;jsessionid=FDA9E2A5EE322005C1B35D2394E6B3CA?doi=10.1.1.54.8958&rep=rep1&type=pdf)

[Higher-Order Dynamic Pattern Unification for Dependent Types and Records - Andreas Abel and Brigitte Pientka](https://www.cse.chalmers.se/~abela/unif-sigma-long.pdf)

MLTS

[adam gundry literate haskell](https://github.com/adamgundry/type-inference) "(for the free theory, abelian groups and higher-order pattern unification)" goes along with thesis
[A tutorial implementation of dynamic pattern unification](https://adam.gundry.co.uk/pub/pattern-unify/) gundry mcbride

[higher order pattern unification exampel in elaboration zoo](https://github.com/AndrasKovacs/elaboration-zoo/blob/master/03-holes/Main.hs)
[Basic pattern unification in haskell](https://www.youtube.com/watch?v=trecCoxYbgM&ab_channel=Andr%C3%A1sKov%C3%A1cs)

What is the pattern fragment?
L_lambda subset
"existential variables" applied to unique bound variables.
reminscent of haskell pattern matching using distinct variables

<http://conal.net/papers/elliott90.pdf> conal elliott's thesis

[Jozef g explanation](https://github.com/jozefg/higher-order-unification/blob/master/explanation.md)

<https://conservancy.umn.edu/bitstream/handle/11299/57268/Qi_umn_0130E_10758.pdf?sequence=1> lambda prolog implementation

See Miller and Nadathur book.

# Nominal Unification

See nominal logic notes

# Boolean Unification

<https://cs.au.dk/~magnusm/papers/oopsla20/paper_b.pdf> using it in Flix type checker

successive variable elimiations
lowenheim's algorithm
<https://web.cs.wpi.edu/~dd/publications/unif19.pdf> coq

[boolean unification, the story so far](https://www.sciencedirect.com/science/article/pii/S0747717189800136)

# Pattern Matching

Arguably pattern matching should be it's own article.
Depending on which you see first, you may consider unification two way pattern matching or pattern matching as one way unification. I think pattern matching is the much simpler topic

# Anti unification

<https://en.wikipedia.org/wiki/Anti-unification_(computer_science)>
Least general anti-unifier

eery variety of uniifcation has it's anti varierty: higher order, E, nominal

[One or Nothing: Anti-unification over the Simply-Typed Lambda Calculus](https://arxiv.org/abs/2207.08918)
babble egg stuff
ruler i think uses anti-unification
inductive logic programming

# Resources

[Unifcation theory Franz Baader Wayne Snyder - handbook of automated reasoning](https://www.cs.bu.edu/fac/snyder/publications/UnifChapter.pdf)

<https://hal.archives-ouvertes.fr/hal-02123709/document> uniifcation modulo reverse. hmm but this says it's really hard
related to unification modulo group action? <https://youtu.be/35xgRnWsUsg?t=1929>
and the generalized union find?

Tiark Rompf nbe?

<script>

let lam = (v1,b1) => ({tag : "lam", v : v1, b : b1});
let app = (f,x) => ({tag : "app", f : f, x : x});
let lvar = (x) => ({tag : "lvar", name : x});

let id = lam("x", lvar("x"));
console.log(id);
// we could use just string as variables.

function eval(l, env) {
    switch(l.tag){
        case "lam":
            return l;
        case "app" :
            let f = eval(l.f, env);
            let x = eval(l.x, env);
            let env2 = {...env};
            env2[f.v] = x;
            return eval( f.b, env2) ;
        case "lvar":
            return env[l.name];
    }
}

function pretty(l){
        switch(l.tag){
        case "lam":
            return `\\${l.v} -> ${pretty(l.b)}`;
        case "app" :
            return `${pretty(l.f)} ${pretty(l.x)}`
        case "lvar":
            return l.name;
    }
}

function reflect(l, env) {
    switch(l.tag){
        case "lam":
            return x => {
                let env2 = {...env};
                env2[l.v] = x;
                return reflect(l.b, env2);
              };
        case "app" :
            let f = reflect(l.f, env);
            let x = reflect(l.x, env);
            return f(x);
        case "lvar":
            return env[l.name];
    }
}
// https://stackoverflow.com/questions/5999998/check-if-a-variable-is-of-function-type
function isFunction(functionToCheck) {
 return functionToCheck && {}.toString.call(functionToCheck) === '[object Function]';
}

var counter = 0;
function reify(l) {
    if(isFunction(l)){
        counter++;
        return lam(counter, reify(l(lvar(counter))));
    }
    return l;
}

fst = lam("x", lam("y", lvar("x")));
snd = lam("x", lam("y", lvar("y")));
comp = lam("f", lam("g", app(lvar("f"), lvar("g"))    ));

nbe = (l) => reify(reflect(l, {}));
print = (l) => console.log(pretty(l))
/*

console.log(pretty((eval(id,{}))));
console.log(pretty((eval(app(id,id),{}))));
print(eval( app(id,app(id,id)), {} ));
pretty(nbe( app(id,app(id,id))));
*/
//pretty(( id));
console.log(reify(reflect(id, {})));
console.log(nbe(id));
print(nbe(id));
print( nbe(app(id,app(id,id) )) );
print( nbe(comp) );

</script>
