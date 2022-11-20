---
layout: post
title: Unification
---

# First Order
First order is the good stuff.
The first part in straightforward. zip down two thing


Unification as a solving a set of equations. multiequations. We can extend unification to work on a system of equations. Doesn't really change much.

Unification as a proof system

# E-unification
It is a natural (?) question to ask how to unify equations in the presence of equations.

Unification is a raw equation solving algorithm. From our mathematics experience, we know that it isn't always easy to solve equations.

For associativity and commutativity, you can brute force expand into every combination of AC and use regular unification. This can be expensive.

A different approach is to try to normalize with respect to the underlying theory.

It is not clear to me that e-unification is a very good idea, since it seems pretty hard.

# Unification Hints

[Hints in unification Andrea Asperti, Wilmer Ricciotti, Claudio Sacerdoti Coen, and Enrico Tassi](https://www.cs.unibo.it/~sacerdot/PAPERS/tphol09.pdf) interesting paper. Describes how typeclasses and canonical structures can be put under a similar umbrella as extesnible unification mechanisms.




# Union Find

# Higher Order Unification
[efficient full higher order unification](https://arxiv.org/abs/2011.09507) zipperposition

[Unification Under a Mixed Prefix  - miller](https://repository.upenn.edu/cgi/viewcontent.cgi?article=1470&context=cis_reports)

equality over lambda terms is similar to universalc quantification
[unification of stlc as logic programming](https://www.lix.polytechnique.fr/Labo/Dale.Miller/papers/iclp91.pdf)
This is really interesting. Interpretting lambda unificatsion as a harrop program. This is similar to what I was suggesting in harrop egglog. forall ((x = y) -> p = q) -> \x p = \y q
structural vs generic equality.

Anti abstracting - if F is only applied to things it can't contain.

[Functions-as-constructors higher-order uniﬁcation:extended pattern uniﬁcatio](https://www.researchgate.net/publication/354972147_Functions-as-constructors_higher-order_unification_extended_pattern_unification)
DSP mathing. FCU unification 
hamana sol https://www.cs.gunma-u.ac.jp/~hamana/

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


# Pattern Matching
Arguably pattern matching should be it's own article.
Depending on which you see first, you may consider unification two way pattern matching or pattern matching as one way unification. I think pattern matching is the much simpler topic


# Resources

[adam gundry literate haskell](https://github.com/adamgundry/type-inference) "(for the free theory, abelian groups and higher-order pattern unification)" goes along with thesis

[higher order pattern unification exampel in elaboration zoo](https://github.com/AndrasKovacs/elaboration-zoo/blob/master/03-holes/Main.hs)
[Basic pattern unification in haskell](https://www.youtube.com/watch?v=trecCoxYbgM&ab_channel=Andr%C3%A1sKov%C3%A1cs)

What is the pattern fragment?
L_lambda subset
"existential variables" applied to unique bound variables.
reminscent of haskell pattern matching using distinct variables


http://conal.net/papers/elliott90.pdf conal elliott's thesis

[Jozef g explanation](https://github.com/jozefg/higher-order-unification/blob/master/explanation.md)

https://conservancy.umn.edu/bitstream/handle/11299/57268/Qi_umn_0130E_10758.pdf?sequence=1 lambda prolog implementation

See Miller and Nadathur book.







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

