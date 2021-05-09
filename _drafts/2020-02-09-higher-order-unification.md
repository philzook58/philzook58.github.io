---
author: philzook58
layout: post
title: Unification
---
What is the pattern fragment?
L_lambda subset
"existential variables" applied to unique bound variables.
reminscent of haskell pattern matching using distinct variables


http://conal.net/papers/elliott90.pdf conal elliott's thesis

https://github.com/jozefg/higher-order-unification/blob/master/explanation.md Jozef g

https://conservancy.umn.edu/bitstream/handle/11299/57268/Qi_umn_0130E_10758.pdf?sequence=1 lambda prolog implementation


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

