---
author: Philip Zucker
date: 2021-03-12
layout: post
title: Rewriting Monoidal Categories in the Browser with Egg
tags:
- category theory
- rust
---

<script type="module">
      import init, { simplify } from '/assets/eggland3.js';

      async function run() {
        await init();
        let start = "(. (id a) (. (id a) (id a)))"
        const result = simplify(start);
        console.log(`${start} ==> ${result}`);
      }

      run();

      function simp(){
        init();
        let start = document.getElementById("querybox").value;
        const result = simplify(start);
        console.log(`${start} ==> ${result}`);
        document.getElementById("output").innerHTML = result;
      }
      window.simp = simp
</script>


<script>



</script>

<label for="querybox"> <b>Query:</b> </label>
<textarea id="querybox" style="width:100%" rows="4">
 (. (om (dup a) (dup b))
    (om (id a) (. (om (swap a b) (id b)) 
                  (om (del b) (om (del a) (id b))))))
</textarea>
<button onclick="simp()">Simplify</button>


<div id="sequent"></div>
<label for="output"><b>Output:</b></label>
<div id="output"></div>

### Other Example Queries:
- `(. (id a) (id a))`
- `(om (id a) (id b))`
- `(. (dup a) (swap a a))`
- `(dom (type (id a)))`
- `(cod (type (dup a)))`
- `(. (swap a b) (. (swap b a) (swap a b)))` 
### Legend
- `(id a)` - identity morphism for object a
- `(om f g)` - monoidal product of morphisms $$f \otimes  g$$
- `(oo a b)` - monoidal product of objects $$ a \otimes b$$
- `(. f g)` - composition of `f : hom(a,b)` and `g: hom(b,c)` resulting in `hom(a,c)`.
- `munit` - unit object of monoidal product
- `(swap a b)` - Braid objects a and b. $$\sigma_{a b}$$
- `(dup a)` - copy object a $\Delta(a)$
- `(del a)` - delete object a $\diamond(a)$
- `(pair f g)` - send input `a` off to both f and g in parallel
- `(proj1 a b)` - project off `a` from $a \otimes b$
- `(proj2 a b)` - project off `b` from $a \otimes b$
- Auxiliary things: `type`, `hom`, `dom` , `cod`, `ob`


I have been finding it quite pleasant to find ways to make things run in the browser. It makes for a much more compelling blog post I think. If you need someone to install your thing, there is a very low chance they'll take the effort to see it working. And that is where the magic is.

This is a follow on post to <http://www.philipzucker.com/metatheory-progress/>. For a more detailed discussion of the tricks involved in the rule system, see that post. In essence, I'm taking the same guarded rewrite system on egraphs and translating it to use [egg](https://egraphs-good.github.io/), which [Metatheory.jl](https://github.com/0x0f0f0f/Metatheory.jl) borrows heavily from in terms of it's implementation. Egg is still to my knowledge more performant (although Alessandro makes great strides every day), easier to compile to [wasm](https://rustwasm.github.io/book/) for the web, plus it is a good excuse to write some rust.

Egg is straightforward enough to use <https://docs.rs/egg/0.6.0/egg/tutorials/>. First you define your language (or you can use the built in generic SymbolLang, presumably at a performance hit.)
There is a nice macro for this. What is it doing? Well it's defining a parser and an ordinary enum. Don't forget the trailing comma!

Here is a language define for my categorical constructors. I renamed everything away from unicode symbols so they would be easier to type. 

```rust
use egg::{*, rewrite as rw};
use wasm_bindgen::prelude::*;
use std::time::Duration;

define_language! {
    enum CatLanguage {
        // string variant with no children
        "id" = IdMorph(Id),
        "om" = OTimesM([Id; 2]),
        "oo" = OTimesO([Id; 2]),
        "." = Comp([Id; 2]),
        "munit" = MUnit,
        "swap" = Sigma([Id;2]),
        "type" = Type(Id),
        "dom" = Dom(Id),
        "cod" = Cod(Id),
        "hom" = Hom([Id;2]),
        "ob" = Ob,
        "dup" = Dup(Id),
        "del" = Del(Id),
        "pair" = Pair([Id;2]),
        "proj1" = Proj1([Id;2]),
        "proj2" = Proj2([Id;2]),
        Symbol(Symbol),

    }
}
```

Then you define your rewrite rules. This was significantly aided by me having already written an egg translator for MetaTheory rules <https://gist.github.com/philzook58/29244c7d44065d81b53f902c590ae90e>. Both Egg and Metatheory store rules in a fairly straightforward data structure.

```rust
    let mut rules : Vec<Rewrite<CatLanguage, ()>> = vec![
        vec![rw!( "dom(hom(a, b)) => a" ; "(dom (hom ?a ?b))" => "?a" )],
        vec![rw!( "cod(hom(a, b)) => b" ; "(cod (hom ?a ?b))" => "?b" )],
        vec![rw!( "type(id(a)) => hom(a, a)" ; "(type (id ?a))" => "(hom ?a ?a)" )],
        vec![rw!( "type(f . g) => hom(dom(type(f)), cod(type(g)))" ; "(type (. ?f ?g))" => "(hom (dom (type ?f)) (cod (type ?g)))" )],
        vec![rw!( "type(f om g) => hom(dom(type(f)) oo dom(type(g)), cod(type(f)) oo cod(type(g)))" ; "(type (om ?f ?g))" => "(hom (oo (dom (type ?f)) (dom (type ?g))) (oo (cod (type ?f)) (cod (type ?g))))" )],
        vec![rw!( "type(a oo b) => :ob" ; "(type (oo ?a ?b))" => "ob" )],
        vec![rw!( "type(munit()) => :ob" ; "(type munit)" => "ob" )],
        vec![rw!( "type(swap(a, b)) => hom(a oo b, b oo a)" ; "(type (swap ?a ?b))" => "(hom (oo ?a ?b) (oo ?b ?a))" )],
        vec![rw!( "type((del)(a)) => hom(a, munit())" ; "(type (del ?a))" => "(hom ?a munit)" )],
        vec![rw!( "type(dup(a)) => hom(a, a oo a)" ; "(type (dup ?a))" => "(hom ?a (oo ?a ?a))" )],
        vec![rw!( "type(pair(f, g)) => hom(dom(type(f)), cod(type(f)) oo cod(type(g)))" ; "(type (pair ?f ?g))" => "(hom (dom (type ?f)) (oo (cod (type ?f)) (cod (type ?g))))" )],
        vec![rw!( "type(proj1(a, b)) => hom(a oo b, a)" ; "(type (proj1 ?a ?b))" => "(hom (oo ?a ?b) ?a)" )],
        vec![rw!( "type(proj2(a, b)) => hom(a oo b, b)" ; "(type (proj2 ?a ?b))" => "(hom (oo ?a ?b) ?b)" )],
        vec![rw!( "f . id(b) => f" ; "(. ?f (id ?b))" => "?f" )],
        vec![rw!( "id(a) . f => f" ; "(. (id ?a) ?f)" => "?f" )],
        vec![rw!( "a oo munit() => a" ; "(oo ?a munit)" => "?a" )],
        vec![rw!( "munit() oo a => a" ; "(oo munit ?a)" => "?a" )],
        rw!( "f . (g . h) == (f . g) . h" ; "(. ?f (. ?g ?h))" <=> "(. (. ?f ?g) ?h)" ),
        vec![rw!( "id(munit()) om f => f" ; "(om (id munit) ?f)" => "?f" )],
        vec![rw!( "f om id(munit()) => f" ; "(om ?f (id munit))" => "?f" )],
        rw!( "a oo (b oo c) == (a oo b) oo c" ; "(oo ?a (oo ?b ?c))" <=> "(oo (oo ?a ?b) ?c)" ),
        rw!( "f om (h om j) == (f om h) om j" ; "(om ?f (om ?h ?j))" <=> "(om (om ?f ?h) ?j)" ),
        rw!( "id(a oo b) == id(a) om id(b)" ; "(id (oo ?a ?b))" <=> "(om (id ?a) (id ?b))" ), 
        vec![rw!( "(f . g) om (p . q) => (f om p) . (g om q)" ; "(om (. ?f ?g) (. ?p ?q))" => "(. (om ?f ?p) (om ?g ?q))" )],
        rw!( "swap(a, b) . swap(b, a) == id(a oo b)" ; "(. (swap ?a ?b) (swap ?b ?a))" <=> "(id (oo ?a ?b))" ),
        rw!( "(swap(a, b) om id(c)) . (id(b) om swap(a, c)) == swap(a, b oo c)" ; "(. (om (swap ?a ?b) (id ?c)) (om (id ?b) (swap ?a ?c)))" <=> "(swap ?a (oo ?b ?c))" ),
        rw!( "(id(a) om swap(b, c)) . (swap(a, c) om id(b)) == swap(a oo b, c)" ; "(. (om (id ?a) (swap ?b ?c)) (om (swap ?a ?c) (id ?b)))" <=> "(swap (oo ?a ?b) ?c)" ),
        rw!( "swap(a, munit()) == id(a)" ; "(swap ?a munit)" <=> "(id ?a)" ),
        rw!( "swap(munit(), a) == id(a)" ; "(swap munit ?a)" <=> "(id ?a)" ),
       
        vec![rw!( "swap(munit(), munit()) => id(munit() oo munit())" ; "(swap munit munit)" => "(id (oo munit munit))" )],
        rw!( "dup(a) . ((del)(a) om id(a)) == id(a)" ; "(. (dup ?a) (om (del ?a) (id ?a)))" <=> "(id ?a)" ),
        rw!( "dup(a) . (id(a) om (del)(a)) == id(a)" ; "(. (dup ?a) (om (id ?a) (del ?a)))" <=> "(id ?a)" ),
        rw!( "dup(a) . swap(a, a) == dup(a)" ; "(. (dup ?a) (swap ?a ?a))" <=> "(dup ?a)" ),
        rw!( "(dup(a) om dup(b)) . ((id(a) om swap(a, b)) om id(b)) == dup(a oo b)" ; "(. (om (dup ?a) (dup ?b)) (om (om (id ?a) (swap ?a ?b)) (id ?b)))" <=> "(dup (oo ?a ?b))" ),
        rw!( "dup(a) . (dup(a) om id(a)) == dup(a) . (id(a) om dup(a))" ; "(. (dup ?a) (om (dup ?a) (id ?a)))" <=> "(. (dup ?a) (om (id ?a) (dup ?a)))" ),
        rw!( "(del)(a oo b) == (del)(a) om (del)(b)" ; "(del (oo ?a ?b))" <=> "(om (del ?a) (del ?b))" ),
        rw!( "dup(munit()) == id(munit())" ; "(dup munit)" <=> "(id munit)" ),
        rw!( "(del)(munit()) == id(munit())" ; "(del munit)" <=> "(id munit)" ),
        vec![rw!( "pair(f, k) => dup(dom(type(f))) . (f om k)" ; "(pair ?f ?k)" => "(. (dup (dom (type ?f))) (om ?f ?k))" )],
        rw!( "proj1(a, b) == id(a) om (del)(b)" ; "(proj1 ?a ?b)" <=> "(om (id ?a) (del ?b))" ),
        rw!( "proj2(a, b) == (del)(a) om id(b)" ; "(proj2 ?a ?b)" <=> "(om (del ?a) (id ?b))" ),
        vec![rw!( "f . (del)(b) => (del)(dom(type(f)))" ; "(. ?f (del ?b))" => "(del (dom (type ?f)))" )],
        vec![rw!( "f . dup(b) => dup(dom(type(f))) . (f om f)" ; "(. ?f (dup ?b))" => "(. (dup (dom (type ?f))) (om ?f ?f))" )],
        vec![rw!( "dup(a) . (f om f) => f . dup(cod(type(f)))" ; "(. (dup ?a) (om ?f ?f))" => "(. ?f (dup (cod (type ?f))))" )],
                
        ].concat();
```


The things I didn't auto translate were the guarded rules. These I did by hand. Egg has a convenient `ConditionEqual` that basically does that guards I need, only allowing a rule to fire if the two patterns in the `ConditionEqual` live in the same EClass.

```rust
        let fcod : Pattern = "(cod (type ?f))".parse().unwrap();
        let gdom : Pattern = "(dom (type ?g))".parse().unwrap();
        let pcod : Pattern = "(cod (type ?p))".parse().unwrap();
        let qdom : Pattern = "(dom (type ?q))".parse().unwrap();
        rules.push(rw!(
            "interchange";
            "(. (om ?f ?p) (om ?g ?q))" => "(om (. ?f ?g) (. ?p ?q))"
            if ConditionEqual(fcod, gdom)
            if ConditionEqual(pcod, qdom)
        )); 

        rules.push(rw!(
            "(f ⊗ₘ h) ⋅ σ(a, b) ";
            "(. (om ?f ?h) (swap ?a ?b))" => "(. (swap (dom (type ?f)) (dom (type ?h))) (om ?h ?f))"
            if ConditionEqual::parse("(cod (type ?f))", "?a")
            if ConditionEqual::parse("(cod (type ?h))", "?b")
        )); 

        rules.push(rw!(
            "σ(c, d) ⋅ (h ⊗ₘ f) ";
            "(. (swap ?c ?d) (om ?h ?f) )" => "(. (om ?f ?h) (swap (cod (type ?f)) (cod (type ?h))) )"
            if ConditionEqual::parse("(dom (type ?f))", "?c")
            if ConditionEqual::parse("(cod (type ?h))", "?d")
        )); 

        rules.push(rw!(
            " Δ(a) ⋅ (f ⊗ₘ k)";
            "(. (dup ?a) (om ?f ?k))" => "(pair ?f ?k)"
            if ConditionEqual::parse("(dom (type ?f))", "?a")
            if ConditionEqual::parse("(dom (type ?k))", "?a")
        )); 

```

Then you can actually run a query. The easiest way to do this is via the `Runner` interface.

```rust
        let start = "(. (id a) (id a))".parse().unwrap();
        let mut runner = Runne r::default().with_expr(&start)
            // More options here https://docs.rs/egg/0.6.0/egg/struct.Runner.html
            .with_iter_limit(400)
            .with_node_limit(2_000_000)
            .with_time_limit(Duration::new(60,0))
            .run(&rules);
        runner.print_report();
        let mut extractor = Extractor::new(&runner.egraph, AstSize);
        let (best_cost, best_expr) = extractor.find_best(runner.roots[0]);
        println!("best cost: {}, best expr {}", best_cost, best_expr);
```

That's pretty much it.

Compiling to the web was pretty straightforward. i wrapped all the above in a function that takes a query `&str` and returns the `best_expr` `String`.  Typically, easy mode for compiling to javascript is to use functions that take and return non weird data types and don't try to directly interact with the DOM. Then a little javascript shim can do the rest, taking the query from the textbox, firing off the solver, and printing the result.

<https://rustwasm.github.io/docs/wasm-bindgen/examples/without-a-bundler.html>
`wasm-pack build --target web`

One hiccup I had was a strange error about a missing env. <https://github.com/rustwasm/wasm-bindgen/issues/2215> was the same problem
Then, adding the following to my Cargo.toml solved my issue:
`parking_lot = { version = "0.11.1", features = ["wasm-bindgen"]}`
Me dunno. Don't question it.

### Bits and Bobbles

- Rust code of post <https://gist.github.com/philzook58/b6779386a3df4aa2e033b5c804ee7547>

- If you give it ill typed input, it will give you junk out. There are no guard rails as of yet

- I left egg on the lowest settings. We could really pump up the solve time, node count, etc if you want it to try super seriously.

- Not all rules can fire with opaque morphisms `f`. I did not give you enough tools to define the types of morphisms.

- It also wouldn't have been hard to allow you to add user defined relations like `f . g = h` and others, but I got lazy. All that is required is to push them these simple equations into the egraph before sending it off to the runner. Designing how to get that back and forth between javascript is a bit annoying.

- Here's a fun idea. Since equivalence classes of terms are string diagrams, it makes sense to output an egraph visualization with eclasses labelled by string diagrams. The enodes describe operations that compose string diagrams, composition, horizontal juxtaposition, etc. This is an example showing some composition operations.

![](/assets/eclass-string.png) 
Compare this to the diagrams egg produces like the below.
![](/assets/egraphs.svg) 

- It would be nice to have sort of an SMTLib style CLI and/or api to Egg. Using Rust is kind of a barrier to entry. It also sounds kind of like a fun project  