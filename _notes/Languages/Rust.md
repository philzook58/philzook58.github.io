---
author: philzook58
comments: true
date: 2020-06-25 20:45:34+00:00
layout: post
link: https://www.philipzucker.com/?p=1849
slug: Rust
title: Rust
wordpress_id: 1849
---

- [Assembly](#assembly)
- [Unsafe](#unsafe)
- [MIR](#mir)
- [Arenas](#arenas)
- [Lifetimes](#lifetimes)
- [Globals Variables](#globals-variables)
- [Formal methods](#formal-methods)
  - [Kani](#kani)
  - [RustBelt](#rustbelt)
  - [RustHorn](#rusthorn)
  - [RustHornBelt](#rusthornbelt)
  - [Prusti](#prusti)
  - [Aeneas](#aeneas)
  - [Creusot](#creusot)
- [Macros](#macros)
  - [Declarative macros aka macro\_rules](#declarative-macros-aka-macro_rules)
  - [Proc Macros](#proc-macros)
  - [Hygiene](#hygiene)
- [Optimization](#optimization)
- [Webassembly](#webassembly)
- [Translation From Legacy](#translation-from-legacy)
- [Code](#code)
  - [Timely Dataflow](#timely-dataflow)
  - [Ascent](#ascent)
- [Traits](#traits)
  - [GAT](#gat)
- [Concurrency](#concurrency)
- [Async](#async)
- [Resources](#resources)
- [warn clippy will give advice](#warn-clippy-will-give-advice)

See Also:

- Prolog and Datalog for Polonius and Chalk info

```rust
fn main(){
    println!("hello world!");
}
```

```rust

fn main(){
    let foo = |x : i64| {x + 1};
    let i = 7;
    fn foo2(x : i64) -> i64 {
        x + i
    }
    dbg!(foo2(4));
}

```

```python
def my_func():
    a = 1
    return lambda: a

print(my_func()())

funcs = ([(lambda a: a*x) for x in range(10)])

for func in funcs:
    print(func(5))
    print(id(func))
```

# Assembly

inline assembly <https://doc.rust-lang.org/reference/inline-assembly.html>

[Rust to Assembly: Understanding the Inner Workings of Rust](https://www.eventhelix.com/rust/)

cargo asm
`cargo asm lib_crate::bar::double_n --rust`

<https://www.reddit.com/r/rust/comments/u3g0ih/new_crate_announcement_cargoshowasm/> cargo-show-asm

<https://darkcoding.net/software/underrust-rust-assembly-output/>
<https://crates.io/crates/rustfilt> rustfilt demangles symbols

godbolt

<https://blog.logrocket.com/interacting-with-assembly-in-rust/> interacting with assembly in rust

```bash
echo "
const NAMES: [&'static str; 1] = [
    \"Kaladin\"
];

fn main() {
    roll_call();
}

pub fn roll_call() {
    println!(\"SOUND OFF\");
    for name in NAMES.iter() {
        println!(\"{}: HERE!\", name);
    }
    let num_present = NAMES.len();
    println!(\"All {} accounted for!\", num_present);
}
" > /tmp/rustex.rs
rustc --emit asm -C llvm-args=-x86-asm-syntax=intel /tmp/rustex.rs -o /tmp/rustex.s
cat /tmp/rustex.s

```

`RUSTFLAGS="--emit asm -C llvm-args=-x86-asm-syntax=intel" cargo build`

# Unsafe

<https://doc.rust-lang.org/reference/unsafety.html>
<https://doc.rust-lang.org/book/ch19-01-unsafe-rust.html>
<https://doc.rust-lang.org/nightly/nomicon/>

rawpointers, ffi, unions, mutable statics, unsafe traits

<https://doc.rust-lang.org/std/ptr/index.html>

<https://rustmagazine.org/issue-3/understand-unsafe-rust/>

Miri reference interpreter <https://github.com/rust-lang/miri>

```bash
rustup +nightly component add miri
```

provnenace. <https://github.com/rust-lang/rfcs/pull/3559>  <https://github.com/rust-lang/rust/issues/95228> strict provenance <https://faultlore.com/blah/fix-rust-pointers/> <https://www.youtube.com/watch?v=d8hd_uv3Gvg&ab_channel=Rust>

stacked borrows. tree borrows
<https://www.ralfj.de/blog/2022/07/02/miri.html> The last two years in Miri
<https://www.youtube.com/watch?v=svR0p6fSUYY> Unsafe Rust and Miri by Ralf Jung - Rust Zürisee June 2023
<https://research.ralfj.de/thesis.html> Understanding and Evolving the Rust Programming Language

```bash
echo "
use std::ptr;
fn evil() {
    {unsafe {
        let x = 0i32;
        let ptr = ptr::from_ref(&x);
        ptr.offset(1).read();
    }}
}
fn main(){evil()} " > /tmp/evil.rs
rustc +nightly -Zmiri-track-raw-pointers /tmp/evil.rs

```

`hint::unreachable_unchecked()` <https://doc.rust-lang.org/std/hint/fn.unreachable_unchecked.html>

<https://doc.rust-lang.org/std/mem/union.MaybeUninit.html>

<https://doc.rust-lang.org/std/slice/fn.from_raw_parts.html>

<https://www.youtube.com/watch?v=9E2v8pCUc48&ab_channel=Let%27sGetRusty>

# MIR

<https://rustc-dev-guide.rust-lang.org/mir/index.html>

<https://github.com/rust-lang/a-mir-formality>
<https://github.com/rust-lang/project-stable-mir> stable mir

miri - see unsafe

# Arenas

Vec arena
bumpalo
typed-arena

# Lifetimes

# Globals Variables

[Rust global variables demystified](https://morestina.net/blog/1774/rust-global-variables-demystified)
[Idiomatically use global variables in rust](https://www.sitepoint.com/rust-global-variables/)
`static` which may not mean what you t5hink

Lazy and once_cell are in nightly rust and std <https://github.com/rust-lang/rust/issues/74465>

# Formal methods

<https://blog.logrocket.com/5-automatic-verification-tools-rust/>

<https://arxiv.org/abs/2311.08862>  Verification of a Rust Implementation of Knuth's Dancing Links using ACL2

## Kani

<https://model-checking.github.io/kani/getting-started.html>
<https://blog.logrocket.com/using-kani-write-validate-rust-code-chatgpt/>
<https://github.com/model-checking/kani>

```bash
cargo install --locked kani-verifier
cargo kani setup
```

```bash
echo "
// File: test.rs
#[kani::proof]
fn main() {
    assert!(1 == 2);
} " > /tmp/test.rs
kani /tmp/test.rs
```

## RustBelt

[RustBelt: Securing the Foundations of the Rust Programming Language](https://bobkonf.de/2022/dreyer.html)  

## RustHorn

Prophetic encoding. Mutable borrows are modelled as pairs of current and final values.

## RustHornBelt

<https://www.lri.fr/~xldenis/paper/rusthornbelt.pdf>

## Prusti

## Aeneas

<https://arxiv.org/abs/2206.07185>
<https://github.com/AeneasVerif/aeneas>

## Creusot

[creusat](https://news.ycombinator.com/item?id=31780128) <https://twitter.com/xldenis/status/1537578878364921856?s=20&t=Id3zoB1xCWLA5QQIrPNHVA>
<https://hal.inria.fr/hal-03526634/document>
built in why3
pearlite - specification language

This toggle thing is very surpising to me
[cyclone](https://pling.jondgoodwin.com/post/cyclone/) Interesting breakdown of some history
[parallel rust](https://parallel-rust-cpp.github.io/)

```rust
fn toggle<T>(t : bool, a : &mut T, b : &mut T) -> &mut T {
    if t { a} else {b}
}
```

# Macros

[updated little book of macros](https://github.com/veykril/tlborm/)

[syn]
[quote] for quasiquoting

## Declarative macros aka macro_rules

## Proc Macros

## Hygiene

I think macro_rules! is hygienic

Hygiene is dealing with what environment variables in your macro refer to. The sort of easy version is to just paste in the code in the call site of the macro.

This kind of isn't what you want though. You almost certainly want to refer to libraries in scope at macro definition. If for example a function `foo` gets shadowed at the callsite.

# Optimization

flamegraph <https://github.com/flamegraph-rs/flamegraph>
rust heap profiler dhat

Make pools to improve performance?

# Webassembly

[https://rustwasm.github.io/](https://rustwasm.github.io/) The general webassembly site

There is a web assembly tutorial

[https://rustwasm.github.io/docs/book/introduction.html](https://rustwasm.github.io/docs/book/introduction.html)

wasm-bindgen is a crate that auto builds javacript bindings given a macro annotation. This guide has the most stuff in it. web-sys and js-sys give useful bindings to things.

[https://rustwasm.github.io/docs/wasm-bindgen/](https://rustwasm.github.io/docs/wasm-bindgen/)

wasm-pack is a tool for building rust to webassembly projects

[https://rustwasm.github.io/docs/wasm-pack/introduction.html](https://rustwasm.github.io/docs/wasm-pack/introduction.html)

println! does not work unfortunately. You need to custom bind to console.log or use the web-sys bindings. It's kind of a pain in the ass [https://rustwasm.github.io/docs/wasm-bindgen/examples/console-log.html](https://rustwasm.github.io/docs/wasm-bindgen/examples/console-log.html)

[https://www.nalgebra.org/](https://www.nalgebra.org/) nalgebra and ndarray are crates that give matrix and numerical stuff. They can bind to blas but also a lot of functionality is in pure rust, so it can be compiled to the web.

Getting a webpage up that runs webassembly seems like an involved process. I thnk there is some preference to using web-pack. There is a lot of modern javascript features being used that I'm not familiar with. Guess I'm a grandpa. [https://javascript.info/](https://javascript.info/) Most importantly is the ES6 module system. Also some examples use await/async syntax to initialize the rust built webassembly.  [https://rustwasm.github.io/docs/wasm-bindgen/examples/without-a-bundler.html](https://rustwasm.github.io/docs/wasm-bindgen/examples/without-a-bundler.html)

Serde seems like a useful route to getting stuff into and out of javascript. It is a serialization deserialization library.

# Translation From Legacy

<https://cpp-rust-assisted-migration.gitlab.io/> C++ to rust
<https://github.com/newca12/awesome-rust-formalized-reasoning>
<https://galois.com/blog/2023/09/using-gpt-4-to-assist-in-c-to-rust-translation/>
<https://c2rust.com/>

# Code

## Timely Dataflow

This stuff is scattered over both datalog and databases notes.

[shipping puzzle in differential dataflow](https://www.nikolasgoebel.com/2018/12/22/shipping-puzzle.html)
Frank mcsherry also has sudoku examples on youtube

[Life in Differential Dataflow](https://materialize.com/life-in-differential-dataflow/) blog post. interesecting lists. fizzbuzz. Game of life.

<https://materialize.com/blog>

Timely associates timestamps with data. That enables more complex operations. A similar thing occurs with computer state, where the program counter exists and enables more powerful programs than pure combinatorial circuitry (~dataflow programming).

Timestamps are extending from simple integers into more complex partially ordered thingies. This may be familiar from lamport clocks for example, but also makes sense from a loopy scope perspective.

Just as importantly you need a notion of frontier or watermark. Things tha are accumulating data may need to know nothing else may come in. How do you describe "nothing else may come in" in a complex notion of time? Antichains is apparently an answer.

modelling purely functionally

frontier -> frontier - can/should be static matrix? Port by port?
[(T, x)] -> [(T, y)]

```rust
// cargo-deps: timely
extern crate timely;

use timely::dataflow::operators::*;

fn main() {
    timely::example(|scope| {
        (0..10).to_stream(scope)
               .inspect(|x| println!("seen: {:?}", x));
    });
}
```

`-w2` gets 2 workers.

```rust
// cargo-deps: timely
extern crate timely;

use timely::dataflow::{InputHandle, ProbeHandle};
use timely::dataflow::operators::{Input, Exchange, Inspect, Probe};

fn main() {
    // initializes and runs a timely dataflow.
    timely::execute_from_args(std::env::args(), |worker| {

        let index = worker.index();
        let mut input = InputHandle::new();
        let mut probe = ProbeHandle::new();

        // create a new input, exchange data, and inspect its output
        worker.dataflow(|scope| {
            scope.input_from(&mut input)
                 .exchange(|x| *x)
                 .inspect(move |x| println!("worker {}:\thello {}", index, x))
                 .probe_with(&mut probe);
        });

        // introduce data and watch!
        for round in 0..10 {
            if index == 0 {
                input.send(round);
            }
            input.advance_to(round + 1);
            while probe.less_than(input.time()) {
                worker.step();
            }
        }
    }).unwrap();
}
```

## Ascent

```rust
// cargo-deps: ascent
use ascent::ascent;
ascent!{
   relation edge(i32, i32);
   relation path(i32, i32);
      
   path(x, y) <-- edge(x, y);
   path(x, z) <-- edge(x, y), path(y, z);
}

fn main() {
   let mut prog = AscentProgram::default();
   prog.edge = vec![(1, 2), (2, 3), (3,4),(4,5)];
   prog.run();
   println!("path: {:?}", prog.path);
}
```

So if I could make a trait that mutates a global uf...

<https://docs.rs/union-find/latest/union_find/>
<https://docs.rs/ena/latest/ena/>

No. nevermind. That isn't good enough.

# Traits

## GAT

<https://blog.logrocket.com/using-rust-gats-improve-code-app-performance/>

# Concurrency

<https://doc.rust-lang.org/nomicon/send-and-sync.html>
Send - safe to send to threads. borrows. Sync. safe to share. marker traits
atomics

# Async

<https://rust-lang.github.io/async-book/>
traits

Future

# Resources

<https://github.com/evcxr/evcxr>  rust jupyter `evcxr_jupyter --install`
<https://dimforge.com/> naalgebra
 rapier physics salva fluid sim

<https://github.com/sunfishcode/eyra> - avoiding libc dependency in rust? Running rust in rust
<https://github.com/sunfishcode/mustang#readme>
<https://github.com/sunfishcode/origin#readme> program an tread shutdown in rust

[from stacks to trees](https://www.ralfj.de/blog/2023/06/02/tree-borrows.html)<https://www.reddit.com/r/rust/comments/13y8a9b/from_stacks_to_trees_a_new_aliasing_model_for_rust/>  <https://perso.crans.org/vanille/treebor/>
[miri interpreter](https://github.com/rust-lang/miri/) interpreter on mir ir detects undefined behavior

[im](https://docs.rs/im/latest/im/#) immutable data structure / maps. Hash array mapped tries. HAMT.

[cargo-dist](https://blog.axo.dev/2023/02/cargo-dist)

[embeddable interpeters](https://www.reddit.com/r/rust/comments/s63j6n/which_scripting_languages_work_well_embedded_with/)

- rlua
- [Rhai](https://github.com/rhaiscript/rhai)
- [Rustpython](https://github.com/RustPython/RustPython) a python interpreter than can run in browser and be embedded

[deflect](https://github.com/jswrenn/deflect) runtime reflectin of types via dwarf <https://jack.wrenn.fyi/blog/deflect/>
rust atmics book <https://marabos.nl/atomics/>

[easy-smt](https://github.com/elliottt/easy-smt)

- [implementing sage gc in rust](https://news.ycombinator.com/item?id=31166368)
- [eyros](https://github.com/peermaps/eyros) interval database. box queries
- [salsa](https://github.com/salsa-rs/salsa) rust incremental computation library
- [maturin](https://github.com/PyO3/maturin) publish pyo3 rust packages on pip
- [automerge-rs](https://github.com/automerge/automerge-rs)
- [crossbeam](https://github.com/crossbeam-rs/crossbeam)
- timely dataflow
- lalrpop nom
- [rust script](https://rust-script.org/) I power my inline blogging with this.
- [cyclone](https://pling.jondgoodwin.com/post/cyclone/) Interesting breakdown of some history
- [little book of rust macros](https://danielkeep.github.io/tlborm/book/README.html)

- <https://news.ycombinator.com/item?id=25222750> - risp a rust lisp

- <https://altsysrq.github.io/proptest-book/intro.html>
- egg - e graph library <https://docs.rs/egg/0.6.0/egg/> <https://arxiv.org/abs/2004.03082>
- <https://nnethercote.github.io/perf-book/>
- <https://ferrous-systems.com/blog/dlx-in-rust/>
- <https://hexgolems.com/2020/10/getting-started-with-ddlog/>
- <https://www.stephendiehl.com/posts/exotic03.html> effect systems are off to the side, but do they help explain lifetimes? divergence as an effect
- crust of rust series
- Max Willsey <https://www.mwillsey.com/blog/rust-intro>
- <https://rust-unofficial.github.io/too-many-lists/>
- <https://news.ycombinator.com/item?id=25610741> alhalf hour to learn rust. This guy has other good articles too
- <https://rust-unofficial.github.io/patterns/>

# warn clippy will give advice

<https://rust-lang.github.io/chalk/book/recursive.html> chalk is interesting

modelling lifetimes as St monad. Moslty makes sense. Lifetimes are ordered though.
Could one make an ST monad that uses a stack of scopes?

deref trait

Rust ffi
<https://rust-embedded.github.io/book/interoperability/rust-with-c.html>
<https://www.greyblake.com/blog/2017-08-10-exposing-rust-library-to-c/>
<https://karroffel.gitlab.io/post/2019-05-15-rust/> Cbindgen

6/2020
Nom parsing

It helps that you can use smart constructors that do the Box::new. That takes away some of the pain

// <https://stackoverflow.com/questions/51182640/is-it-possible-to-represent-higher-order-abstract-syntax-in-rust> interesting example of HOAS

    ```
    <code>    #[derive(Debug, Eq, PartialEq, Clone)]
        pub enum Lambo {
            Lam(Box<Lambo>),
            Var(i64),
            App(Box<Lambo>, Box<Lambo>),
        }
        pub use self::Lambo::*;
        
        fn lam(t: Lambo) -> Lambo {
            Lambo::Lam(Box::new(t))
        }
        fn app(t: Lambo, v: Lambo) -> Lambo {
            Lambo::App(Box::new(t), Box::new(v))
        }
        fn parse_lam(input: &str) -> IResult<&str, Lambo> {
            let head = preceded(char('\\'), preceded(space0, alpha1));
            let tail = preceded(space0, preceded(tag("->"), parse_lambo));
            map(pair(head, tail), |(v, b)| lam(b))(input)
        }
        fn parse_lambo_parens(input: &str) -> IResult<&str, Lambo> {
            delimited(char('('), parse_lambo, char(')'))(input)
        }
        fn parse_nonapp(input: &str) -> IResult<&str, Lambo> {
            let parse_var = map(alpha1, |x| Var(0)); // placeholder
            alt((parse_lambo_parens, parse_lam, parse_var))(input)
        }
    
        fn parse_lambo(input: &str) -> IResult<&str, Lambo> {
            let (input, n) = terminated(preceded(space0, parse_nonapp), space0)(input)?;
            // let (input, n) = preceded(space0, parse_nonapp)(input)?; */
            fold_many0(terminated(parse_nonapp, space0), n, |t, e| app(t, e))(input)
        }
    
        #[test]
        fn parse_lambo_test() {
            assert_eq!(
                parse_lambo("  (\\ x -> x)  (\\ z -> z )  "),
                Ok(("", app(lam(Var(0)), lam(Var(0)))))
            );
        }</code>

```

* * *

Thoughts. Put the enum in the outer type. Matching on that outer type then tells us which branch we're in. Make each indivudal field of the gadt an irretuable struct. Each one then has an eliminator form. Writing the elim typeclass for these is more foolproof. The irrefutable match in the eliminator allows for a more pattern matching like syntax. No mixup of lambda is possible. Two layer design. The rust compiler knows that actual branches of a match can't all happen. The pure eliminator form I had didn't. That will be a problem for moving stuff into the closures proabbly. Another possibility that feels interesting is Gadt<S>(Gadt<Int>()) where we have the specalize version inside the unspecialized version. Still use smart construcotrs. that guy mentioned. The pure structs in the enum should hypoethtically have no additional overhead as far as i know. Somehow related to the fact that gadts are somehow very similar to typelevel programming using typeclasses.

Might still be things to leanr in the gadtless programming paper

[https://www.cs.ox.ac.uk/files/3060/gadtless.pdf](https://www.cs.ox.ac.uk/files/3060/gadtless.pdf)

Simpler forms of the eliminator can be used based on the situation. Singletons - GADTs aren't free, so maybe it is better off doing the isngleton pattern a different way.

The two layer design gives kind of a type level witness to the branch you are in. If the only way to Access the TTBool type is in the context of the TBool enum constructor, then you know you are in that branch of a pattern match in your have access to such a thing. Then you can use a typeclass predictaed pon that type to do a simple eimination. Or you could have a leibnitz class that let's you cast s. The inner construcotrs also gfive a reasonable place to put existentiual variables?

    ```
    <code>
    struct TTBool<S> {bool, phantom<S>}
    
    struct TTInt<S> {i64, phanton<S>}
    
    enum MyGadt<S>{
    TBool(TTBool<S>),
    TInt(TTInt<S>)
    }
    
    struct Succ<N>{ N }
    struct Zero{}
    
    enum SNat<S>{
    SSucc(Succ<?>( Box(SNat<?>))),
    SZero(Zero)
    }
    enum SNat<S>{
    SSucc(SSSucc<S,T>( Box(SNat<T>))), // This T will not compile. It's not bound anywhere. T = Pred(S), S = Succ T
    SZero(Zero)
    }
    
    fn sSucc( ) -> 
    
    impl<S,T> Elim for SSSucc<S,T> {
      fn<F : App<> > elim(  Fn (Box<SNat<T>>) -> F as App<Succ<T>>   ) -> <F as App<S>>
    }
    
    impl<T> Elim for SSSucc<Succ<T>> {
      fn<F : App<> > elim(  Fn (Box<SNat<T>>) -> F as App<Succ<T>>   ) -> <F as App<S>>
    }
    
    
    
    
    match x{
    SSucc x => x.elim<?>(|b| )
    
    
    </code>
```

This pattern of giving each in an enum constructor it's own struct data type has the flavor of something oner might call an associated type constructor. If you wanted to associate a constructor with a type, you could give this tpye name as an associated type . Nvm. This is not what is meant by the term in rust.

This is trash. i hate this

Linear types: Secret sharing. If i had a channel that output two linked bits on each side, then I could use functions that accept ownership only of the shares, enforcing via the type system that i only use them once. Then I can open shares and send them. Secrets are held in their own data type that can be combined with Shares.

Linear types for quantum. Again, functions that consume the arguments. Kron could have a bimap function that takes tuples of vectors. The kron needs the ability to know how to seperate out the vectors into sums. lmap and rmap as well.

What are type constructors? They are very similar to functions. Through some strange twist of fate, we don't get to specify their type the same way in most programming languages. Any type variables in the type have to be fully generic/polymorphic. This is not the case for functions.

We can have an identity function

fn id<A>(x : A) -> A { x}

but without changing the implementation we can restrict the allowed types

    <code>fn id_i64(x : i64) -> i64 { x }</code>

Where the type constructor Id we don't really have this specialization available at define time.

    <code>struct Id<A>(A);</code>

However, we can build a type specialized smart constructor.

    <code>struct Idi64INTERNAL<A> (A);
    fn Idi64(x : i64) -> Idi64INTERNAL<i64> { Idi64INTERNAL(x) }</code>

Likewise we can build smart constructors with restricted types. This gives us half of the GADT. We can only produce GADT correct values

What else is a data type? It is a thing you can pattern match to get stuff out of. The regular rust `match` will not work for us anymore. What is a match? Well, one way to replicate the behavior of a match is with another function

An example of this is in the standard library for Option

[https://doc.rust-lang.org/std/option/enum.Option.html#method.map_or_else](https://doc.rust-lang.org/std/option/enum.Option.html#method.map_or_else)

map_or_else is exactly the eliminator form.

Similarly

[https://doc.rust-lang.org/std/result/enum.Result.html#method.map_or_else](https://doc.rust-lang.org/std/result/enum.Result.html#method.map_or_else)

```
pub fn [map_or_else](https://doc.rust-lang.org/std/option/enum.Option.html#method.map_or_else)<U, D, F>(self, default: D, f: F) -> U where  
D: [FnOnce](https://doc.rust-lang.org/std/ops/trait.FnOnce.html)() -> U,  
F: [FnOnce](https://doc.rust-lang.org/std/ops/trait.FnOnce.html)(T) -> U, `
```

   ```
    <code>
    fn elimOption<A,B>(x:Option<A>, some : Fn(A) -> B, none : B) -> B {
      match x {
        Some(x) => some(x),
        None => none 
       }
    }</code>
```

The extra power of the GADT match is that somehow it knows how to handle every possible type parameter that might show up and the result can depend on that type parameter.

Rust does not have great support for higher-kinded-types. In order to talk about a Vec, you need to fully apply it to something Vec. This is too bad. There are some thoughts on how to fake them.

[https://gist.github.com/CMCDragonkai/a5638f50c87d49f815b8](https://gist.github.com/CMCDragonkai/a5638f50c87d49f815b8)

[https://gist.github.com/14427/af90a21b917d2892eace](https://gist.github.com/14427/af90a21b917d2892eace)  

A related trick that I think works the best is defunctionalization. You need to make a new type that means VecTag. Then we can make a typelevel function using a trait with associated types to apply it.

   ```// every use site of gmatch reuqires an instance of App1 connected to a function symbol.
    trait App1<A> {
        type T;
    }
    struct VecTag {}
    impl<A> App1<A> for VecTag{
        type T = Vec<A>;
    }
    struct OptionTag {}
    impl<A> App1<A> for OptionTag{
        type T = Option<A>;
    }
    
    // A more anonymous function. Is more like a defunctionialized type synonym
    struct F1 {}
    impl<A> App1<A> for F1{
        type T = Vec<Vec<A>>;
    }
    
    
    // partially applied const.
    // struct Const()
    // call this next one const1
    struct Const2();
    struct Const<B>(PhantomData<B>);
    impl<A> App1<A> for Const2 { // partial application
        type T = Const<A>;
    }
    
    impl<A,B> App1<A> for Const<B>{
        type T = B; 
    }
    
    struct Id();
    
    impl<A> App1<A> for Id{
        type T = A; 
    }```

Having to define a new impl for App every time you want to eliminate is _literally_ the worst, it's merely pretty bad.

The other problem is how to get the eliminator to typecheck at all. One way out is to just blow a hole in the type system with an unsafe coercion construct. This is what is done in the Refl library for example. [https://docs.rs/refl/0.1.2/refl/ ](https://docs.rs/refl/0.1.2/refl/)This is okay-ish, but I'd rather do it this way. 

It is more clear to me in this encoding that given I only construct via my safe constructors, I should never end up in any of the panic! statements. Should it bug you that I've made the program a little more unsafe in order to implement these features? Yeah, probably.

    
    <code>impl<A> App<A> for VecTag {
       type T = Vec<A>;
    }</code>

  
Now we need to manually supply the type of the result if we want a GADT elimination. We can get the original eliminator that didn't depend on the type via a wrapping function that calls gadtElim with Const1<A>. 

A little macro sugar may be in order here as well.

Downsides:

It is unfortunate that now the order in which you pattern match matters. You also don't get good syntax for default cases.

syntax is worse overall

safety is possibly compromised by those panic! statements.

The eliminator typeclass is tough to read and probably error prone to write.  

Upsides:

Actually using the eliminator is surprisingly not that bad.

    
    <code>TInt().gadtElim::<F7>(vec!(true,false) , vec!(34,45,4,3,46))</code>

more types = good. If you don't buy into that, you probably hated this post.

Combining this with the singleton techniques you can do cool pseudo-dependently typed stuff in pure Rust. Neat-o.  

ATC/GAT do not exist at the moment.

Traits.

lifetimes are kind of like ST monad?

Higher ranked lifetimes are available. But no general rank-n types.

Existentials are in some weird nebulous zone.

The Key monad.

[https://cglab.ca/~abeinges/blah/too-many-lists/book/](https://cglab.ca/~abeinges/blah/too-many-lists/book/)

Huh. mem::replace is not something I would have expected. Neither the Option as_ref

null pointer optimization. Certain enums can use the tag field and unify it with the pointer field

In particular Option(&T) is the same size as Option

[http://cosmic.mearie.org/2014/01/periodic-table-of-rust-types/](http://cosmic.mearie.org/2014/01/periodic-table-of-rust-types/)

periodic table of rust

    
    <code>
    data FakeGADT a = IsInt' Int | IsBool' Bool
    -- smart constructors get us some of the way there
    isInt' :: Int -> FakeGADT Int
    isInt' = IsInt'
    isBool' :: Bool -> FakeGADT Bool
    isBool' = IsBool'
    
    class Tagless repr where
        isInt :: Int -> repr Int
        isBool :: Bool -> repr Bool
    
    class Consume2 repr where
        consume2' :: repr a -> a
    
    -- do we need a typeclass per function we may want to write?
    
    -- ambiguous without annotation
    --r1 :: (Consume2 repr, Tagless repr) => Int -> Int  
    --r1 x = consume2' @repr (isInt x)
    
    
    
    data RealGADT a where
        IsInt :: Int -> RealGADT Int
        IsBool :: Bool -> RealGADT Bool
    
    consume :: RealGADT a -> Int
    consume (IsInt x) = x 
    consume (IsBool x) = if x then 1 else 0 
    
    consume2 :: RealGADT a -> a -- pretty weird.
    consume2 (IsInt x) = x
    consume2 (IsBool x) = x
    
    transform :: RealGADT a -> RealGADT a -- can't transfrom IsInt to IsBool
    transform (IsInt x) = IsInt $ x + 1 
    transform (IsBool x) = IsBool $ not x 
    
    data DoorState = Opened | Closed | Locked
      deriving (Show, Eq)
    
    data SingDS :: DoorState -> * where
        SOpened :: SingDS 'Opened
        SClosed :: SingDS 'Closed
        SLocked :: SingDS 'Locked
    
    data DoorState' a = Opened | Closed | Locked
    -- smart constructors. basically do the same thing as gadt in the forward direction
    sOpened :: sOpened 'Opened
    sOpened = Opened
    sClosed :: sOpened 'Closed
    sOpened = Closed
    sLocked :: sOpened 'Locked
    sOpened = Locked
    
    matchDoor :: DoorState' a -> b -> b -> b -> b -- opened closed
    matchDoor Opened o c l = o -- matchDoor Opened = churchOpen
    matchDoor Closed o c l = c
    matchDoor Locked o c l = l
    
    --conor mcbride in faking it
    -- 
    data VNil a = VNil
    data VCons a b = VCons a b
    class Vector n s where
        vcons :: Vector (n-1) a -> 
    class ReflectDoorState s where
        reflect :: Proxy s -> DoorState -- DoorState' s?
    instance ReflectDoorState 'Opened where
        reflect = Opened -- sOpened?
    
    reifyWithDS :: DoorState -> (forall s. ReflectDoorState s => Proxy s -> a) -> a 
    reifyWithDS Opened f = f (Proxy @'Opened)
    reifyWithDS Closed f = f (Proxy @'Closed)
    reifyWithDS Locked f = f (Proxy @'Locked)
    
    
    class MatchDoor s where
        matchDoor :: DoorState' s -> f s -> b -> b -> f s
    instance MatchDoor (DoorState' 'Opened) where
        matchDoor _ o _ _ = o
    -- a typeclass for the recursor?
    -- but now we need a typeclass for the induction principle
    -- clearly pretty similar to the leibniz equality idea. We don't need to explcitly pack in the equality, but we still need 
    -- higher kinded polymorphism
    -- rust will probablt have significant difficulty inferring f?
    
    class MatchDoor s where
        matchDoor :: forall f. DoorState' s -> f 'Opened -> f 'Closed -> f 'Locked -> f s
    
    
    instance MatchDoor 'Opened where
        matchDoor Opened o _ _ = o
    
    matchDoor :: forall tag s. (fo ~ Apply tag 'Opened, fc ~ Apply tag 'Closed, fl ~ Apply tag 'Locked, fs ~ ApplyTag tag s) => 
                 DoorState' s -> fo -> fc -> fl -> fs
    -- it is not going to be able to guess tag? It needs to unify 4 different terms. Can we abuse the rust unifier?
    -- Unify1 taga tagb tagc | taga tagb -> tagc. Take the least specific. If you ever hit a contradiction, factor that bit out
    -- Unify fo fl fc -> tag, then Apply tag to s.
    instance Matchable s where
        type Cases
        type Res
        match :: s -> Cases -> Res
    -- reify and reflect let us get runtime typeclass choices.
    
    -- The equality class is basically leibnitz
    class MatchEq a b where
        matchEq :: forall f. f a -> f b
    
    -- how does one make hkt as painless as possible.
    -- Apply<f<x>,y> 
    -- https://medium.com/@JosephJnk/higher-kinded-polymorphism-with-javascript-and-flow-in-depth-da8d303b5854
    -- they are doign it in flow
    
    -- https://www.cl.cam.ac.uk/~jdy22/papers/lightweight-higher-kinded-polymorphism.pdf
    -- could desugar a case based on alphabetical ordering
    -- only one case deep?
    
    -- https://www.youtube.com/watch?v=ERM0mBPNLHc
    
    -- ok but how can we deal with nested situations.
    -- explicit type composition or recursion
    -- struct Compose<F,G>  is a tag representing the compsition
    -- Apply<U> for Compose<F,G> : F : Apply<G::Apply<U>::T> , G: Apply<U>  
    -- Id<a>
    -- Par
    -- Fst
    -- Snd 
    -- forall!(F<A>)   F<G<A>> ==>  rips the thing appart and builds the tag for it. While this could be a typeclass in haskell, it needs to be a macro inrust
    -- maybe not. If you instantiate the right kind of tagify for every concrete HKT type.
    -- The DSL is first order. Either by giving variables explciti names or by going point free.
    -- I hate this trash. macro dsl for type computation?
    -- this is not really all it needs. It also needs instantiation
    -- forall1!(F)  => 
    -- forall()
    -- forall!( F .   typeexpression  ) -- syntactically replace very occurence of F with 
    -- n is arity of the constructor
    type family Tagify (f a) = Apply (Tagify1 f) (Tagify a) 
    type family Tagify (f (g a)) = Apply (Tagify1 f) (Tagify a) 
    type family Tagify (Maybe a) = Apply (Maybe NullTag) (Tagify a) -- Compose (Maybe NullTag) 
    type family Tagify Bool = Bool
    
    class Tagify (f a) Compose (Tagify f)
    
    -- it is not going to infer much of anything typechecking wise
    -- can we achive some level of inferrence using a typeclass?
    class Tag1 Expr a where
        type Tagged -- with all occurrence replaced with 
    
    -- write type level unification?
    --class Unify env a b where 
    
        -- could I tap out to Z3 for unification? in  a macro. But I won't even get the type in the macro. It's inferred.
    churchOpen :: b -> b -> b -> b
    churchOpen x _ _ = x
    
    -- the isomorphism
    initialOpen :: (forall b. b -> b -> b -> b) -> DoorState
    initialOpen f = f Opened Closed Locked
    
    -- http://www.haskellforall.com/2012/06/gadts.html
    -- eds comment at the bottom. Typeclass are often rank-2 dictionaries.
    -- Huh. Yeah. He might be right.
    class IdFaker s where
        idfaker :: a -> a -- looks regular polymorphic
    instance IdFaker s where
        idfaker = id
    needsid :: IdFaker b => b -> b -- desugars to => forall b. (forall a. a -> a) -> b -> b 
    needsid b = idfaker b
    -- any polymorphic variable in the typeclass functions themselves is higher ranked.
    class Rank2Helper label a where -- in order to pass in t
        reifyHelper :: ReifiesDoor s => Proxy s -> a
    reifyWith :: Rank2Helper a => DoorState -> a -- yikes
    reifyWith Opened = reifyHelper @label (Proxy @'Opened)
    -- in order to use the reifyHelper, we need to give the function a name. and define the typeclass for it.
    -- I guess we could #[derive HigherRank] to build the typeclass automatically.
    -- what if I did reifyWith for the helper also, since I kind of want to be passing in typeclass on the fly without having to consutrct them.
        
    
    -- the reify trick needs higher ranked types. But it is using actuallty a scoping vairable a la ST. so perhaps this can be emulated with lifetimes.
    Is that right? I think the foralled variavle is a typelevel index of the value you're passing in.
    
    {-
    class DS repr where
        sOpened :: repr 'Opened
        sClosed :: repr 'Closed
        sLocked :: repr 'Locked
    -}
    data Door s
    
    closeDoor :: Door 'Opened -> Door 'Closed
    closeDoor = undefined
    
    lockDoor :: Door 'Closed -> Door 'Locked
    lockDoor = undefined
    
    lockAnyDoor :: SingDS s -> Door s -> Door 'Locked
    lockAnyDoor sng door = case sng of
        SOpened -> lockDoor (closeDoor door) -- in this branch, s is 'Opened
        SClosed -> lockDoor door             -- in this branch, s is 'Closed
        SLocked -> door                      -- in this branch, s is 'Locked
    
    
    class LockDoor lockstate repr where
        lockAnyDoor :: repr lockstate -> repr 'Locked</code>

lam \i

sum \i

argmin \i

max \i
