use vstd::prelude::*;

/* SLIDE

┏━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━┓
┃ Verus: Verified Rust for Low-Level Systems ┃
┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛

FIN */

/* SLIDE

“Verus is a tool for verifying the correctness of code 
written in Rust. Developers write specifications of what 
their code should do, and Verus statically checks that 
the executable Rust code will always satisfy the specifications 
for all possible executions of the code. Rather than adding 
run-time checks, Verus instead relies on powerful solvers 
to prove the code is correct.”

FIN */

/* SLIDE

“Verus currently supports a subset of Rust (which we are 
working to expand), and in some cases, it allows developers 
to go beyond the standard Rust type system and statically 
check the correctness of code that, for example, manipulates 
raw pointers.”

FIN */

/* SLIDE

Verus is used in practical verification projects

∙ The Atmosphere kernel
∙ Verdict: An X.509 certificate validator
∙ Vest: verified high performance parsing and serialization
∙ VeriSMo: a verified security module for VMs
∙ Concurrency correctness for Amazon's EC2 hypervisor
∙ <https://verus-lang.github.io/verus/publications-and-projects/>

FIN */

/* SLIDE

┌───────────────────────────┐
│ §1 : Verification Basics  │
└───────────────────────────┘

FIN */

// SLIDE
verus! {

  pub fn foo() {
      assert(1 == 1 + 0);
  }

}

// To use verus, you need to enclose verus code in a block 
// and apply the `verus!` macro.
// 
// This turns on some extra syntax for the verus verifier 
// (above, we have `assert` rather than `assert!`)
//
// to verify your current crate, run `cargo verus verify`
/* SLIDE
Because the interface is through cargo, you get drop-in 
compatibility with some rust tooling (e.g. vim's Rust
`:make` configuration). There's also verus-analyzer LSP, 
a fork of rust-analyzer.
FIN */

verus! {

// SLIDE
pub fn requires_mod_34(x : u8) 
    requires
        x % 34 == 0
{
    assert(x % 17 == 0);
    assert(x % 2 == 0);
}

// You can impose preconditions on functions using `requires`
//
// These are assumed when verifying the function body
// SLIDE
pub fn foo3() {
    requires_mod_34(68);
}

// They're also checked when calling the function
// SLIDE
pub fn ensures_mod_34(x: u8) -> (out: u8)
    ensures
        out % 34 == 0
{
    if x % 34 == 0 { x }
    else { 68 }
}

// Similarly, you can impose postconditions. These are 
// checked when verifying the function body.
// SLIDE
pub fn foo4(x : u8) {
    requires_mod_34(ensures_mod_34(x));
}

// postconditions are also assumed when calling the function
// FIN

// SLIDE
pub fn just_mod_34(x: u8) -> (out: u8)
    // XXX no ensures clause!
{
    if x % 34 == 0 { x }
    else { 68 }
}

pub fn foo5(x : u8) {
    requires_mod_34(ensures_mod_34(x));
}

// Requires and ensures are manditory. Verus won't inline 
// the body automatically.
// FIN

/* SLIDE

┌─────────────────────┐
│ §2 : Ghost Code 👻  │
└─────────────────────┘

FIN */

/* SLIDE
In verus, code has MODES

All of the functions above were in "Exec Mode". That's 
the default mode. During compilation, exec mode code
is distilled to regular Rust, by removing verus-specific
syntax.
FIN */

// SLIDE
// These are equivalent

pub exec fn exec_example_1() -> String {
    assert(7 + 5 == 12);
    "obviously".to_owned()
}

pub fn exec_example_2() -> String {
    assert(7 + 5 == 12);
    "obviously".to_owned()
}
/* SLIDE
The other main modes are

∙ Proof Mode: functions whose point is to statically
  hint that some conditions is or must be met
∙ Spec Mode: functions that cannot necessarily be executed
  but which can be used in defining pre/post conditons

Non-exec modes are *ghost code*, erased before compilation.
FIN */

// SLIDE
//               ↓        ↓       ↓
spec fn max(n : nat, m : nat) -> nat {
    if (n < m) { n }
    else { m }
}

// Ghost code can use an extended type system inherited from z3
// SLIDE
pub fn fibs_det(x : usize, y : usize) {
    assert(max(x as nat, y as nat) == max(x as nat, y as nat))
}

// spec functions are determinstic
// SLIDE
// spec functions don't need a body (although they can 
// be given one).

uninterp spec fn F(n : nat) -> nat;

// with no body, z3 treats a spec as an uninterpreted function. 
// SLIDE
proof fn max_sym(x : nat, y: nat)
    ensures
        max(x,y) == max(y,x)
{ /* z3 discharges this */ }

// Within a module, spec bodies are inlined. If the spec 
// is exported, you need to decide whether to expose the body
// within other modules.
// SLIDE
// If you don't expose a spec body, proofs form a kind of API; 
// you can call them in other proofs in order to bring some of 
// the properties of the spec into scope.

proof fn max_sym_proof() {
    max_sym(5,10);
    assert(max(5,10) == max(10,5));
}

// proof code can also be injected into exec functions using `by`
pub fn max_sym_exec() {
    assert(max(5,10) == max(10,5)) 
        by { max_sym(5,10) };
}
// SLIDE
// `by` can also can call out to specialized solvers

pub fn bitblast(x : u64)
        requires x < 2^63
{
    assert(((x as u64) << 1) >> 1 == x) 
        by (bit_vector)
        requires x < 2^63
}
/* SLIDE

┌────────────────────────────────┐
│ §3: Recursion and Induction ♾️ │
└────────────────────────────────┘

FIN */

// SLIDE
spec fn fib(n: int) -> int 
        decreases n,
    {
        if n <= 1 {
            1
        } else {
            fib(n - 1) + fib(n - 2)
        }
    }

// Recursive functions require a decreases clause
// SLIDE
proof fn inlined_fib(n: int) 
    requires
    n > 3
{
    reveal_with_fuel(fib, 2);
    assert(fib(n) == fib(n - 2) + fib(n - 3) + fib(n - 3) + fib(n - 4))
}

// recursive specs can be recursively inlined by giving them "reveal fuel"
// SLIDE
proof fn fib_mono (m : int, n : int)
        ensures 
            m <= n ==> fib(m) <= fib(n)
        decreases n,
{ 
    if n <= 1 {

    } else {
        fib_mono(m - 1, n - 1); // so fib(m - 1) <= fib(n - 1)
        fib_mono(m - 2, n - 2); // so fib(m - 2) <= fib(n - 2)
        // fib(m) = 
        // fib(m - 1) + fib(m - 2) <= 
        // fib(n - 1) + fib(n - 2) = 
        // fib(n)
        
    }
}

// inductive proofs are just recursive functions!
// FIN

/* SLIDE

┌──────────────┐
│ §4: Loops 🌀 │
└──────────────┘

FIN */

/* SLIDE
If you want to know anything about the state of the program 
after a loop, you need a loop invariant. This is something 
that's true when you enter the loop, and still true at the
end of each loop iteration.
FIN */

// SLIDE
pub fn ndouble(n : u64, d : u64) -> (ndoubled : u64)
        requires n < 2^62
        ensures ndoubled % 2 == 0
{
    let mut out = n * 2;
    let mut idx = d;
    while idx > 0
        invariant
            out < 0xFFFFFFFFFFFF, // avoid overflow
            out % 2 == 0, idx >= 0,
        decreases
            idx // ← you need a decreases clause!
    {   
        out = 
            if out < 0xFFFFFFFFFFF { out * 2 }
            else { out };
        idx = idx - 1 
    }
    out
}
// SLIDES
// loops are information-impermeable. Any facts going in or out
// need to be part of the loop invariant.
/* SLIDE
┌────────────────────┐
│ §4: Quantifiers ∀∃ │
└────────────────────┘
FIN*/

// SLIDE
// Verus supports quantifiers!

proof fn forall_evens(s: Seq<int>)
    requires
        5 <= s.len(),
        forall|i: int| 0 <= i < s.len() ==> s[i] % 2 == 0,
{
    assert(s[3] % 2 == 0);
}

proof fn exists_evens(mut s: Seq<int>) -> (out : Seq<int>)
    ensures
        exists|i: int| out[i] % 2 == 0,
{
    let l = seq![32 as int];
    let v = l + s;
    assert(v[0] == 32);
    v
}
/* SLIDE
Using universal truths requires us to *instantiate* 

⊢ ∀x.Fx => ⊢ Fa

Proving existential truths requires us to *generalize*.

⊢ Fa => ⊢ ∃x.Fx
FIN */

/* SLIDE
But we have infinitely terms we might instantiate to, 
or generalize from. 

CHOICE PARALYSIS!
FIN */

spec fn is_distinct(x: int, y: int) -> bool {
    x != y
}

// SLIDE
// Verus adopts z3's solution. *Triggers*. We pattern 
// match against *trigger expressions* inside the function 
// body, and instantiate with any matching tuples of terms.

proof fn test_distinct1(s: Seq<int>)
    requires
        5 <= s.len(),
        forall|i: int, j: int| 0 <= i < j < s.len() 
            ==> is_distinct(#[trigger] s[i], #[trigger] s[j]),
{
    assert(s[2] != s[4]);
}
// SLIDE
// It picks reasonable triggers by default though, 
// so this works well enough even for proving general facts

uninterp spec fn P(x : int) -> bool;
uninterp spec fn Q(x : int) -> bool;

proof fn forall_exists(s: Seq<int>)
    requires
        forall|i: int| #[trigger] P(s[i]),
        forall|i: int| P(s[i]) ==> #[trigger] Q(s[i]),
    ensures
        forall|i: int| #[trigger] Q(s[i])
{ }
/* SLIDE

┌───────────────────┐
│ §5: Next Steps ⏰ │
└───────────────────┘

FIN */

/* SLIDE
I'd like to get started with verus' support for unsafe pointers and
multi-threaded concurrency.
FIN */

/* SLIDE
Verus' approach to all nontrivial ownership disciplines (involving the 
coordination of access to shared resources) is to build a state-machine
model, and prove that the code implements it.
FIN */

/* SLIDE
The general idea is:

“1. Consider the program you want to verify.
 2. Create an “abstraction” of the program as a tokenized state machine.
 3. Verus will automatically produce for you a bunch of ghost “token types”
    that make up the tokenized state machine.
 4. Implement a verified program using the token types”

Unfortunately, this part of verus is a little raw and underdocumented.
FIN */

/* SLIDE
But fundamentally, it's based on *macros* which expand to more elaborate 
specifications built out of verus primitives - (including some not discussed 
today). It's not a special purpose feature. Rather, it's ergonomics for a 
particular design pattern.
FIN */

/* SLIDE
Maybe that's the right design for a securestack kernel? Or maybe different
theoretical foundations implemented as a macro library?
FIN */

// FIN

}
