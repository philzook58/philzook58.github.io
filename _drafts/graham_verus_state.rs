#[allow(unused_imports)]
use verus_builtin::*;
use verus_builtin_macros::*;
use vstd::prelude::*;
use vstd::{pervasive::*, *};

use verus_state_machines_macros::state_machine;
use verus_state_machines_macros::tokenized_state_machine;

/* SLIDE

┏━━━━━━━━━━━━━━━━━━━━━━━━━┓
┃ State Machines in Verus ┃
┗━━━━━━━━━━━━━━━━━━━━━━━━━┛

FIN */

/* SLIDE

┌────────────────────────────────────┐
│ §1 : Verification Basics Refresher │
└────────────────────────────────────┘

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
//
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

// postconditions are also assumed when calling the function
// FIN

// SLIDE

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

The other main modes are

∙ Proof Mode: functions whose point is to statically
  hint that some conditions is or must be met
∙ Spec Mode: functions that cannot necessarily be executed
  but which can be used in defining pre/post conditons

Non-exec modes are *ghost code*, erased before compilation.
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
However, we live in an age of strange and terrible wonders.
FIN */

/* SLIDE
I extracted a not-too-bad manual from the code using an LLM.
FIN */

/* SLIDE

┌───────────────────────────────┐
│ §3 : State Machine Basics ⚙️  │
└───────────────────────────────┘

FIN */

/* SLIDE

A Traffic Light:

   ┌───────┐   ┌────────┐   ┌─────┐   
┌→ │ GREEN │ → │ YELLOW │ → │ RED │ ┐
│  └initial┘   └────────┘   └─────┘ │  
└───────────────────────────────────┘

FIN */

/* SLIDE

To specify the thing structurally, we need:

1. initial states
2. transitions

FIN */

// SLIDE

// And also actually,
// 
// 0. the shape of the state data


pub enum Color {
    Green,
    Yellow,
    Red,
    BLACK,
}

//FIN */


/* SLIDE

So at a high level we want:

state_machine! {
    MyStateMachine {
        fields { ...state data goes here... }

        init! { ...possible initialization... }

        transition! { ...possible transition... }
    }
}

FIN */

// SLIDE

// So to open the definition:

state_machine!{
    TrafficLight {

// SLIDE

// And then we declare the state data:

    fields {
        pub color : Color,
        pub step_count : nat,
    }

// SLIDE

// and initialize some fields with a simple DSL:

    init!{
        initialize() {
            init color = Color::Green;
            init step_count = 0; // useful later
        }
    }

// SLIDE

// And also define some transitions, with another DSL

    transition!{
        to_yellow() {
            require(pre.color == Color::Green);
            update color = Color::Yellow;
            update step_count = pre.step_count + 1;
        }
    }

// SLIDE

    transition!{
        to_red() {
            require(pre.color == Color::Yellow);
            update color = Color::Red;
            update step_count = pre.step_count + 1;
        }
    }

// SLIDE


    transition!{
        to_green() {
            require(pre.color == Color::Red);
            update color = Color::Green;
            update step_count = pre.step_count + 1;
        }
    }

/* SLIDE

OK, and so that lets us build a state machine.

but what's the *point*?

FIN */

/* SLIDE

Well, we want verus to PROVE things about the machine.

FIN */

// SLIDE

// For example, that the machine satisfies certain invariants.

    #[invariant]
    pub fn is_valid_color(&self) -> bool {
        self.color !== Color::BLACK
    }

    #[invariant]
    pub fn is_correct_count(&self) -> bool {
        match self.color  {
           Color::BLACK => false,
           Color::Green => self.step_count % 3 == 0,
           Color::Red => self.step_count % 3 == 2,
           Color::Yellow => self.step_count % 3 == 1,
        }
    }

/* SLIDE

How do we prove these? By induction. We need to prove that they hold in each initial state, given
how the state is initialized, and also that they are preserved by each transition.

FIN */

// SLIDE

// In the case above, the proofs are pretty simple:

    #[inductive(initialize)] fn init_inductive(post : Self) { }

    #[inductive(to_yellow)] fn to_yellow_ind(pre: Self, post : Self) { }

    #[inductive(to_red)] fn to_red_ind(pre: Self, post : Self) { }

    #[inductive(to_green)] fn to_green_ind(pre: Self, post : Self) { }

/* SLIDE

But what's going on?

∙ the invariants are macro-expanded to spec mode code, defining spec predicates.
∙ the inductives are macro-expanded to proof mode code.

FIN */

/* SLIDE

∙ inductives get `requires` clauses stating that the invariants hold of pre, and that pre and post have
  the relation ensured by the transition or initialization DLS*

∙ inductives get `ensures` clauses stating that invariants

That's why the proofs are often trivial - z3 can tell that the invariant on post follows from the
invariant on pre plus the relations from transition.

* details a little subtle

FIN */


}}

/* SLIDE

┌───────────────────────────────┐
│ §4 : Tokenized state machines │
└───────────────────────────────┘

FIN */

/* SLIDE
OK, that's a state machine. We can prove it satisifies invariants using verus. So that makes verus
into a kind of frontend for state machine verification using z3.

But what would be really cool would be if we could tie all this to the rust code that we actually
run.
FIN */

// SLIDE

// For that we need:

tokenized_state_machine!{ 
    TokTrafficLight {

    fields {
        #[sharding(variable)]
        pub color : Color,
        #[sharding(variable)]
        pub cycle_count : nat,
    }

// FIN

    init!{
        initialize() {
            init color = Color::Green;
            init cycle_count = 0;
        }
    }

    transition!{
        to_yellow() {
            require(pre.color == Color::Green);
            update color = Color::Yellow;
        }
    }

    transition!{
        to_red() {
            require(pre.color == Color::Yellow);
            update color = Color::Red;
            update cycle_count = pre.cycle_count + 1;
        }
    }


    transition!{
        to_green() {
            require(pre.color == Color::Red);
            update color = Color::Green;
            update cycle_count = pre.cycle_count + 1;
        }
    }

    #[invariant]
    pub fn is_valid_color(&self) -> bool {
        self.color !== Color::BLACK
    }

    #[invariant]
    pub fn is_correct_count(&self) -> bool {
        match self.color  {
           Color::BLACK => false,
           Color::Green => self.cycle_count % 2 == 0,
           Color::Red => self.cycle_count % 2 == 1,
           Color::Yellow => self.cycle_count % 2 == 0,
        }
    }

    #[inductive(initialize)] fn init_inductive(post : Self) { }

    #[inductive(to_yellow)] fn to_yellow_ind(pre: Self, post : Self) { }

    #[inductive(to_red)] fn to_red_ind(pre: Self, post : Self) { }

    #[inductive(to_green)] fn to_green_ind(pre: Self, post : Self) { }

}}

/* SLIDE
Everything else is the same as before, at least for this example
FIN */

// SLIDE

// but now we can write an exec mode function:

fn traffic_cycle() {

    let tracked (
        Tracked(light), 
        Tracked(color), 
        Tracked(cycle_count)
    ) = TokTrafficLight::Instance::initialize();

    proof { light.to_yellow(&mut color); }

    proof { light.to_red(&mut color, &mut cycle_count); }

    proof { light.to_green(&mut color, &mut cycle_count); }

}

// What's up with `tracked`?

// SLIDE
// Tracked is a trick for letting you pass around ghost proof-mode variables. They're wrapped in
// a constructor that, at runtime, erases the tracked ghost variables. 

fn traffic_cycle_exec() {

    // notice the "tracked" prefix to the destructuring assignment
    let tracked (
        Tracked(light), 
        Tracked(color), 
        Tracked(cycle_count)
    ) = TokTrafficLight::Instance::initialize();

    go_yellow(Tracked(&light), Tracked(&mut color), Tracked(&mut cycle_count));

    go_red(Tracked(&light), Tracked(&mut color), Tracked(&mut cycle_count));

    go_green(Tracked(&light), Tracked(&mut color), Tracked(&mut cycle_count));

}

// SLIDE
// Each transition above is an exec mode function, with some proof code in it. 

fn go_green(
    Tracked(light) : Tracked<&TokTrafficLight::Instance>, 
    Tracked(color) : Tracked<&mut TokTrafficLight::color>,
    Tracked(cycle_count) : Tracked<&mut TokTrafficLight::cycle_count>
    )
    requires 
        // ↓ we need to guarantee that we're going to be able to meet the preconditions
        // for the transition,
        old(color).value() == Color::Red,
        // ↓ we need to guarantee that our state is all coming from the same machine
        old(color).instance_id() == light.id(), 
        old(cycle_count).instance_id() == light.id()
    ensures
        color.value() == Color::Green,
        // ↓ and we need to guarantee that we're not mutating the tracked variables and swapping in
        // state from a different machine
        old(color).instance_id() == color.instance_id(),
        old(cycle_count).instance_id() == cycle_count.instance_id(),
{ 
    proof {
        light.to_green(color, cycle_count);
    }
}
// FIN


fn go_red(
    Tracked(light) : Tracked<&TokTrafficLight::Instance>, 
    Tracked(color) : Tracked<&mut TokTrafficLight::color>,
    Tracked(cycle_count) : Tracked<&mut TokTrafficLight::cycle_count>
    )
    requires 
        old(color).value() == Color::Yellow,
        old(color).instance_id() == light.id(),
        old(cycle_count).instance_id() == light.id()
    ensures
        color.value() == Color::Red,
        old(color).instance_id() == color.instance_id(),
        old(cycle_count).instance_id() == cycle_count.instance_id()
{ 
    proof {
        light.to_red(color, cycle_count);
    }
}

fn go_yellow(
    Tracked(light) : Tracked<&TokTrafficLight::Instance>, 
    Tracked(color) : Tracked<&mut TokTrafficLight::color>,
    Tracked(cycle_count) : Tracked<&mut TokTrafficLight::cycle_count>
    )
    requires 
        old(color).value() == Color::Green,
        old(color).instance_id() == light.id(),
        old(cycle_count).instance_id() == light.id()
    ensures
        color.value() == Color::Yellow,
        old(color).instance_id() == color.instance_id(),
        old(cycle_count).instance_id() == cycle_count.instance_id()
{ 
    proof {
        // transitions take exactly the arguments they update
        light.to_yellow(color);
    }
}

/* SLIDE
┌────────────────────────────┐
│ §5 : Linear Token Tracking │
└────────────────────────────┘
FIN */

//SLIDE

// tokenized state machines have one more cool trick.

tokenized_state_machine!{ 
    ParkingLot {
        fields {
            // `variable` is the basic "sharding strategy" we've been dealing with
            #[sharding(variable)]
            pub occupancy: nat,

            // But it's not the only one!
            #[sharding(constant)]
            pub capacity: nat,

            // ↓ count is representative, and interesting
            #[sharding(count)]
            pub permits: nat,
    }

// FIN

    init! {
        initialize(capacity : nat) {
            init capacity = capacity;
            init occupancy = 0;
            init permits = capacity;
        }
    }

// SLIDE

// Each kind of sharding strategy has some designated update keywords in the transition DSL

    transition! {
        enter() {
            remove permits -= (1);
            update occupancy = pre.occupancy + 1;
        }
    }

    transition! {
        leave() {
            require(pre.occupancy > 0);
            add permits += (1);
            update occupancy = (pre.occupancy - 1) as nat;
        }
    }
    
// FIN

    #[inductive(initialize)]
    fn ind_init(post : Self, capacity : nat) { }

    #[inductive(enter)]
    fn ind_enter(pre: Self, post : Self) { }

    #[inductive(leave)]
    fn ind_leave(pre: Self, post : Self) { }

// SLIDE

// They're treated as ordinary fields in the invariants

    #[invariant]
    pub fn cap_tot(&self) -> bool {
        self.occupancy + self.permits == self.capacity
    }

    #[invariant]
    pub fn occ_cap(&self) -> bool {
        self.occupancy <= self.capacity
    }

// FIN

}}

// SLIDE 

// But non `variable` sharded state is passed around using rust's ownership disciple

fn main() { 

    let tracked (
        Tracked(lot), 
        Tracked(occupancy), 
        Tracked(permits), 
    ) = ParkingLot::Instance::initialize(3);

    proof {
        let tracked one_permit = permits.split(1);
        let tracked two_permit = permits.split(1);

        // ↓ enter *consumes* one unit of permit token, by taking ownership of it
        lot.enter(&mut occupancy, one_permit);
        lot.enter(&mut occupancy, two_permit);
        // ↓ leave *emits* one unit of permit token
        let new_permit = lot.leave(&mut occupancy);
        assert(occupancy.value() == 1)
    }

}

// FIN

/* SLIDE

The verus repo contains examples showing how to use linear tokens for various ways of "checking
out" ghost resources.

Examples include things like RW locks: locks are passed out and returned,
only one W lock at a time, as many R locks as you want, no R and W locks simultaneously.

Linearity enforces that you can only release a lock that you hold.

FIN */

/* SLIDE

But many patterns are imaginable.

Other features still not covered:

∙ storage sharding - storing fixed ghost values in the state machine
∙ refinement - proving one state machine refines another

FIN */

}

