


Here's a fun gizmo.


A thing that disturbs me about OCaml modules compared to Haskell typeclasses is that it is not clear how to use them to build something that manipulates types.
Typeclasses instance declarations are a kind of restricted typelevel prolog.

```haskell
data Nat = Succ Nat | Zero
class Plus(a,b,c) where

instance Plus `Zero y y where
instance Plus x y z => Plus (`Succ x) y (`Succ z) where
```

```prolog
plus(zero, Y, Y).
plus(succ(X),Y,succ(Z)) :- plus(X,Y,Z)
```

You can achieve this in ocaml using gadts.

```ocaml
type 'a succ
type zero
type (_,_,_) plus =
  | PZero : (zero, 'a, 'a) plus
  | PSucc : ('x, 'y, 'z) plus -> ('x succ, 'y, 'z succ) plus
```

Gadts are however unmoving. You will need to build the evidence

```ocaml
type _ snat =
    | SZero : zero snat
    | SSucc : 'a snat -> 'a succ snat
type ('x, 'y) eplus = EPlus of 'z snat * ('x,'y,'z) plus
let plus : forall x y. x snat -> y snat -> (x, y) eplus
```

Modules themselves are kind of their own dependent type system bolted on.
They are dependent in the sense that modules may contain module signatures. A Functor that takes in a module may refer to this module signature in the type of it's result

```coq
Record Wrapper := {
    T : Type
    v : T
}.

Definition unwrap (x : Wrapper) : x.(T) := x.(v).
```

```ocaml
module type Wrapper = sig
    module type T
    module v : T
end

module UnWrap (X : Wrapper) : X.T = X.v
```

We can also use the finally tagless style as an alternative to the GADT style `(_,_,_) plus` above. It is sometimes said that finally tagless achieves what GADTs do in more ordinary ocaml.
The finally tagless signature is the pattern matching function. Actually it isn't quite. We should quantify over repr.

```coq
Inductive Plus : nat -> nat -> nat -> Type :=
    | PZero : forall y, Plus 0 y y
    | PSucc : forall x y z, Plus x y z -> Plus (Succ x) y (Succ z)
    .

Print Plus_rec.
(*   *)

Fixpoint plus_rec (x y z : nat) (repr : nat -> nat -> nat -> Type) (p : Plus x y z) (pzero : repr 0 y y) (psucc : repr -> ) : repr x y z :=
    match p with
    | PZero => repr 0 y y
    | PSucc p => 
    end
```

```ocaml
module type PLUS = sig
    type (_,_,_) repr
    val pzero : (zero, 'y, 'y) repr
    val psucc : ('x, 'y, 'z) repr -> ('x succ, 'y, 'z succ) repr
end

module Gadt : PLUS = struct
    type ('a,'b,'c) repr = ('a,'b,'c) plus
    let pzero = Pzero
    let psucc p = PSucc p
end
```
