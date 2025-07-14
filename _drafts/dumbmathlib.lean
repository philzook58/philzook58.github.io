import Std.Data.HashMap
import Std.Data.HashSet

/-
Take mathlib stuff, try not to actually use mathlib.
https://leanprover-community.github.io/mathematics_in_lean/
-/

/-

https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Category/Basic.html#CategoryTheory.Category

-/
class Category obj where
  hom : obj -> obj -> Type
  id : (X : obj) -> hom X X
  comp : {X Y Z : obj} -> hom Y Z -> hom X Y -> hom X Z


instance : Category Type where
  hom x y := x -> y
  id := fun X => fun (x : X) => x
  comp := fun f g x => f (g x)



/-
Even talking about the reals is tough.


Balancing a pendulum using gym.
Hmmmmmmmm.
Bouncing dvd logo


-/



/-
instance {X : Type} [BEq X] [Hashable X]: Category (Std.HashSet X) where
  hom x y := Std.HashMap X X
  id x := Std.HashMap.ofList (x.toList.map (fun a => (a, a)))
  comp f g := f.map (fun k v => g.findD k )
-/
