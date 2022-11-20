From Ltac2 Require Import Ltac2.
(* need this line to acivate ltac2*)
From Ltac2 Require Option.
From Ltac2 Require List.
From Ltac2 Require Import Message.
(* https://github.com/coq/coq/tree/master/test-suite/ltac2 *)
(* https://github.com/tchajed/ltac2-tutorial/blob/master/src/ltac2_tutorial.v *)
Ltac2 dl_step (db : constr) := print (of_constr db).

Ltac2 get_head (l : constr list) :=  match l with
  | x :: xs => Some x
  | [] => None
  end.

Ltac2 print_option x := match x with 
| Some c => print (of_constr c)
| None => print (of_string "None")
end.
Ltac2 Eval dl_step constr:(True).

Goal True.
Proof. dl_step constr:(True). 
print_option (get_head ['False]).