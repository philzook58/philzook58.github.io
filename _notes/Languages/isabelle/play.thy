theory play (* same as file name *)
imports Main (* You usually want Main *)
begin
(* https://isabelle.in.tum.de/doc/tutorial.pdf *)

(* defining a datatype *)
datatype 'a  MyList = MyNil | MyCons 'a "'a MyList"
(* What needs quotes "" vs what doesn't I find confusing 
I think it just infers a lot
*)

(*
difference between fun and primrec. fun is basically better.
https://stackoverflow.com/questions/30419419/what-is-the-difference-between-primrec-and-fun-in-isabelle-hol#:~:text=For%20algebraic%20datatypes%20without%20a,which%20can%20be%20rather%20tedious.
*)

primrec myapp :: "'a MyList \<Rightarrow> 'a MyList \<Rightarrow> 'a MyList"
  where
  "myapp MyNil x = x" 
| "myapp (MyCons x xs) ys = MyCons x (myapp xs ys)"

export_code myapp in OCaml module_name Foo
(* But also I already have definitions and notation imported 
from Main*)
value "[True , False]"
value "nil"

value "rev [True, False]"

definition foo :: nat where "foo = 3"


lemma "(1 :: nat) + 2 = 3"
  by simp

type_synonym bar = nat

lemma "union a b = union b a"
  apply (rule Groups.ac_simps)
  done

(* type \<lbrakk> using [ |  *) 
lemma test_theorem : "\<lbrakk>f a = a\<rbrakk> \<Longrightarrow>  f (f a) = a"
  print_state
  apply simp
  print_state
  done

print_commands
print_theory
print_theorems
print_locales

help

(* How do I model a new theory?
Locales I guess
https://lawrencecpaulson.github.io/2022/03/23/Locales.html


typedecl and axiomatization. To be avoided in many cases since it is easy to make an inconsistent tehory
https://isabelle.in.tum.de/library/HOL/HOL/Set.html
Set is axiomatized
*)

lemma "a \<in> (A :: 'a set) \<longrightarrow> a \<in> A \<union> B" 
  apply simp
  done

(*
Note the state panel on the right. 
Also a proof state checkbox in the output panel
*)

fun myadd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
   "myadd 0 x = x"
|  "myadd (Suc n) x = Suc (myadd n x)"
(* Found termination order: "(\<lambda>p. size (fst p)) <*mlex*> {}" *)

find_consts name:myadd
(* 
  play.myadd :: "nat \<Rightarrow> nat \<Rightarrow> nat"
  play.myadd_dom :: "nat \<times> nat \<Rightarrow> bool"
  play.myadd_sumC :: "nat \<times> nat \<Rightarrow> nat"
*)
value "True \<and> False \<or> True \<longrightarrow> False"
(* lemma "\<lambda>x. \<lambda>y. true = \<lambda>x. \<lambda>y. true" *)

find_theorems name:myadd
(*
found 6 theorem(s):
  play.myadd.simps(1): myadd 0 ?x = ?x
  play.myadd.simps(2): myadd (Suc ?n) ?x = Suc (myadd ?n ?x)
  play.myadd.induct:
    (\<And>x. ?P 0 x) \<Longrightarrow>
    (\<And>n x. ?P n x \<Longrightarrow> ?P (Suc n) x) \<Longrightarrow> ?P ?a0.0 ?a1.0
  play.myadd.cases:
    (\<And>x. ?x = (0, x) \<Longrightarrow> ?P) \<Longrightarrow>
    (\<And>n x. ?x = (Suc n, x) \<Longrightarrow> ?P) \<Longrightarrow> ?P
  play.myadd.elims:
    myadd ?x ?xa = ?y \<Longrightarrow>
    (\<And>x. ?x = 0 \<Longrightarrow> ?xa = x \<Longrightarrow> ?y = x \<Longrightarrow> ?P) \<Longrightarrow>
    (\<And>n x. ?x = Suc n \<Longrightarrow>
            ?xa = x \<Longrightarrow> ?y = Suc (myadd n x) \<Longrightarrow> ?P) \<Longrightarrow>
    ?P
  play.myadd.pelims:
    myadd ?x ?xa = ?y \<Longrightarrow>
    myadd_dom (?x, ?xa) \<Longrightarrow>
    (\<And>x. ?x = 0 \<Longrightarrow>
          ?xa = x \<Longrightarrow> ?y = x \<Longrightarrow> myadd_dom (0, x) \<Longrightarrow> ?P) \<Longrightarrow>
    (\<And>n x. ?x = Suc n \<Longrightarrow>
            ?xa = x \<Longrightarrow>
            ?y = Suc (myadd n x) \<Longrightarrow>
            myadd_dom (Suc n, x) \<Longrightarrow> ?P) \<Longrightarrow>
    ?P
*)


(*
https://isabelle.in.tum.de/library/Pure/Pure/Pure.html
Pure doesn't import anything. I followed an import chain
up from Set.
It is unfortunate that the deeper stuff is always magical.
Users do not need the sorts of things in this file
*)

(*
HOL theory
https://isabelle.in.tum.de/library/HOL/HOL/HOL.html

typedecl of bool
judgement command
*)

(*
https://isabelle.in.tum.de/library/HOL/HOL/Orderings.html
*)


(* https://lawrencecpaulson.github.io/2023/03/22/Binomial_Coeffs.html 
*)
value "binomial 3 1" 


end