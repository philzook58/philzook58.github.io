theory isabelleplay
  imports Complex_Main
begin
print_commands
(*
find_consts
find_
prf
*)

value "1 + 2::nat"
(*  Comment *)
lemma "a \<Longrightarrow> b"

find_theorems "_ \<longrightarrow> _" 
find_theorems "_ \<and> _ \<longrightarrow> _"
find_theorems name:impI
find_consts name:list
(* lemma is nameless? *)
lemma "p \<and> q \<longrightarrow> p::bool"
  apply (rule impI)
  apply (erule conjunct1)
  done
(* drule erule frule *)
(* cheatsheet https://www.inf.ed.ac.uk/teaching/courses/ar/isabelle/FormalCheatSheet.pdf *)

find_consts "_ \<Rightarrow> _"
(*
Arrows
\<longrightarrow> implication?
\<rightarrow> ?
\<Rightarrow> function
\<Longrightarrow> inference rule? Sequent?
*)

lemma "1 = 2"
  apply (rule eq.sym)
  (* by auto *)
(*
auto 
force
blast
arith
clairfy
clarsimp
*)
lemma "s \<inter> t \<subseteq> s"
by (rule Set.Int_lower1)


theorem foo : "1 + 2 = 3"
  by simp

datatype aexpr = Lit nat | Plus aexpr aexpr
print_theorems (* datatype defines a ton of theorems*)
find_consts aexpr

find_consts 

value "1 + 2::nat"
print_theorems

value "(1::nat) # []"
find_consts name:"Lam [_]._"
find_consts name:sin
find_theorems sin
(* my commented isabelle https://www.lri.fr/~wolff/papers/other/TR_my_commented_isabelle.pdf *)
ML val x = 1 + 2
(*
  declare [[show_types]]
  declare [[show_sorts]]
declare [[show_consts]]
*)
(* ctrl + hover 
https://stackoverflow.com/questions/15489508/how-do-i-view-hidden-type-variables-in-isabelle-proof-goals
I get burned by bad type inference a lot *)
lemma "sin x \<le> (1::real)"
  apply (rule Transcendental.sin_le_one)
  done
find_theorems "(sin _ * sin _)"
find_theorems name:sin_cos_sq


lemma "cos (x::real) * Transcendental.cos x + sin x * sin x = (1::real)"
  by simp (* but the other direction doesn't work *)
 lemma "sin x * sin x + cos (x::real) * cos x  = (1::real)"
   apply   

end