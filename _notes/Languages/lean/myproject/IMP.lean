-- From Coq Require Import Arith ZArith Psatz Bool String List Program.Equality.
-- Require Import Sequences.
/-   -/
-- Local Open Scope string_scope.
-- Local Open Scope Z_scope.
-- Local Open Scope list_scope.

-- import home.philip.Documents.lean.std4.Std.Data.Int.Basics
import std.Std.Data.List.Basic

#eval Lean.versionString
#eval 1 + 1
#check (1 : Int)
#check "string"

/-
-- (** * 1. The source language: IMP *)
-/
-- (** ** 1.1 Arithmetic expressions *)


def ident : Type := String
#check String
-- def mythree : Nat := 3
-- type ident = string

-- (** The abstract syntax: an arithmetic expression is either... *)
def myid : forall {a :Type}, a -> a := fun x => x
def myid2 : {a :Type} -> a -> a := fun x => x
#check myid

inductive aexp where
  | CONST (n : Int) : aexp --                      (**r a constant, or *)
  | VAR (x : ident) : aexp --                   (**r a variable, or *)
  | PLUS (a1 : aexp) (a2 : aexp) : aexp --        (**r a sum of two expressions, or *)
  | MINUS (a1 : aexp) (a2 : aexp) : aexp --      (**r a difference of two expressions *)


/-(** The denotational semantics: an evaluation function that computes
  the integer value denoted by an expression.  It is parameterized by
  a store [s] that associates values to variables. *)
-/


def store : Type := ident -> Int

def aeval (s: store) (a: aexp) : Int :=
  match a with
  | aexp.CONST n => n
  | aexp.VAR x => s x
  | aexp.PLUS a1 a2 => aeval s a1 + aeval s a2
  | aexp.MINUS a1 a2 => aeval s a1 - aeval s a2


--(** Such evaluation functions / denotational semantics have many uses.
--    First, we can use [aeval] to evaluate a given expression in a given store. *)

#eval (aeval (fun _x => 2) (aexp.PLUS (aexp.VAR "x") (aexp.MINUS (aexp.VAR "x") (aexp.CONST 1))))

-- (** Result is: [ = 3 : Z ]. *)

-- (** We can also do partial evaluation with respect to an unknown store *)
open aexp
-- #eval (fun s => aeval s (PLUS (VAR "x") (MINUS (CONST 10) (CONST 1))))


--(** Result is: [ = fun s : store => s "x" + 9 ]. *)

-- (** We can prove properties of a given expression. *)


theorem aeval_xplus1 :
  forall (s :store) (x :ident), aeval s (PLUS (VAR x) (CONST 1)) > aeval s (VAR x) := by 
  intros
  delta aeval
  simp
  




/-
Proof.
  intros. cbn. lia.
Qed.
-/
/-
(** Finally, we can prove "meta-properties" that hold for all expressions.
  For example: the value of an expression depends only on the values of its
  free variables.

  Free variables are defined by this recursive predicate:
*)

Fixpoint free_in_aexp (x: ident) (a: aexp) : Prop :=
  match a with
  | CONST n => False
  | VAR y => y = x
  | PLUS a1 a2 | MINUS a1 a2 => free_in_aexp x a1 \/ free_in_aexp x a2
  end.

Theorem aeval_free:
  forall s1 s2 a,
  (forall x, free_in_aexp x a -> s1 x = s2 x) ->
  aeval s1 a = aeval s2 a.
Proof.
  induction a; cbn; intros SAMEFREE.
- (* Case a = CONST n *)
  auto.
- (* Case a = VAR x *)
  apply SAMEFREE. auto.
- (* Case a = PLUS a1 a2 *)
  rewrite IHa1, IHa2. auto. auto. auto.
- (* Case a = MINUS a1 a2 *)
  rewrite IHa1, IHa2; auto.
Qed.

(** *** Exercise (1 star, recommended). *)
(** Add support for multiplication in arithmetic expressions.
  Modify the [aexp] type and the [aeval] function accordingly. *)

(** *** Exercise (2 stars, recommended). *)
(** Add support for division and for detecting arithmetic overflow.
  With this extension, the evaluation of an expression can produce an
  error: integer division by zero or result that exceeds the range
  [[min_int, max_int]].  You can either change the type of the
  function [aeval] to
<<
  aeval: store -> aexp -> option Z
>>
  with [None] meaning "error" and [Some n] meaning "success with
  result n".  Alternatively, you can define the semantics as a
  relation instead of a function:
<<
  Inductive aeval_rel: store -> aexp -> Z -> Prop := ...
>>
  Some definitions you can use:
*)

Definition min_int := - (2 ^ 63).
Definition max_int := 2 ^ 63 - 1.
Definition check_for_overflow (n: Z): option Z :=
  if n <? min_int then None else if n >? max_int then None else Some n.

(** ** 1.3 Boolean expressions *)

(** The IMP language has conditional statements (if/then/else) and
  loops.  They are controlled by expressions that evaluate to Boolean
  values.  Here is the abstract syntax of Boolean expressions. *)

Inductive bexp : Type :=
  | TRUE                              (**r always true *)
  | FALSE                             (**r always false *)
  | EQUAL (a1: aexp) (a2: aexp)       (**r whether [a1 = a2] *)
  | LESSEQUAL (a1: aexp) (a2: aexp)   (**r whether [a1 <= a2] *)
  | NOT (b1: bexp)                    (**r Boolean negation *)
  | AND (b1: bexp) (b2: bexp).        (**r Boolean conjunction *)

(** Just like arithmetic expressions evaluate to integers,
  Boolean expressions evaluate to Boolean values [true] or [false]. *)

Fixpoint beval (s: store) (b: bexp) : bool :=
  match b with
  | TRUE => true
  | FALSE => false
  | EQUAL a1 a2 => aeval s a1 =? aeval s a2
  | LESSEQUAL a1 a2 => aeval s a1 <=? aeval s a2
  | NOT b1 => negb (beval s b1)
  | AND b1 b2 => beval s b1 && beval s b2
  end.

(** There are many useful derived forms. *)

Definition NOTEQUAL (a1 a2: aexp) : bexp := NOT (EQUAL a1 a2).

Definition GREATEREQUAL (a1 a2: aexp) : bexp := LESSEQUAL a2 a1.

Definition GREATER (a1 a2: aexp) : bexp := NOT (LESSEQUAL a1 a2).

Definition LESS (a1 a2: aexp) : bexp := GREATER a2 a1.

Definition OR (b1 b2: bexp) : bexp := NOT (AND (NOT b1) (NOT b2)).

(** *** Exercise (1 star, recommended) *)
(** Show the expected semantics for the [OR] derived form: *)

Lemma beval_OR:
  forall s b1 b2, beval s (OR b1 b2) = beval s b1 || beval s b2.
Proof.
  intros; cbn.
  (* Hint: do "SearchAbout negb" to see the available lemmas about Boolean negation. *)
  (* Hint: or just do a case analysis on [beval s b1] and [beval s b2], there are
     only 4 cases to consider. *)
  (* FILL IN HERE *)
Abort.

(** ** 1.4 Commands *)

(** To complete the definition of the IMP language, here is the
  abstract syntax of commands, also known as statements. *)

Inductive com: Type :=
  | SKIP                                     (**r do nothing *)
  | ASSIGN (x: ident) (a: aexp)              (**r assignment: [v := a] *)
  | SEQ (c1: com) (c2: com)                  (**r sequence: [c1; c2] *)
  | IFTHENELSE (b: bexp) (c1: com) (c2: com) (**r conditional: [if b then c1 else c2] *)
  | WHILE (b: bexp) (c1: com).               (**r loop: [while b do c1 done] *)

(** We can write [c1 ;; c2] instead of [SEQ c1 c2], it is easier on the eyes. *)

Infix ";;" := SEQ (at level 80, right associativity).

(** Here is an IMP program that performs Euclidean division by
  repeated subtraction.  At the end of the program, "q" contains
  the quotient of "a" by "b", and "r" contains the remainder.
  In pseudocode:
<<
       r := a; q := 0;
       while b <= r do r := r - b; q := q + 1 done
>>
  In abstract syntax:
*)

Definition Euclidean_division :=
  ASSIGN "r" (VAR "a") ;;
  ASSIGN "q" (CONST 0) ;;
  WHILE (LESSEQUAL (VAR "b") (VAR "r"))
    (ASSIGN "r" (MINUS (VAR "r") (VAR "b")) ;;
     ASSIGN "q" (PLUS (VAR "q") (CONST 1))).

(** A useful operation over stores:
    [update x v s] is the store that maps [x] to [v] and is equal to [s] for
    all variables other than [x]. *)

Definition update (x: ident) (v: Z) (s: store) : store :=
  fun y => if string_dec x y then v else s y.

(** A naive approach to giving semantics to commands is to write an
  evaluation function [cexec s c] that runs the command [c] in initial
  store [s] and returns the final store when [c] terminates. *)

Fail Fixpoint cexec (s: store) (c: com) : store :=
  match c with
  | SKIP => s
  | ASSIGN x a => update x (aeval s a) s
  | SEQ c1 c2 => let s' := cexec s c1 in cexec s' c2
  | IFTHENELSE b c1 c2 => if beval s b then cexec s c1 else cexec s c2
  | WHILE b c1 =>
      if beval s b
      then (let s' := cexec s c1 in cexec s' (WHILE b c1))
      else s
  end.

(** The definition above is rejected by Coq, and rightly so, because
  all Coq functions must terminate, yet the [WHILE] case may not
  terminate.  Consider for example the infinite loop [WHILE TRUE
  SKIP].

  Worse, IMP is Turing-complete, since it has unbounded iteration
  ([WHILE]) plus arbitrary-precision integers.  Hence, there is no
  computable function [cexec s c] that would return [Some s'] if [c]
  terminates with store [s'], and [None] if [c] does not terminate.

  However, instead of computable functions, we can use a relation
  [cexec s c s'] that holds iff command [c], started in state [s],
  terminates with state [s'].  This relation can easily be defined as
  a Coq inductive predicate:
*)

Inductive cexec: store -> com -> store -> Prop :=
  | cexec_skip: forall s,
      cexec s SKIP s
  | cexec_assign: forall s x a,
      cexec s (ASSIGN x a) (update x (aeval s a) s)
  | cexec_seq: forall c1 c2 s s' s'',
      cexec s c1 s' -> cexec s' c2 s'' ->
      cexec s (SEQ c1 c2) s''
  | cexec_ifthenelse: forall b c1 c2 s s',
      cexec s (if beval s b then c1 else c2) s' ->
      cexec s (IFTHENELSE b c1 c2) s'
  | cexec_while_done: forall b c s,
      beval s b = false ->
      cexec s (WHILE b c) s
  | cexec_while_loop: forall b c s s' s'',
      beval s b = true -> cexec s c s' -> cexec s' (WHILE b c) s'' ->
      cexec s (WHILE b c) s''.

(** This style of semantics is known as natural semantics or big-step
  operational semantics.  The predicate [cexec s c s'] holds iff there
  exists a finite derivation of this conclusion, using the axioms and
  inference rules above.  The structure of the derivation represents
  the computations performed by [c] in a tree-like manner.  The
  finiteness of the derivation guarantees that only terminating
  executions satisfy [cexec].  Indeed, [WHILE TRUE SKIP] does not
  satisfy [cexec]: *)

Lemma cexec_infinite_loop:
  forall s, ~ exists s', cexec s (WHILE TRUE SKIP) s'.
Proof.
  assert (A: forall s c s', cexec s c s' -> c = WHILE TRUE SKIP -> False).
  { induction 1; intros EQ; inversion EQ.
  - subst b c. cbn in H. discriminate.
  - subst b c. apply IHcexec2. auto.
  }
  intros s (s' & EXEC). apply A with (s := s) (c := WHILE TRUE SKIP) (s' := s'); auto.
Qed.

(** Our naive idea of an execution function for commands was not
  completely off.  We can define an approximation of such a function
  by bounding a priori the recursion depth, using a [fuel] parameter
  of type [nat].  When the fuel drops to 0, [None] is returned,
  meaning that the final store could not be computed. *)

Fixpoint cexec_bounded (fuel: nat) (s: store) (c: com) : option store :=
  match fuel with
  | O => None
  | S fuel' =>
      match c with
      | SKIP => Some s
      | ASSIGN x a => Some (update x (aeval s a) s)
      | SEQ c1 c2 =>
          match cexec_bounded fuel' s c1 with
          | None  => None
          | Some s' => cexec_bounded fuel' s' c2
          end
      | IFTHENELSE b c1 c2 =>
          if beval s b then cexec_bounded fuel' s c1 else cexec_bounded fuel' s c2
      | WHILE b c1 =>
          if beval s b then
            match cexec_bounded fuel' s c1 with
            | None  => None
            | Some s' => cexec_bounded fuel' s' (WHILE b c1)
            end
          else Some s
      end
  end.

(** This bounded execution function is great for testing programs.
    For example, let's compute the quotient and the remainder of 14 by
    3 using the Euclidean division program above. *)

Eval compute in
  (let s := update "a" 14 (update "b" 3 (fun _ => 0)) in
   match cexec_bounded 100 s Euclidean_division with
   | None => None
   | Some s' => Some (s' "q", s' "r")
   end).

(** *** Exercise (3 stars, optional) *)
(** Relate the [cexec] relation with the [cexec_bounded] function by
  proving the following two lemmas. *)

Lemma cexec_bounded_sound:
  forall fuel s c s', cexec_bounded fuel s c = Some s' -> cexec s c s'.
Proof.
  induction fuel as [ | fuel ]; cbn; intros.
- discriminate.
- destruct c.
  (* FILL IN HERE *)
Abort.

Lemma cexec_bounded_complete:
  forall s c s', cexec s c s' ->
  exists fuel1, forall fuel, (fuel >= fuel1)%nat -> cexec_bounded fuel s c = Some s'.
Proof.
  induction 1.
  (* FILL IN HERE *)
Abort.

(** * 6. Small-step semantics for IMP *)

(** * 6.1 Reduction semantics *)

(** In small-step style, the semantics is presented as a one-step
  reduction relation [ red (c, s) (c', s') ], meaning that the command
  [c], executed in initial state [s], performs one elementary step of
  computation.  [s'] is the updated state after this step.  [c'] is
  the residual command, capturing all the computations that remain to
  be done.  *)

Inductive red: com * store -> com * store -> Prop :=
  | red_assign: forall x a s,
      red (ASSIGN x a, s) (SKIP, update x (aeval s a) s)
  | red_seq_done: forall c s,
      red (SEQ SKIP c, s) (c, s)
  | red_seq_step: forall c1 c s1 c2 s2,
      red (c1, s1) (c2, s2) ->
      red (SEQ c1 c, s1) (SEQ c2 c, s2)
  | red_ifthenelse: forall b c1 c2 s,
      red (IFTHENELSE b c1 c2, s) ((if beval s b then c1 else c2), s)
  | red_while_done: forall b c s,
      beval s b = false ->
      red (WHILE b c, s) (SKIP, s)
  | red_while_loop: forall b c s,
      beval s b = true ->
      red (WHILE b c, s) (SEQ c (WHILE b c), s).

(** *** Exercise (2 stars, recommended) *)
(** Show that Imp programs cannot go wrong.  Hint: first prove the following
  "progress" result for non-[SKIP] commands. *)

Lemma red_progress:
  forall c s, c = SKIP \/ exists c', exists s', red (c, s) (c', s').
Proof.
  induction c; intros.
  (* FILL IN HERE *)
Abort.

Definition goes_wrong (c: com) (s: store) : Prop :=
  exists c', exists s',
  star red (c, s) (c', s') /\ irred red (c', s') /\ c' <> SKIP.

Lemma not_goes_wrong:
  forall c s, ~(goes_wrong c s).
Proof.
  intros c s (c' & s' & STAR & IRRED & NOTSKIP).
  (* FILL IN HERE *)
Abort.

(** Sequences of reductions can go under a sequence context, generalizing
  rule [red_seq_step]. *)

Lemma red_seq_steps:
  forall c2 s c s' c',
  star red (c, s) (c', s') -> star red ((c;;c2), s) ((c';;c2), s').
Proof.
  intros. dependent induction H.
- apply star_refl.
- destruct b as [c1 st1].
  apply star_step with (c1;;c2, st1). apply red_seq_step. auto. auto.  
Qed.

(** We now recall the equivalence result between 
- termination according to the big-step semantics
- existence of a finite sequence of reductions to [SKIP]
  according to the small-step semantics.

We start with the implication big-step ==> small-step, which is
a straightforward induction on the big-step evaluation derivation. *)

Theorem cexec_to_reds:
  forall s c s', cexec s c s' -> star red (c, s) (SKIP, s').
Proof.
  induction 1.
- (* SKIP *)
  apply star_refl.
- (* ASSIGN *)
  apply star_one. apply red_assign. 
- (* SEQ *)
  eapply star_trans. apply red_seq_steps. apply IHcexec1.
  eapply star_step.  apply red_seq_done.  apply IHcexec2.
- (* IFTHENELSE *)
  eapply star_step. apply red_ifthenelse. auto.
- (* WHILE stop *)
  apply star_one. apply red_while_done. auto.
- (* WHILE loop *)
  eapply star_step. apply red_while_loop. auto.
  eapply star_trans. apply red_seq_steps. apply IHcexec1.
  eapply star_step. apply red_seq_done. apply IHcexec2.
Qed.

(** The reverse implication, from small-step to big-step, is more subtle.
The key lemma is the following, showing that one step of reduction
followed by a big-step evaluation to a final state can be collapsed
into a single big-step evaluation to that final state. *)

Lemma red_append_cexec:
  forall c1 s1 c2 s2, red (c1, s1) (c2, s2) ->
  forall s', cexec s2 c2 s' -> cexec s1 c1 s'.
Proof.
  intros until s2; intros STEP. dependent induction STEP; intros.
- (* red_assign *)
  inversion H; subst. apply cexec_assign. 
- (* red_seq_done *)
  apply cexec_seq with s2. apply cexec_skip. auto.
- (* red seq step *)
  inversion H; subst. apply cexec_seq with s'0.
  eapply IHSTEP; eauto.
  auto.
- (* red_ifthenelse *)
  apply cexec_ifthenelse. auto.
- (* red_while_done *)
  inversion H0; subst. apply cexec_while_done. auto.
- (* red while loop *)
  inversion H0; subst. apply cexec_while_loop with s'0; auto.
Qed.

(** As a consequence, a term that reduces to [SKIP] evaluates in big-step
  with the same final state. *)

Theorem reds_to_cexec:
  forall s c s',
  star red (c, s) (SKIP, s') -> cexec s c s'.
Proof.
  intros. dependent induction H.
- apply cexec_skip.
- destruct b as [c1 s1]. apply red_append_cexec with c1 s1; auto.
Qed.

(** ** 6.2 Transition semantics with continuations *)

(** We now introduce an alternate form of small-step semantics
  where the command to be executed is explicitly decomposed into:
- a sub-command under focus, where computation takes place;
- a continuation (or context) describing the position of this sub-command
  in the whole command, or, equivalently, describing the parts of the
  whole command that remain to be reduced once the sub-command is done.

As a consequence, the small-step semantics is presented as a
transition relation between triples (subcommand-under-focus,
continuation, state).  Previously, we had transitions between pairs
(whole-command, state).

The syntax of continuations is as follows:
*)

Inductive cont : Type :=
  | Kstop
  | Kseq (c: com) (k: cont)
  | Kwhile (b: bexp) (c: com) (k: cont).

(** Intuitive meaning of these constructors:
- [Kstop] means that, after the sub-command under focus terminates,
  nothing remains to be done, and execution can stop.  In other words,
  the sub-command under focus is the whole command.
- [Kseq c k] means that, after the sub-command terminates, we still need
  to execute command [c] in sequence, then continue as described by [k].
- [Kwhile b c k] means that, after the sub-command terminates, we still need
  to execute a loop [WHILE b DO c END], then continue as described by [k].
*)

(** Another way to forge intuitions about continuations is to ponder the following
  [apply_cont k c] function, which takes a sub-command [c] under focus
  and a continuation [k], and rebuilds the whole command.  It simply
  puts [c] in lefmost position in a nest of sequences as described by [k].
*)

Fixpoint apply_cont (k: cont) (c: com) : com :=
  match k with
  | Kstop => c
  | Kseq c1 k1 => apply_cont k1 (SEQ c c1)
  | Kwhile b1 c1 k1 => apply_cont k1 (SEQ c (WHILE b1 c1))
  end.

(** Transitions between (subcommand-under-focus, continuation, state)
  triples perform conceptually different kinds of actions:
- Computation: evaluate an arithmetic expression or boolean expression
  and modify the triple according to the result of the evaluation.
- Focusing: replace the sub-command by a sub-sub-command that is to be
  evaluated next, possibly enriching the continuation as a consequence.
- Resumption: when the sub-command is [SKIP] and therefore fully executed,
  look at the head of the continuation to see what to do next.

Here are the transition rules, classified by the kinds of actions they implement.
*)

Inductive step: com * cont * store -> com * cont * store -> Prop :=

  | step_assign: forall x a k s,              (**r computation for assignments *)
      step (ASSIGN x a, k, s) (SKIP, k, update x (aeval s a) s)

  | step_seq: forall c1 c2 s k,               (**r focusing for sequence *)
      step (SEQ c1 c2, k, s) (c1, Kseq c2 k, s)

  | step_ifthenelse: forall b c1 c2 k s,      (**r computation for conditionals *)
      step (IFTHENELSE b c1 c2, k, s) ((if beval s b then c1 else c2), k, s)

  | step_while_done: forall b c k s,          (**r computation for loops *)
      beval s b = false ->
      step (WHILE b c, k, s) (SKIP, k, s)

  | step_while_true: forall b c k s,          (**r computation and focusSKIing for loops *)
      beval s b = true ->
      step (WHILE b c, k, s) (c, Kwhile b c k, s)

  | step_skip_seq: forall c k s,              (**r resumption *)
      step (SKIP, Kseq c k, s) (c, k, s)

  | step_skip_while: forall b c k s,          (**r resumption *)
      step (SKIP, Kwhile b c k, s) (WHILE b c, k, s).


(** *** Extensions to other control structures *)

(** A remarkable feature of continuation semantics is that they extend very easily
  to other control structures besides "if-then-else" and "while" loops.
  Consider for instance the "break" construct of C, C++ and Java, which
  immediately terminates the nearest enclosing "while" loop.  Assume we
  extend the type of commands with a [BREAK] constructor.  Then, all we need
  to give "break" a semantics is to add two resumption rules:
<<
  | step_break_seq: forall c k s,
      step (BREAK, Kseq c k, s) (BREAK, k, s)
  | step_break_while: forall b c k s,
      step (BREAK, Kwhile b c k, s) (SKIP, k, s)
>>
  The first rule says that a [BREAK] statement "floats up" pending sequences,
  skipping over the computations they contain.  Eventually, a [Kwhile]
  continuation is encountered, meaning that the [BREAK] found its enclosing
  loop.  Then, the second rule discards the [Kwhile] continuation and
  turns the [BREAK] into a [SKIP], effectively terminating the loop.
  That's all there is to it!
**)

(** *** Exercise (2 stars, recommended) *)
(** Besides "break", C, C++ and Java also have a "continue" statement
  that terminates the current iteration of the enclosing loop,
  then resumes the loop at its next iteration (instead of stopping
  the loop like "break" does). Give the transition rules
  for the "continue" statement. *)

(** *** Exercise (3 stars, optional) *)
(** In Java, loops as well as "break" and "continue" statements carry
  an optional label.  "break" without a label exits out of the immediately
  enclosing loop, but "break lbl" exits out of the first enclosing loop
  that carries the label "lbl".  Similarly for "continue".
  Give the transition rules for "break lbl" and "continue lbl". *)

(** *** Relating the continuation semantics and the big-step semantics *)

(** *** Exercise (2 stars, optional) *)
(** Show that a big-step execution give rise to a sequence of steps to [SKIP].
  You can adapt the proof of theorem [cexec_to_reds] with minor changes. *)

Theorem cexec_to_steps:
  forall s c s', cexec s c s' -> forall k, star step (c, k, s) (SKIP, k, s').
Proof.
  induction 1; intros k.
  (* FILL IN HERE *)
Abort.

(** *** Exercise (3 stars, optional) *)
(** Show the converse result: a sequence of steps to [(SKIP, Kstop)] corresponds
  to a big-step execution.  You need a lemma similar to [red_append_cexec],
  but also a notion of big-step execution of a continuation. *)

Theorem steps_to_cexec:
  forall c s s', star step (c, Kstop, s) (SKIP, Kstop, s') -> cexec s c s'.
Proof.
  (* FILL IN HERE *)
Abort.