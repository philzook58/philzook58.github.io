import Std.Internal.Parsec
import Lean.Data.Json.Parser
import Mathlib.Lean.Json
import Plausible
import Lean.Data.Json

open Std.Internal.Parsec
open Std.Internal.Parsec.String
open Lean.Json.Parser

#eval Parser.run digit "1"
#eval Parser.run (many digit) "12345"


inductive SExp where
  | atom : String -> SExp
  | list : Array SExp -> SExp
deriving Repr, Inhabited

def atomP := many1Chars (asciiLetter <|> digit )
#eval Parser.run atomP "12eSFS3"
partial def sexpP : Parser SExp :=
  (atomP >>= fun a => pure (SExp.atom a)) <|>
  (pchar '(' *>
    many (sexpP <* ws) >>= fun l =>
    pchar ')' *> pure (SExp.list l)
  )
#eval Parser.run sexpP "(foo (bar baz) quux)"

structure App where
  f : String
  args : Array App
deriving Repr, Inhabited, Lean.ToJson, Lean.FromJson

#eval (1, App.mk "f" #[] |> Lean.ToJson.toJson)
#check (2,3,4.0)
-- https://leanprover.zulipchat.com/#narrow/channel/113489-new-members/topic/Termination.20checking.20of.20structure.20with.20nested.20Array/near/569411040
-- Ok,I'm a dumbass thinking Array didn't work

/-
-- Ah the issue is actually with matching on array literals

def App.mysize3 (a : App) : Nat :=
  match a with
  | ⟨_, #[]⟩ => 1
  | ⟨_, args⟩ => 1 + (args.map mysize3 |>.sum)
  decreasing_by
  next h =>
  have p := Array.sizeOf_lt_of_mem h
  simp

-/

def App.mysize (a : App) : Nat :=
  match a with
  | ⟨_, args⟩ => 1 + (args.map mysize).sum

def App.mysizeOf (a : App) : Nat := 1 + (a.args.map mysizeOf).sum
  decreasing_by
    let ⟨_, args ⟩ := a
    decreasing_tactic

def App.mysize2 (a : App) : Nat :=
  match a with
  | ⟨_, args⟩ => 1 + (args.map mysize2 |> Array.sum)






-- Lean.ToJson, Lean.FromJson

#print App.rec
#print App._sizeOf_1

-- accepted with List but not Array
def App.mysize (a : App) : Nat :=
  match a with
  | ⟨_, []⟩ => 1
  | ⟨_, args⟩ => 1 + (args.map mysize |> Array.sum)

#eval App.mysize (App.mk "f" [])

-- https://leanprover-community.github.io/mathlib4_docs/Init/Data/List/Attach.html
-- List.attach
-- List.pmap
def App.mysizeOf (a : App) : Nat :=
  1 + (a.args.map mysizeOf).sum
  termination_by a
  decreasing_by
    simp [sizeOf, App._sizeOf_1]









--termination_by?

#eval (App.mk "f" #[]) |> sizeOf
#eval Lean.ToJson.toJson (App.mk "f" #[])
#eval (Lean.Json.parse r#"{"f" : "f", "args" : []}"#).toOption.get! |> Lean.FromJson.fromJson? (α := App)
-- Lean.FromJson.fromJson?) : Option App

-- https://dl.acm.org/doi/10.1145/3547640 do unchained
-- https://lean-lang.org/doc/reference/latest/Functors___-Monads-and--do--Notation/Syntax/#do-notation
#eval do
  let mut b := 1
  while b < 10 do
    b := b + 1
  return b


partial def is_eq (t s : App) : Bool :=
  if t.f != s.f || t.args.size != s.args.size then
    false
  else
    Array.zip t.args s.args |>.all (fun (a, b) => is_eq a b)

#eval is_eq (App.mk "f" #[]) (App.mk "f" #[])

partial def is_subterm (t s : App) : Bool :=
  if is_eq t s then
    true
  else
    t.args.any (fun a => is_subterm a s)
#eval do assert! is_subterm (App.mk "f" #[App.mk "g" #[]]) (App.mk "g" #[])
#eval do assert! is_subterm (App.mk "f" #[App.mk "g" #[]]) (App.mk "h" #[])
#check true
-- example: (is_subterm (App.mk "f" #[App.mk "g" #[]]) (App.mk "g" #[])) = true := by rfl
example : 1 + 2 = 3 := rfl
#eval Plausible.Testable.check <| forall x : Nat, x + 0 = x



--#eval Mathlib.Json
-- https://github.com/codyroux/simple-prolog/blob/master/SimpleProlog/Basic.lean
-- https://lean-lang.org/doc/reference/latest/Basic-Types/Maps-and-Sets/


/-
def papp : Parser App :=
  (many1Chars asciiLetter) >>= fun f =>
  (pchar '(' *>
    many (sexpP <* ws) >>= fun l =>
    pchar ')' *> pure (App.mk f l)
  ) <|>
  pure (App.mk f #[])
-/


def test_string := "foo(bar,baz(quux))"
