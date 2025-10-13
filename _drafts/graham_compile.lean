import Std.Internal.Parsec
import Lean.Data

inductive L_Var.Sym
| quote : String → Sym
deriving Repr, BEq

instance : ToString L_Var.Sym where
  toString : L_Var.Sym → String
  | .quote x => x

inductive L_Var.Expr
| plus : Expr → Expr → Expr
| minus : Expr → Expr → Expr
| negative : Expr → Expr
| read : Expr
| int : Int → Expr
| var : Sym → Expr
| let : Sym → Expr → Expr → Expr
deriving Repr

inductive L_Var.Program
| Program : Expr → Program

open Std.Internal
open Parsec.String
open Std.Internal.Parsec

def L_Var.Expr.parse_int : Parsec String.Iterator Expr := do
  let minus ← optional (pchar '-')
  let value ← digits
  match minus with
  | .some _ => pure $ .int (value * -1)
  | .none => pure $ .int value

def L_Var.Sym.parse_sym : Parsec String.Iterator Sym := do
  let char_array ← pchar '\'' *> many1 asciiLetter
  pure $ .quote ⟨ char_array.toList ⟩

def L_Var.Expr.parse_var : Parsec String.Iterator Expr :=
  Sym.parse_sym >>= pure ∘ .var

def L_Var.Expr.parse_atom := parse_var <|> parse_int

mutual

unsafe def L_Var.Expr.parse_complex : Parsec String.Iterator Expr :=
  pchar '(' *> ws *> parse_inner <* ws <* pchar ')'

unsafe def L_Var.Expr.parse_plus : Parsec String.Iterator Expr :=
  plus <$> (pchar '+' *> ws *> parse_expr) <*> (ws *> parse_expr)

unsafe def L_Var.Expr.parse_minus : Parsec String.Iterator Expr :=
  minus <$> (pchar '-' *> ws *> parse_expr) <*> (ws *> parse_expr)

unsafe def L_Var.Expr.parse_negative : Parsec String.Iterator Expr :=
  negative <$> (pstring "-" *> ws *> parse_expr)

unsafe def L_Var.Expr.parse_read : Parsec String.Iterator Expr :=
  pstring "read" *> pure read

unsafe def L_Var.Expr.parse_let : Parsec String.Iterator Expr :=
  Expr.let <$> (pstring "let" *> ws *> Sym.parse_sym) <*> (ws *> parse_expr) <*> (ws *> parse_expr)

unsafe def L_Var.Expr.parse_inner : Parsec String.Iterator Expr :=
  parse_plus <|> parse_read <|> attempt parse_minus <|> parse_negative <|> parse_let

unsafe def L_Var.Expr.parse_expr : Parsec String.Iterator Expr :=
  parse_atom <|> parse_complex

end

def L_Var.Expr.eval_expr : Lean.AssocList Sym Int → Expr → IO Int
| env, .plus a b => (. + .) <$> eval_expr env a <*> eval_expr env b
| env, .minus a b => (. - .) <$> eval_expr env a <*> eval_expr env b
| env, .negative a => (. * -1) <$> eval_expr env a
| ___, .int i => pure i
| ___, .read => IO.getStdin >>= IO.FS.Stream.getLine >>= pure ∘ parseDigits
| env, .var x => match env.find? x with | .some i => pure i | .none => MonadExceptOf.throw $ IO.userError s!"undefined variable {x}"
| env, .let v x body => eval_expr env x >>= fun x => eval_expr (env.insert v x) body
where parseDigits s := match Parser.run digits s with | .ok n => n | _ => 0

unsafe def L_Var.Expr.eval_str (s : String) : IO Int :=
  match parse_expr s.iter with
  | .success _ res => eval_expr .nil res
  | .error _ _ => MonadExceptOf.throw $ IO.userError "Couldn't Parse String"

#eval L_Var.Expr.eval_str "(let 'x 1 (+ 'x 'x))"
