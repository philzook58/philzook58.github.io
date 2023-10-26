inductive Term where
  | Var : String -> Term
  | Fn : String -> List Term -> Term

def Subst := List (String × Term)
def walk subst t : Term :=
  match t with
  | Var s => match subst.find (_ == s) with
    | Some t => walk subst t
    | None => t
  | Fn f ts => Fn f (ts.map (walk subst))

def unify t1 t2 subst : Option Subst :=
  match t1,t2 with
  | Var s1, Var s2 => if s1 == s2 then some subst else some ((s1,t2)::subst)

def disj := 
def conj :=

