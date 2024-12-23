opaque β : Type

-- tacti hyigene false?

inductive AExp : Type where
  | num : ℤ -> AExp
  | var : String -> AExp
  | add : AExp -> AExp -> AExp

inductive MyList  (a : Type) where
  | nil : MyList a
  | cons : a -> MyList a -> MyList a

#check MyList
#print MyList


-- I am shocked this goes throgyh
def fib n := if n = 0
    then 1
    else if n = 1
    then 1
    else fib (n - 1) + fib (n - 2)
#print fib


theorem double_negation_exclude_middle : (forall a, ¬ ¬ a -> a) -> forall b, b ∨ ¬ b := by
  intro dn
  intro b
  apply dn
  intro p
  apply p
  right
  intro r
  apply p
  left
  exact r

#print double_negation_exclude_middle


def dn2 : (forall a, ¬ ¬ a -> a) -> forall b, b ∨ ¬ b :=
  fun dn b => dn _ (fun p => p (Or.inr (fun b1 => p (Or.inl b1))))
