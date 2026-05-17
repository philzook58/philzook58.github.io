
def sumn (x : Nat) :=
  if x == 0 then 0 else x + sumn (x - 1)
  decreasing_by grind

def sumacc (x acc : Nat) :=
  if x == 0 then acc else sumacc (x-1) (x + acc)
  decreasing_by grind

theorem sumacc_sum (x : Nat) : forall acc, sumacc x acc = acc + sumn x := by
  induction x
