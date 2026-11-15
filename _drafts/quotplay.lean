
/-
Quotients huh


QITIT

-/
#check Quot
#check Quotient
#print Setoid

#check Quotient.mk
#check Quotient.lift
#check Quotient.ind

def mytwo := Quot (fun a b : Nat => a % 2 = b % 2)
def a : mytwo := Quot.mk _ (3 : Nat)
