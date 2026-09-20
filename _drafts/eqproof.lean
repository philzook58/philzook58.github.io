
variable (a b : Nat)
variable (f g : Nat -> Nat)
variable (h : a = b)
variable (hf : f = g)
theorem ex1 : f a = f b := by
  congr

#print ex1
#check Eq.refl a
#check Eq.symm h
#check Eq.trans h (h.symm)
#check congrArg f h
#check congrFun hf a
#check congr hf h
#check congrFun'
#check Eq.mp
#check Eq.mpr
#check h ▸ value
