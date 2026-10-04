

--example (e1 : T  -> T) (e2 : T)
--   (h : e1 = (fun y => e2)) :
--    := by

example[Inhabited T] (e1 e2 : T -> T)
   (h : (fun x y => e1 x) = (fun x y => e2 y)) :
   exists e3, e1 = (fun x => e3) /\ e2 = (fun x => e3)
    := by
    exists e1 default
    constructor
    funext






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
#check congr
#check congrFun hf a
#check congr hf h
#check congrFun'
#check Eq.mp
#check Eq.mpr
#check h ▸ value
