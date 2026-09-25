example (a b : Int) (pfab : a = b) : a = b := by
   let e0 := a
   let p0 : a = e0 := Eq.refl e0
   let p2 : e0 = e0 := Eq.refl e0
   let e1 := b
   let p3 : b = e1 := Eq.refl e1
   let p5 : e1 = e1 := Eq.refl e1
   let p6 : e0 = e1 := trans (Eq.symm p2) (trans pfab p5)
   let p7  := Eq.trans p6 p5
   let p8  := Eq.trans p7 p5
   exact trans (Eq.trans p0 p5) (Eq.symm (trans p3 p5))
