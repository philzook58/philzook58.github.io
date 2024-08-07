(declare-sort Gat 0)
(declare-fun Hom (Gat Gat) Gat)
(declare-fun typo (Gat) Gat)
(declare-fun id (Gat) Gat)
(declare-fun compose (Gat Gat) Gat)
(declare-fun Ob () Gat)
(declare-fun otimes (Gat Gat) Gat)
(declare-fun otimeso (Gat Gat) Gat)
(declare-fun munit () Gat)
(declare-fun braid (Gat Gat) Gat)
(declare-fun mcopy (Gat) Gat)
(declare-fun delete (Gat) Gat)
(declare-fun pair (Gat Gat) Gat)
(declare-fun proj1 (Gat Gat) Gat)
(declare-fun proj2 (Gat Gat) Gat)
(declare-fun B () Gat)
(declare-fun A () Gat)
(assert (forall ((A Gat)) (=> true (= (typo (id A)) (Hom A A)))))
(assert (forall ((A Gat) (B Gat) (C Gat) (f Gat) (g Gat))
  (=> (and (= (typo f) (Hom A B)) (= (typo g) (Hom B C)))
      (= (typo (compose f g)) (Hom A C)))))
;(assert (forall ((A Gat) (B Gat)) (=> true (= (typo (otimeso A B)) Ob))))
(assert (forall ((A Gat) (B Gat) (C Gat) (D Gat) (f Gat) (g Gat))
  (=> (and (= (typo f) (Hom A B)) (= (typo g) (Hom C D)))
      (= (typo (otimes f g)) (Hom (otimeso A C) (otimeso B D))))))
(assert (= (typo munit) Ob))
(assert (forall ((A Gat) (B Gat))
  (=> true (= (typo (braid A B)) (Hom (otimeso A B) (otimeso B A))))))
(assert (forall ((A Gat)) (=> true (= (typo (mcopy A)) (Hom A (otimeso A A))))))
(assert (forall ((A Gat)) (=> true (= (typo (delete A)) (Hom A munit)))))
(assert (forall ((A Gat) (B Gat) (C Gat) (f Gat) (g Gat))
  (=> (and (= (typo f) (Hom A B)) (= (typo g) (Hom A C)))
      (= (typo (pair f g)) (Hom A (otimeso B C))))))
(assert (forall ((A Gat) (B Gat)) (=> true (= (typo (proj1 A B)) (Hom (otimeso A B) A)))))
(assert (forall ((A Gat) (B Gat)) (=> true (= (typo (proj2 A B)) (Hom (otimeso A B) B)))))
(assert (forall ((A Gat) (B Gat) (C Gat) (D Gat) (f Gat) (g Gat) (h Gat))
  (=> (and (= (typo f) (Hom A B)) (= (typo g) (Hom B C)) (= (typo h) (Hom C D)))
      (= (compose (compose f g) h) (compose f (compose g h))))))
(assert (forall ((A Gat) (B Gat) (f Gat))
  (=> (and (= (typo f) (Hom A B))) (= (compose f (id B)) f))))
(assert (forall ((A Gat) (B Gat) (f Gat))
  (=> (and (= (typo f) (Hom A B))) (= (compose (id A) f) f))))
(assert (forall ((A Gat) (B Gat) (C Gat))
  (=> true (= (otimeso (otimeso A B) C) (otimeso A (otimeso B C))))))
(assert (forall ((A Gat)) (=> true (= (otimeso A munit) A))))
(assert (forall ((A Gat)) (=> true (= (otimeso munit A) A))))
(assert (forall ((A Gat)
         (B Gat)
         (C Gat)
         (X Gat)
         (Y Gat)
         (Z Gat)
         (f Gat)
         (g Gat)
         (h Gat))
  (=> (and (= (typo f) (Hom A X)) (= (typo g) (Hom B Y)) (= (typo h) (Hom C Z)))
      (= (otimes (otimes f g) h) (otimes f (otimes g h))))))
(assert (forall ((A Gat)
         (B Gat)
         (C Gat)
         (X Gat)
         (Y Gat)
         (Z Gat)
         (f Gat)
         (h Gat)
         (g Gat)
         (k Gat))
  (=> (and (= (typo f) (Hom A B))
           (= (typo h) (Hom B C))
           (= (typo g) (Hom X Y))
           (= (typo k) (Hom Y Z)))
      (= (compose (otimes f g) (otimes h k))
         (otimes (compose f h) (compose g k))))))
(assert (forall ((A Gat) (B Gat)) (=> true (= (id (otimeso A B)) (otimes (id A) (id B))))))
(assert (forall ((A Gat) (B Gat))
  (=> true (= (compose (braid A B) (braid B A)) (id (otimeso A B))))))
(assert (forall ((A Gat) (B Gat) (C Gat))
  (let ((a!1 (= (braid A (otimeso B C))
                (compose (otimes (braid A B) (id C))
                         (otimes (id B) (braid A C))))))
    (=> true a!1))))
(assert (forall ((A Gat) (B Gat) (C Gat))
  (let ((a!1 (= (braid (otimeso A B) C)
                (compose (otimes (id A) (braid B C))
                         (otimes (braid A C) (id B))))))
    (=> true a!1))))
(assert (forall ((A Gat) (B Gat) (C Gat) (D Gat) (f Gat) (g Gat))
  (=> (and (= (typo f) (Hom A B)) (= (typo g) (Hom C D)))
      (= (compose (otimes f g) (braid B D)) (compose (braid A C) (otimes g f))))))
(assert (forall ((A Gat))
  (let ((a!1 (= (compose (mcopy A) (otimes (mcopy A) (id A)))
                (compose (mcopy A) (otimes (id A) (mcopy A))))))
    (=> true a!1))))
(assert (forall ((A Gat))
  (let ((a!1 (= (compose (mcopy A) (otimes (delete A) (id A))) (id A))))
    (=> true a!1))))
(assert (forall ((A Gat))
  (let ((a!1 (= (compose (mcopy A) (otimes (id A) (delete A))) (id A))))
    (=> true a!1))))
(assert (forall ((A Gat)) (=> true (= (compose (mcopy A) (braid A A)) (mcopy A)))))
(assert (forall ((A Gat) (B Gat))
  (let ((a!1 (compose (otimes (mcopy A) (mcopy B))
                      (otimes (otimes (id A) (braid A B)) (id B)))))
    (=> true (= (mcopy (otimes A B)) a!1)))))
(assert (forall ((A Gat) (B Gat))
  (=> true (= (delete (otimeso A B)) (otimes (delete A) (delete B))))))
(assert (= (mcopy munit) (id munit)))
(assert (= (delete munit) (id munit)))
(assert (forall ((A Gat) (B Gat) (C Gat) (f Gat) (g Gat))
  (=> (and (= (typo f) (Hom C A)) (= (typo g) (Hom C B)))
      (= (pair f g) (compose (mcopy C) (otimes f g))))))
(assert (forall ((A Gat) (B Gat)) (=> true (= (proj1 A B) (otimes (id A) (delete B))))))
(assert (forall ((A Gat) (B Gat)) (=> true (= (proj2 A B) (otimes (delete A) (id B))))))
(assert (forall ((A Gat) (B Gat) (f Gat))
  (=> (and (= (typo f) (Hom A B)))
      (= (compose f (mcopy B)) (compose (mcopy A) (otimes f f))))))
(assert (forall ((A Gat) (B Gat) (f Gat))
  (=> (and (= (typo f) (Hom A B))) (= (compose f (delete B)) (delete A)))))
;(assert (let ((a!1 (=> true ;(and (= (typo A) Ob) (= (typo B) Ob))
;               (= (pair (proj1 A B) (proj2 A B)) (otimes (id A) (id B))))))
;  (not a!1)))
(assert   (not  ( =  (pair (delete A)  (pair (id A) (delete A))) (id A)   )))


  (check-sat)