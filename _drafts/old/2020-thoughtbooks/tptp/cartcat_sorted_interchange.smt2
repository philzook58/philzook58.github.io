(set-option :produce-proofs true)
(declare-sort TYPE 0)
(declare-sort Ob 0)
(declare-sort Hom 0)
(declare-fun Hom (Ob Ob) TYPE)
(declare-fun typo (Hom) TYPE)
(declare-fun id (Ob) Hom)
(declare-fun compose (Hom Hom) Hom)
(declare-fun Ob () TYPE)
;(declare-fun typo (Ob) TYPE)
(declare-fun otimeso (Ob Ob) Ob)
(declare-fun otimes (Hom Hom) Hom)
(declare-fun munit () Ob)
(declare-fun braid (Ob Ob) Hom)
(declare-fun mcopy (Ob) Hom)
(declare-fun delete (Ob) Hom)
(declare-fun pair (Hom Hom) Hom)
(declare-fun proj1 (Ob Ob) Hom)
(declare-fun proj2 (Ob Ob) Hom)
(declare-fun B () Ob)
(declare-fun A () Ob)
(assert (forall ((A Ob)) (= (typo (id A)) (Hom A A))))
(assert (forall ((A Ob) (B Ob) (C Ob) (f Hom) (g Hom)) (!
  (=> (and (= (typo f) (Hom A B)) (= (typo g) (Hom B C)))
      (= (typo (compose f g)) (Hom A C)))
      :pattern (  (Hom A B) (Hom B C) (compose f g) )
      )))

(assert (forall ((A Ob) (B Ob) (C Ob) (D Ob) (f Hom) (g Hom)) (!
  (=> (and (= (typo f) (Hom A B)) (= (typo g) (Hom C D)))
      (= (typo (otimes f g)) (Hom (otimeso A C) (otimeso B D))))  
      :pattern (  (Hom A B) (Hom C D) (otimes f g) )
        )))

;(assert (forall ((A Ob) (B Ob) (C Ob) (D Ob) (f Hom) (g Hom)) (!
 ; (=> (and (= (typo f) (Hom A B)) (= (typo g) (Hom C D)))
  ;    (= (typo (otimes f g)) (Hom (otimeso A C) (otimeso B D))))  
   ;   :pattern (  (Hom (otimeso A C) (otimeso B D)) (otimes f g) )
    ;   )))









(assert (forall ((A Ob) (B Ob)) (!
  (= (typo (braid A B)) (Hom (otimeso A B) (otimeso B A)))
  :pattern ((braid A B))
  )))


(assert (forall ((A Ob)) (! 
(= (typo (mcopy A)) (Hom A (otimeso A A)))
:pattern ((mcopy A))
)))
(assert (forall ((A Ob)) (! (= (typo (delete A)) (Hom A munit))
:pattern ((delete A))
  )))
(assert (forall ((A Ob) (B Ob) (C Ob) (f Hom) (g Hom))
  (! (=> (and (= (typo f) (Hom A B)) (= (typo g) (Hom A C)))
      (= (typo (pair f g)) (Hom A (otimeso B C))))
      :pattern ((Hom A B) (Hom B C) (pair f g))
      )))

(assert (forall ((A Ob) (B Ob)) (! (= (typo (proj1 A B)) (Hom (otimeso A B) A))
:pattern ((proj1 A B))
)))
(assert (forall ((A Ob) (B Ob)) (! (= (typo (proj2 A B)) (Hom (otimeso A B) B))
:pattern ((proj2 A B))
)))



(assert (forall ((A Ob) (B Ob) (C Ob) (X Ob) (Y Ob) (Z Ob) (f Hom) (g Hom) (h Hom))
; maybe this one doesn't
  (=> (and (= (typo f) (Hom A X)) (= (typo g) (Hom B Y)) (= (typo h) (Hom C Z)))
      (= (otimes (otimes f g) h) (otimes f (otimes g h)))))
    )




(assert (forall ((A Ob) (B Ob) (C Ob) (D Ob) (f Hom) (g Hom))
  (=> (and (= (typo f) (Hom A B)) (= (typo g) (Hom C D)))
      (= (compose (otimes f g) (braid B D)) (compose (braid A C) (otimes g f))))))
(assert (forall ((A Ob))
  (= (compose (mcopy A) (otimes (mcopy A) (id A)))
     (compose (mcopy A) (otimes (id A) (mcopy A)))))) ; This has a terrible pattern. Patterns should be the full sides I think
(assert (forall ((A Ob)) (= (compose (mcopy A) (otimes (delete A) (id A))) (id A))))
(assert (forall ((A Ob)) (= (compose (mcopy A) (otimes (id A) (delete A))) (id A))))
(assert (forall ((A Ob)) (= (compose (mcopy A) (braid A A)) (mcopy A))))
;(assert (forall ((A Ob) (B Ob))
;  (let ((a!1 (compose (otimes (mcopy A) (mcopy B))
;                      (otimes (otimes (id A) (braid A B)) (id B)))))
;    (= (mcopy (otimeso A B)) a!1))))
;(assert (forall ((A Ob) (B Ob))
;  (= (delete (otimeso A B)) (otimes (delete A) (delete B)))))
(assert (= (mcopy munit) (id munit)))
(assert (= (delete munit) (id munit)))
; this predicate hurt the time a lot. It's probably because it needs it. And I'm not assertnig the axioms of category
(assert (forall ((A Ob) (B Ob) (C Ob) (f Hom) (g Hom))
  (=> (and (= (typo f) (Hom C A)) (= (typo g) (Hom C B)))
      (= (pair f g) (compose (mcopy C) (otimes f g)))))
      )






(assert (forall ((A Ob) (B Ob) (C Ob))
  (= (otimeso (otimeso A B) C) (otimeso A (otimeso B C)))))
(assert (forall ((A Ob)) (= (otimeso A munit) A)))
(assert (forall ((A Ob)) (= (otimeso munit A) A)))


(assert (forall ((A Ob)
         (B Ob)
         (C Ob)
         (X Ob)
         (Y Ob)
         (Z Ob)
         (f Hom)
         (h Hom)
         (g Hom)
         (k Hom))
  (=> (and (= (typo f) (Hom A B))
           (= (typo h) (Hom B C))
           (= (typo g) (Hom X Y))
           (= (typo k) (Hom Y Z)))
      (= (compose (otimes f g) (otimes h k))
         (otimes (compose f h) (compose g k)))))
         )


(assert (= (typo (id A)) (Hom A A)))
(assert (= (typo (id B)) (Hom B B)))

    (assert (not (= 
         (compose (otimes (mcopy A) (mcopy B)) (compose (otimes (id A) (otimes (braid A B) (id B))) 
                   (otimes (id A) (otimes (delete B) (otimes (delete A) (id B))))))

         (compose (otimes (mcopy A) (mcopy B)) (otimes (compose (id A) (id A)) (compose (otimes (braid A B) (id B))
                   (otimes (delete B) (otimes (delete A) (id B))))))

     )))

; If I give the types, this goes through. If I don't it doesn't
; requiring it to figure out the association made this way harder.
; This implies a big problem is the type inference.
; Well, that combined with it being much faster when I leave the guards off.
; albeit possibly unsound?
; And this isn't about composition. This is about 
;(assert (= (typo (otimes (braid A B) (id B))) (Hom (otimeso A (otimeso B B)) (otimeso B (otimeso A B)))))
;(assert (= (typo (delete A)) (Hom A munit)))
;(assert (= (typo (delete B)) (Hom B munit)))
;(assert (= (typo (otimes (delete B) (otimes (delete A) (id B)))) (Hom (otimeso B (otimeso A B))  B))) ; 30s wityh this only
;(assert (= (typo (otimes (delete B) (otimes (delete A) (id B)))) (Hom (otimeso B (otimeso A B))  (otimeso munit (otimeso munit B)))))
;(assert (= (typo (otimes (delete B) (otimes (delete A) (id B)))) (Hom (otimeso (otimeso B A) B)  B)))
;(assert (= (typo (otimes (delete B) (otimes (delete A) (id B)))) (Hom (otimeso (otimeso B A) B)  B)))



; We could perhaps use the theorem prover to determine which guards are unnecessary?
; We could typecheck the proof. If the proof doesn't use any steps that fail the typechecker, it's probably ok.
; That's sort of my criteria right now.

(check-sat)
(get-proof)