%% SZS status Success
%% SZS output start ListOfTFF
%$ :produce-proofs true
%% Types:
tff('Gat', type, 'Gat': $tType).

%% Declarations:
tff(munit, type, munit: 'Gat').
tff(braid, type, braid: ('Gat' * 'Gat') > 'Gat').
tff('Ob', type, 'Ob': 'Gat').
tff(typo, type, typo: 'Gat' > 'Gat').
tff(delete, type, delete: 'Gat' > 'Gat').
tff('Hom', type, 'Hom': ('Gat' * 'Gat') > 'Gat').
tff(compose, type, compose: ('Gat' * 'Gat') > 'Gat').
tff(otimes, type, otimes: ('Gat' * 'Gat') > 'Gat').
tff(mcopy, type, mcopy: 'Gat' > 'Gat').
tff(proj1, type, proj1: ('Gat' * 'Gat') > 'Gat').
tff('A', type, 'A': 'Gat').
tff(pair, type, pair: ('Gat' * 'Gat') > 'Gat').
tff(proj2, type, proj2: ('Gat' * 'Gat') > 'Gat').
tff(id, type, id: 'Gat' > 'Gat').

%% Assertions:
%% ∀ A:Gat ((typo(A) = Ob) ⇒ (typo(id(A)) = Hom(A, A)))
tff(formula_1, axiom,
( ! [A:'Gat'] :
( (typo(A) = 'Ob')
=> (typo(id(A)) = 'Hom'(A, A))))).

%% ∀ A:Gat B:Gat C:Gat f:Gat g:Gat (((typo(A) = Ob) ∧ (typo(B) = Ob) ∧ (typo(C) = Ob) ∧ (typo(f) = Hom(A, B)) ∧ (typo(g) = Hom(B, C))) ⇒ (typo(compose(f, g)) = Hom(A, C)))
tff(formula_2, axiom,
( ! [A:'Gat', B:'Gat', C:'Gat', F:'Gat', G:'Gat'] :
( ( (typo(A) = 'Ob')
& (typo(B) = 'Ob')
& (typo(C) = 'Ob')
& (typo(F) = 'Hom'(A, B))
& (typo(G) = 'Hom'(B, C)))
=> (typo(compose(F, G)) = 'Hom'(A, C))))).

%% ∀ A:Gat B:Gat (((typo(A) = Ob) ∧ (typo(B) = Ob)) ⇒ (typo(otimes(A, B)) = Ob))
tff(formula_3, axiom,
( ! [A:'Gat', B:'Gat'] :
( ( (typo(A) = 'Ob')
& (typo(B) = 'Ob'))
=> (typo(otimes(A, B)) = 'Ob')))).

%% ∀ A:Gat B:Gat C:Gat D:Gat f:Gat g:Gat (((typo(A) = Ob) ∧ (typo(B) = Ob) ∧ (typo(C) = Ob) ∧ (typo(D) = Ob) ∧ (typo(f) = Hom(A, B)) ∧ (typo(g) = Hom(C, D))) ⇒ (typo(otimes(f, g)) = Hom(otimes(A, C), otimes(B, D))))
tff(formula_4, axiom,
( ! [A:'Gat', B:'Gat', C:'Gat', D:'Gat', F:'Gat', G:'Gat'] :
( ( (typo(A) = 'Ob')
& (typo(B) = 'Ob')
& (typo(C) = 'Ob')
& (typo(D) = 'Ob')
& (typo(F) = 'Hom'(A, B))
& (typo(G) = 'Hom'(C, D)))
=> (typo(otimes(F, G)) = 'Hom'(otimes(A, C), otimes(B, D)))))).

%% (typo(munit) = Ob)
tff(formula_5, axiom,
(typo(munit) = 'Ob')).

%% ∀ A:Gat B:Gat (((typo(A) = Ob) ∧ (typo(B) = Ob)) ⇒ (typo(braid(A, B)) = Hom(otimes(A, B), otimes(B, A))))
tff(formula_6, axiom,
( ! [A:'Gat', B:'Gat'] :
( ( (typo(A) = 'Ob')
& (typo(B) = 'Ob'))
=> (typo(braid(A, B)) = 'Hom'(otimes(A, B), otimes(B, A)))))).

%% ∀ A:Gat ((typo(A) = Ob) ⇒ (typo(mcopy(A)) = Hom(A, otimes(A, A))))
tff(formula_7, axiom,
( ! [A:'Gat'] :
( (typo(A) = 'Ob')
=> (typo(mcopy(A)) = 'Hom'(A, otimes(A, A)))))).

%% ∀ A:Gat ((typo(A) = Ob) ⇒ (typo(delete(A)) = Hom(A, munit)))
tff(formula_8, axiom,
( ! [A:'Gat'] :
( (typo(A) = 'Ob')
=> (typo(delete(A)) = 'Hom'(A, munit))))).

%% ∀ A:Gat B:Gat C:Gat f:Gat g:Gat (((typo(A) = Ob) ∧ (typo(B) = Ob) ∧ (typo(C) = Ob) ∧ (typo(f) = Hom(A, B)) ∧ (typo(g) = Hom(A, C))) ⇒ (typo(pair(f, g)) = Hom(A, otimes(B, C))))
tff(formula_9, axiom,
( ! [A:'Gat', B:'Gat', C:'Gat', F:'Gat', G:'Gat'] :
( ( (typo(A) = 'Ob')
& (typo(B) = 'Ob')
& (typo(C) = 'Ob')
& (typo(F) = 'Hom'(A, B))
& (typo(G) = 'Hom'(A, C)))
=> (typo(pair(F, G)) = 'Hom'(A, otimes(B, C)))))).

%% ∀ A:Gat B:Gat (((typo(A) = Ob) ∧ (typo(B) = Ob)) ⇒ (typo(proj1(A, B)) = Hom(otimes(A, B), A)))
tff(formula_10, axiom,
( ! [A:'Gat', B:'Gat'] :
( ( (typo(A) = 'Ob')
& (typo(B) = 'Ob'))
=> (typo(proj1(A, B)) = 'Hom'(otimes(A, B), A))))).

%% ∀ A:Gat B:Gat (((typo(A) = Ob) ∧ (typo(B) = Ob)) ⇒ (typo(proj2(A, B)) = Hom(otimes(A, B), B)))
tff(formula_11, axiom,
( ! [A:'Gat', B:'Gat'] :
( ( (typo(A) = 'Ob')
& (typo(B) = 'Ob'))
=> (typo(proj2(A, B)) = 'Hom'(otimes(A, B), B))))).

%% ∀ A:Gat B:Gat C:Gat D:Gat f:Gat g:Gat h:Gat (((typo(A) = Ob) ∧ (typo(B) = Ob) ∧ (typo(C) = Ob) ∧ (typo(D) = Ob) ∧ (typo(f) = Hom(A, B)) ∧ (typo(g) = Hom(B, C)) ∧ (typo(h) = Hom(C, D))) ⇒ (compose(compose(f, g), h) = compose(f, compose(g, h))))
tff(formula_12, axiom,
( ! [A:'Gat', B:'Gat', C:'Gat', D:'Gat', F:'Gat', G:'Gat', H:'Gat'] :
( ( (typo(A) = 'Ob')
& (typo(B) = 'Ob')
& (typo(C) = 'Ob')
& (typo(D) = 'Ob')
& (typo(F) = 'Hom'(A, B))
& (typo(G) = 'Hom'(B, C))
& (typo(H) = 'Hom'(C, D)))
=> (compose(compose(F, G), H) = compose(F, compose(G, H)))))).

%% ∀ A:Gat B:Gat f:Gat (((typo(A) = Ob) ∧ (typo(B) = Ob) ∧ (typo(f) = Hom(A, B))) ⇒ (compose(f, id(B)) = f))
tff(formula_13, axiom,
( ! [A:'Gat', B:'Gat', F:'Gat'] :
( ( (typo(A) = 'Ob')
& (typo(B) = 'Ob')
& (typo(F) = 'Hom'(A, B)))
=> (compose(F, id(B)) = F)))).

%% ∀ A:Gat B:Gat f:Gat (((typo(A) = Ob) ∧ (typo(B) = Ob) ∧ (typo(f) = Hom(A, B))) ⇒ (compose(id(A), f) = f))
tff(formula_14, axiom,
( ! [A:'Gat', B:'Gat', F:'Gat'] :
( ( (typo(A) = 'Ob')
& (typo(B) = 'Ob')
& (typo(F) = 'Hom'(A, B)))
=> (compose(id(A), F) = F)))).

%% ∀ A:Gat B:Gat C:Gat (((typo(A) = Ob) ∧ (typo(B) = Ob) ∧ (typo(C) = Ob)) ⇒ (otimes(otimes(A, B), C) = otimes(A, otimes(B, C))))
tff(formula_15, axiom,
( ! [A:'Gat', B:'Gat', C:'Gat'] :
( ( (typo(A) = 'Ob')
& (typo(B) = 'Ob')
& (typo(C) = 'Ob'))
=> (otimes(otimes(A, B), C) = otimes(A, otimes(B, C)))))).

%% ∀ A:Gat ((typo(A) = Ob) ⇒ (otimes(A, munit) = A))
tff(formula_16, axiom,
( ! [A:'Gat'] :
( (typo(A) = 'Ob')
=> (otimes(A, munit) = A)))).

%% ∀ A:Gat ((typo(A) = Ob) ⇒ (otimes(munit, A) = A))
tff(formula_17, axiom,
( ! [A:'Gat'] :
( (typo(A) = 'Ob')
=> (otimes(munit, A) = A)))).

%% ∀ A:Gat B:Gat C:Gat X:Gat Y:Gat Z:Gat f:Gat g:Gat h:Gat (((typo(A) = Ob) ∧ (typo(B) = Ob) ∧ (typo(C) = Ob) ∧ (typo(X) = Ob) ∧ (typo(Y) = Ob) ∧ (typo(Z) = Ob) ∧ (typo(f) = Hom(A, X)) ∧ (typo(g) = Hom(B, Y)) ∧ (typo(h) = Hom(C, Z))) ⇒ (otimes(otimes(f, g), h) = otimes(f, otimes(g, h))))
tff(formula_18, axiom,
( ! [A:'Gat', B:'Gat', C:'Gat', X:'Gat', Y:'Gat', Z:'Gat', F:'Gat', G:'Gat', H:'Gat'] :
( ( (typo(A) = 'Ob')
& (typo(B) = 'Ob')
& (typo(C) = 'Ob')
& (typo(X) = 'Ob')
& (typo(Y) = 'Ob')
& (typo(Z) = 'Ob')
& (typo(F) = 'Hom'(A, X))
& (typo(G) = 'Hom'(B, Y))
& (typo(H) = 'Hom'(C, Z)))
=> (otimes(otimes(F, G), H) = otimes(F, otimes(G, H)))))).

%% ∀ A:Gat B:Gat C:Gat X:Gat Y:Gat Z:Gat f:Gat h:Gat g:Gat k:Gat (((typo(A) = Ob) ∧ (typo(B) = Ob) ∧ (typo(C) = Ob) ∧ (typo(X) = Ob) ∧ (typo(Y) = Ob) ∧ (typo(Z) = Ob) ∧ (typo(f) = Hom(A, B)) ∧ (typo(h) = Hom(B, C)) ∧ (typo(g) = Hom(X, Y)) ∧ (typo(k) = Hom(Y, Z))) ⇒ (compose(otimes(f, g), otimes(h, k)) = otimes(compose(f, h), compose(g, k))))
tff(formula_19, axiom,
( ! [A:'Gat', B:'Gat', C:'Gat', X:'Gat', Y:'Gat', Z:'Gat', F:'Gat', H:'Gat', G:'Gat', K:'Gat'] :
( ( (typo(A) = 'Ob')
& (typo(B) = 'Ob')
& (typo(C) = 'Ob')
& (typo(X) = 'Ob')
& (typo(Y) = 'Ob')
& (typo(Z) = 'Ob')
& (typo(F) = 'Hom'(A, B))
& (typo(H) = 'Hom'(B, C))
& (typo(G) = 'Hom'(X, Y))
& (typo(K) = 'Hom'(Y, Z)))
=> (compose(otimes(F, G), otimes(H, K)) = otimes(compose(F, H), compose(G, K)))))).

%% ∀ A:Gat B:Gat (((typo(A) = Ob) ∧ (typo(B) = Ob)) ⇒ (id(otimes(A, B)) = otimes(id(A), id(B))))
tff(formula_20, axiom,
( ! [A:'Gat', B:'Gat'] :
( ( (typo(A) = 'Ob')
& (typo(B) = 'Ob'))
=> (id(otimes(A, B)) = otimes(id(A), id(B)))))).

%% ∀ A:Gat B:Gat (((typo(A) = Ob) ∧ (typo(B) = Ob)) ⇒ (compose(braid(A, B), braid(B, A)) = id(otimes(A, B))))
tff(formula_21, axiom,
( ! [A:'Gat', B:'Gat'] :
( ( (typo(A) = 'Ob')
& (typo(B) = 'Ob'))
=> (compose(braid(A, B), braid(B, A)) = id(otimes(A, B)))))).

%% ∀ A:Gat B:Gat C:Gat let a!1=(braid(A, otimes(B, C)) = compose(otimes(braid(A, B), id(C)), otimes(id(B), braid(A, C)))) in (((typo(A) = Ob) ∧ (typo(B) = Ob) ∧ (typo(C) = Ob)) ⇒ a!1)
tff(formula_22, axiom,
( ! [A:'Gat', B:'Gat', C:'Gat'] :
( ( (typo(A) = 'Ob')
& (typo(B) = 'Ob')
& (typo(C) = 'Ob'))
=> (braid(A, otimes(B, C)) = compose(otimes(braid(A, B), id(C)), otimes(id(B), braid(A, C))))))).

%% ∀ A:Gat B:Gat C:Gat let a!1=(braid(otimes(A, B), C) = compose(otimes(id(A), braid(B, C)), otimes(braid(A, C), id(B)))) in (((typo(A) = Ob) ∧ (typo(B) = Ob) ∧ (typo(C) = Ob)) ⇒ a!1)
tff(formula_23, axiom,
( ! [A:'Gat', B:'Gat', C:'Gat'] :
( ( (typo(A) = 'Ob')
& (typo(B) = 'Ob')
& (typo(C) = 'Ob'))
=> (braid(otimes(A, B), C) = compose(otimes(id(A), braid(B, C)), otimes(braid(A, C), id(B))))))).

%% ∀ A:Gat B:Gat C:Gat D:Gat f:Gat g:Gat (((typo(A) = Ob) ∧ (typo(B) = Ob) ∧ (typo(C) = Ob) ∧ (typo(D) = Ob) ∧ (typo(f) = Hom(A, B)) ∧ (typo(g) = Hom(C, D))) ⇒ (compose(otimes(f, g), braid(B, D)) = compose(braid(A, C), otimes(g, f))))
tff(formula_24, axiom,
( ! [A:'Gat', B:'Gat', C:'Gat', D:'Gat', F:'Gat', G:'Gat'] :
( ( (typo(A) = 'Ob')
& (typo(B) = 'Ob')
& (typo(C) = 'Ob')
& (typo(D) = 'Ob')
& (typo(F) = 'Hom'(A, B))
& (typo(G) = 'Hom'(C, D)))
=> (compose(otimes(F, G), braid(B, D)) = compose(braid(A, C), otimes(G, F)))))).

%% ∀ A:Gat let a!1=(compose(mcopy(A), otimes(mcopy(A), id(A))) = compose(mcopy(A), otimes(id(A), mcopy(A)))) in ((typo(A) = Ob) ⇒ a!1)
tff(formula_25, axiom,
( ! [A:'Gat'] :
( (typo(A) = 'Ob')
=> (compose(mcopy(A), otimes(mcopy(A), id(A))) = compose(mcopy(A), otimes(id(A), mcopy(A))))))).

%% ∀ A:Gat let a!1=(compose(mcopy(A), otimes(delete(A), id(A))) = id(A)) in ((typo(A) = Ob) ⇒ a!1)
tff(formula_26, axiom,
( ! [A:'Gat'] :
( (typo(A) = 'Ob')
=> (compose(mcopy(A), otimes(delete(A), id(A))) = id(A))))).

%% ∀ A:Gat let a!1=(compose(mcopy(A), otimes(id(A), delete(A))) = id(A)) in ((typo(A) = Ob) ⇒ a!1)
tff(formula_27, axiom,
( ! [A:'Gat'] :
( (typo(A) = 'Ob')
=> (compose(mcopy(A), otimes(id(A), delete(A))) = id(A))))).

%% ∀ A:Gat ((typo(A) = Ob) ⇒ (compose(mcopy(A), braid(A, A)) = mcopy(A)))
tff(formula_28, axiom,
( ! [A:'Gat'] :
( (typo(A) = 'Ob')
=> (compose(mcopy(A), braid(A, A)) = mcopy(A))))).

%% ∀ A:Gat B:Gat let a!1=compose(otimes(mcopy(A), mcopy(B)), otimes(otimes(id(A), braid(A, B)), id(B))) in (((typo(A) = Ob) ∧ (typo(B) = Ob)) ⇒ (mcopy(otimes(A, B)) = a!1))
tff(formula_29, axiom,
( ! [A:'Gat', B:'Gat'] :
( ? [A_bang_1_6:'Gat'] :
( (A_bang_1_6 = compose(otimes(mcopy(A), mcopy(B)), otimes(otimes(id(A), braid(A, B)), id(B))))
& ( ( (typo(A) = 'Ob')
& (typo(B) = 'Ob'))
=> (mcopy(otimes(A, B)) = A_bang_1_6)))))).

%% ∀ A:Gat B:Gat (((typo(A) = Ob) ∧ (typo(B) = Ob)) ⇒ (delete(otimes(A, B)) = otimes(delete(A), delete(B))))
tff(formula_30, axiom,
( ! [A:'Gat', B:'Gat'] :
( ( (typo(A) = 'Ob')
& (typo(B) = 'Ob'))
=> (delete(otimes(A, B)) = otimes(delete(A), delete(B)))))).

%% (mcopy(munit) = id(munit))
tff(formula_31, axiom,
(mcopy(munit) = id(munit))).

%% (delete(munit) = id(munit))
tff(formula_32, axiom,
(delete(munit) = id(munit))).

%% ∀ A:Gat B:Gat C:Gat f:Gat g:Gat (((typo(A) = Ob) ∧ (typo(B) = Ob) ∧ (typo(C) = Ob) ∧ (typo(f) = Hom(C, A)) ∧ (typo(g) = Hom(C, B))) ⇒ (pair(f, g) = compose(mcopy(C), otimes(f, g))))
tff(formula_33, axiom,
( ! [A:'Gat', B:'Gat', C:'Gat', F:'Gat', G:'Gat'] :
( ( (typo(A) = 'Ob')
& (typo(B) = 'Ob')
& (typo(C) = 'Ob')
& (typo(F) = 'Hom'(C, A))
& (typo(G) = 'Hom'(C, B)))
=> (pair(F, G) = compose(mcopy(C), otimes(F, G)))))).

%% ∀ A:Gat B:Gat (((typo(A) = Ob) ∧ (typo(B) = Ob)) ⇒ (proj1(A, B) = otimes(id(A), delete(B))))
tff(formula_34, axiom,
( ! [A:'Gat', B:'Gat'] :
( ( (typo(A) = 'Ob')
& (typo(B) = 'Ob'))
=> (proj1(A, B) = otimes(id(A), delete(B)))))).

%% ∀ A:Gat B:Gat (((typo(A) = Ob) ∧ (typo(B) = Ob)) ⇒ (proj2(A, B) = otimes(delete(A), id(B))))
tff(formula_35, axiom,
( ! [A:'Gat', B:'Gat'] :
( ( (typo(A) = 'Ob')
& (typo(B) = 'Ob'))
=> (proj2(A, B) = otimes(delete(A), id(B)))))).

%% ∀ A:Gat B:Gat f:Gat (((typo(A) = Ob) ∧ (typo(B) = Ob) ∧ (typo(f) = Hom(A, B))) ⇒ (compose(f, mcopy(B)) = compose(mcopy(A), otimes(f, f))))
tff(formula_36, axiom,
( ! [A:'Gat', B:'Gat', F:'Gat'] :
( ( (typo(A) = 'Ob')
& (typo(B) = 'Ob')
& (typo(F) = 'Hom'(A, B)))
=> (compose(F, mcopy(B)) = compose(mcopy(A), otimes(F, F)))))).

%% ∀ A:Gat B:Gat f:Gat (((typo(A) = Ob) ∧ (typo(B) = Ob) ∧ (typo(f) = Hom(A, B))) ⇒ (compose(f, delete(B)) = delete(A)))
tff(formula_37, axiom,
( ! [A:'Gat', B:'Gat', F:'Gat'] :
( ( (typo(A) = 'Ob')
& (typo(B) = 'Ob')
& (typo(F) = 'Hom'(A, B)))
=> (compose(F, delete(B)) = delete(A))))).

%% ¬((typo(A) = Ob) ⇒ (pair(delete(A), pair(id(A), delete(A))) = id(A)))
tff(formula_38, conjecture,
( ( (typo('A') = 'Ob')
=> (pair(delete('A'), pair(id('A'), delete('A'))) = id('A'))))).

%% SZS output end ListOfTFF
%% File generated by smttotptp version 0.9.9 (2/3/2016) from cartcat.smt