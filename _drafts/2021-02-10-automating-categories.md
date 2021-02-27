
Problems to pose:
Finitely presented categories
Axiomatic categories - (equality questions over)
pullback of monic is monic
demonstrate universal properties or reason with them. There exists unique is a problem.




Look at category theory textbook to collect problems?
Higher falutin stuff. Adjunction reasoning Functor. Expressing the yoneda lemma.




Verify that concrete mathematical objects obey categroical axioms
Prove that any object that obeys categorical axiomns
In this case we have construction X, vs we always have constructin X.

Look at Isabelle. How automated are Isabelle category packages
TPTP encodings


Graphs vs terms


ATP - 
SMT - 
??? - Categorical automation


Automation takes a strong first order logic flavor.


EGraph techniques - EGraphs have risen in prominence recently thanks the egg paper and implementation, but the core idea is quite old.


Knuth Bendix
Operad book


Biting off obviously manageable chunks - Extremely constrained
Finite categories
Finitely presented categories



Fabirizio whatever's company
Ryan wisknesky's company
That python category thing
GAP categories



Given f : A -> B and g : B -> A such that f.g = 1 and g.f = 1, show that 
any other such g' must equal g.

f.g = id(A)
g.f = id(B)
f.g2 = id(A)
g2 . f = id(B)

prove
g1 = g2

That's good. This is the analog of uniqueness of identity in group theory

Hmmmm... What if I took my yoneda lemma technique and used it in Vampire?
Typed terms.
What about a prove with intrinsic polymorphism support
https://link.springer.com/chapter/10.1007/978-3-030-51054-1_21


f g m m'

fof(  ![X]: f(g(X)) = m(g(X)) ) % square commutes
fof(     ) # pullabck condition
We need to qwuantify over morphisms, which FOL will not let us do.
Howveer, zipperposition offers lambda free HOL?




WWhat about automating co end calculus profunctor nonsense.
Hom(-,-)
????

could I use the standard rewrites of categories to develop something...
Equivalence proofs?
(a * b) + c etc. ordinary algebra.

adjunctions
a -> G b  <=> F a -> b 
kan extensions


