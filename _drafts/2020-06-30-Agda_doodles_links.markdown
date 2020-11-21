---
author: philzook58
comments: true
date: 2020-06-30 03:14:14+00:00
layout: post
link: https://www.philipzucker.com/?p=1284
published: false
slug: Agda doodles, links
title: Agda doodles, links
wordpress_id: 1284
---




Back on the agda train. I guess. Or should I be an idris boy? I want to try idris 2 but it feels not ready. Plus apparently agda has irrelevant notations?







Maybe I should try some of that homotopy stuff I wass trying in Haskell. Kind of defeats the point of "simp0lciity" to be in agda though







New mcbride notes [https://github.com/pigworker/ProgrammerCommaCon/tree/master/CS410-19/Lec](https://github.com/pigworker/ProgrammerCommaCon/tree/master/CS410-19/Lec)







Old mcbride notes document I'd never seen [http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.706.8140&rep=rep1&type=pdf](http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.706.8140&rep=rep1&type=pdf) Pretty cool







[http://citeseerx.ist.psu.edu/viewdoc/download;jsessionid=E3CD5927D73589F5E8AC1DE03CB29E05?doi=10.1.1.705.3086&rep=rep1&type=pdf](http://citeseerx.ist.psu.edu/viewdoc/download;jsessionid=E3CD5927D73589F5E8AC1DE03CB29E05?doi=10.1.1.705.3086&rep=rep1&type=pdf)







Dependently typed programming with finite sets







Decidable and Semidecidable. The same as recursive and recrusively enumerable. The same as some part of the arithemtic hierarchy













Observational Types Now says it has some artifact in Agda?







Relationship between theorem proving and partial evaluation. You have to case on stuff because it gets "stuck". Is this the trick? Lambda is the ultaimte abrtaction. I was oncsidering at one point using typeclasses to keep everything abstract that I wanted to stay folded. I guess this is ultimately the finally tagless style, where you use modules or typeclasses to carry around that huge outer lambda. "Charlike" 







Any equality that the compiler can't understand immediately is something that wouldn't partially evaluate to optimized form. If I have some   to . from = id, I want the compiler to know that by construction (basically by beta reduction). It gets blocked on abstract terms.







I did have some impression that Agda might be nice for 2Vect







You know  figuring out if two algerbaic expressions are identical: The easiest thing is to just evaluate them. Maybe define this indictively? Probing for equality.. "Auotmatic" equality. Probe n f.  ; holds n and f such that probing f n unique times is enough to determine equality of g f. n can be overestimate. nf+ ng => nq (I think )







nf * mg => (n + m) h. Why is this?Is this a general ring property or depends on nats?







const x = requires 1







multivariate multiplies probes. (tensoring) Is this inspired by plotkin's talk? Maybe.







Brute force SAT search, or List monad style search







(p : bool -> Set) -> (bool -> Dec (p x)) -> Dec (exists b, pb) - if forall b it's decidable if b satisfies p, it's decidable if b . Where was that website







(bool -> Dec (p x)) -> Dec (forall b, p b)







doit f with f true  f false =   







Maybe I want strong things than Dec p . That's just bools. sometimes I want more. Like, if I had a nat -> ? function, if it could tell me how far I am from the nearest region or truth, that would be nice. Or dual







Duals as proof objects. Give me a set of affine equations( many). If I can produce a vectorial combination of them that gives 0 = 1, then they are inconsistent. Nullstullensatz is analog for polynomial. Fa







Bezout as duals.







view from the left

























Try to do the final differentiation is automatic







2/20







  * [http://relmics.mcmaster.ca/RATH-Agda/RATH-Agda-2.0.0.pdf](http://relmics.mcmaster.ca/RATH-Agda/RATH-Agda-2.0.0.pdf) - Relation lagerba agda
  *   * [https://agda.readthedocs.io/en/v2.6.0.1/getting-started/tutorial-list.html](https://agda.readthedocs.io/en/v2.6.0.1/getting-started/tutorial-list.html)
  * [https://github.com/jespercockx/popl19-tutorial](https://github.com/jespercockx/popl19-tutorial)
  * [https://people.inf.elte.hu/divip/AgdaTutorial/Symbols.html](https://people.inf.elte.hu/divip/AgdaTutorial/Symbols.html)
  * [https://wenkokke.github.io/pubs/mpc2015.pdf](https://wenkokke.github.io/pubs/mpc2015.pdf) auto in agda






From agda-pkg project






    
    <code>agda-base            v0.2            https://github.com/pcapriotti/agda-base.git
    agda-categories      026658c         https://github.com/agda/agda-categories.git
    agda-metis           v0.2.1          https://github.com/jonaprieto/agda-metis.git
    agda-prelude         64b0eb2         https://github.com/UlfNorell/agda-prelude.git
    agda-prop            v0.1.2          https://github.com/jonaprieto/agda-prop.git
    agda-real            70b739a0        https://gitlab.com/pbruin/agda-real.git
    agda-ring-solver     d1ed21c         https://github.com/oisdk/agda-ring-solver.git
    agdarsec             v0.3.0          https://github.com/gallais/agdarsec.git
    alga-theory          0fdb96c         https://github.com/algebraic-graphs/agda.git
    ataca                a9a7c06         https://github.com/jespercockx/ataca.git
    cat                  v1.6.0          https://github.com/fredefox/cat.git
    cubical              v0.1            https://github.com/agda/cubical.git
    FiniteSets           c8c2600         https://github.com/L-TChen/FiniteSets.git
    fotc                 apia-1.0.2      https://github.com/asr/fotc.git
    hott-core            1037d82         https://github.com/HoTT/HoTT-Agda.git
    hott-theorems        1037d82         https://github.com/HoTT/HoTT-Agda.git
    HoTT-UF-Agda         3bdfe5c         https://github.com/martinescardo/HoTT-UF-Agda-Lecture-Notes.git
    lightweight-prelude  b2d440a         https://github.com/L-TChen/agda-lightweight-prelude.git
    MtacAR               mtac1           https://github.com/L-TChen/MtacAR.git
    plfa                 1dfd02f         https://github.com/plfa/plfa.github.io.git
    routing-library      thesis          https://github.com/MatthewDaggitt/agda-routing.git
    standard-library     v1.1            https://github.com/agda/agda-stdlib.git</code>












Agda. What a trip




Atom agda-mode seems acceptable




-- C-alt- is go to definiton?  

-- search is C-c C-z




https://atom.io/packages/agda-mode




-- https://homes.cs.washington.edu/~jrw12/#blog coq stuff




https://github.com/alhassy/gentle-intro-to-reflection




http://casperbp.net/posts/2019-04-nondeterminism-using-a-free-monad/index.html




https://gallais.github.io/blog/blog.Agda.html




https://serokell.io/blog/2018/11/30/playing-with-negation




https://mazzo.li/posts/AgdaSort.html




https://doisinkidney.com/




https://jozefg.bitbucket.io/posts/2014-09-21-what-are-dep-types-2.html




there is a more useful readme hidden. God that's dumb




https://github.com/agda/agda-stdlib/blob/master/README.agda




An exploration of the standard lib. Stops short unfortunately




http://neil-strickland.staff.shef.ac.uk/formal/agdalib.pdf




I need to stop playing with Nat and just do other stuff




more hotkeys. \bN gives funky N. \Gl gives lambda so does \lambda -> is fine




\all \forall




------------




Linear Functions category




A fun silly category



    
    -- from Conor mcBride's cs410 notes
    
    -- Cmonoid is kind of like the profunctor analog of the Const functor
    newtype CMonoid x a b = CMonoid x
    
    -- with the intent that a and b are ().
    -- using other indices doesn't necessarily hurt though.
    -- could constrain this with a constrained category
    instance Monoid x => Category CMonoid x a b where
       id = CMonoid mempty
       (CMonoid x) . (CMonoid y) = CMonoid (x <> y)




It would be fun to do some number theory style proofs.




record Prime {a : Nat}




(c : Nat -> b : Nat -> c \ne 1 -> b \ne 1 -> b * c == a -> Void) -> Prime a




If you look at the agda standard lib




https://github.com/agda/agda-stdlib/blob/master/src/Data/Nat/Divisibility.agda




Divisibility seems to be the first notion




m | n




The proof of such statement is to supply a divisor d and the equality proof d * m = n.




Divisiblity forms a partial order. if a divides b and b divides c then a divides c. a divides itself.




These are the first couple theorems.




Prime factorization is quite useful




Can we verify that the maximum of a list is bigger than anything in it? Really, we want that it is the least upper bound.



    
    open import Data.List
    open import Data.Rational
    import Data.Nat as Nat
    open Nat using (ℕ; zero; suc; _+_; _*_; _^_; _∸_; _⊓_; _⊔_; _≥_)
    open import Data.List.Membership.Setoid
    open import Data.Product
    open import Data.List.Any
    import Relation.Binary.PropositionalEquality as Eq
    open Eq using (_≡_; refl; cong; sym)
    open import Data.Nat.Properties
    
    
    mylist = 3 ∷ []
    
    
    -- min out of some set.
    -- min : s:(S M) -> ( n:M ,  ∀ {m : M} -> (m ∈ s) → n ≤ m)
    
    -- min : [ℕ] -> ℕ
    
    -- sqcup is max
    
    max' : ℕ -> List ℕ  -> ℕ
    max' x [] = x
    max' x (y ∷ ys) = max' (x ⊔ y) ys
    
    
    
    max : List ℕ -> ℕ 
    max xs = max' zero xs 
    
    _∈N_ : _
    _∈N_ = _∈_ (Eq.setoid ℕ) 
    
    test1 : 1 ∈N (1 ∷ [])
    test1 = here refl
    
    test2 : 1 ∈N (0 ∷ 1 ∷ [])
    test2 = there (here refl)
    
    {-
    max-good : ∀ {z : ℕ}  {xs : List ℕ } ->  z ∈N xs -> max xs ≥ z
    max-good {z}  {[]} ()
    max-good {z} {x ∷ xs} p with max (x :: xs)
                                     | x =  ?
                                     | max xs = {!!}
    -}
    
    injnat : {a : ℕ} {b : ℕ} -> suc a ≡ suc b -> a ≡ b
    injnat refl = refl
    
    cupimpl : {x : ℕ} {y : ℕ} -> x ⊔ y ≡ x -> x ≥ y 
    cupimpl {zero} {zero} _ = Nat.z≤n
    cupimpl {zero} {suc y} = λ ()
    cupimpl {suc x} {zero} _ =  Nat.z≤n
    cupimpl {suc x} {suc y} p = Nat.s≤s (cupimpl (injnat p)  )
    
    cupimply :  {x : ℕ} {y : ℕ} -> x ⊔ y ≡ y -> y ≥ x
    cupimply {x} {y} p rewrite ⊔-comm x y = cupimpl p
    
    
    max-tup : (ℕ × ℕ) -> ℕ 
    max-tup (x , y) = x ⊔ y  
    {-
    
    record myin
      left : myin a (a , b) 
      right : myin b (a , b) 
    
    -}
    
    
    -- max-tup-good : 
    
    -- simplein : 0 ∈ (1 ∷ 2 ∷ 0 ∷ [])
    -- simplein = ?
    
    
    
    -- rat : 
    -- rat = 3 ÷ 4
    
    {-
    record Rat : Set where
      field
        numerator : Data.Nat.Nat
        denominator : Nat
    -}
    
    -- \bN \bQ
    
    
    
    
    
    
    




Transitivty of <= is important.




Dynamic programming verified?



    
    -- open import Data.Rational
    import Data.Nat as Nat
    open Nat using (ℕ; zero; suc; _+_; _*_; _^_; _∸_; _⊓_; _⊔_; _≥_; _≤_;  _≟_; _≤?_ )
    open import Data.List.Membership.Setoid
    open import Data.Product
    open import Data.List.Any
    import Relation.Binary.PropositionalEquality as Eq
    open Eq using (_≡_; refl; cong; sym)
    open import Data.Nat.Properties
    open import Data.Maybe.Base
    open import Relation.Nullary using (¬_; Dec; yes; no)
    open import Relation.Unary using (Decidable)
    import Data.List.All as All
    open import Data.List.All.Properties
    open import Data.List
    mylist = 3 ∷ []
    
    
    
    
    -- min out of some set.
    -- min : s:(S M) -> ( n:M ,  ∀ {m : M} -> (m ∈ s) → n ≤ m)
    
    -- min : [ℕ] -> ℕ
    
    -- sqcup is max
    
    max' : ℕ -> List ℕ  -> ℕ
    max' x [] = x
    max' x (y ∷ ys) = max' (x ⊔ y) ys
    
    
    
    max : List ℕ -> ℕ 
    max xs = max' zero xs 
    
    _∈N_ : _
    _∈N_ = _∈_ (Eq.setoid ℕ) 
    
    test1 : 1 ∈N (1 ∷ [])
    test1 = here refl
    
    test2 : 1 ∈N (0 ∷ 1 ∷ [])
    test2 = there (here refl)
    
    
    max'' : List ℕ -> ℕ
    max'' [] = zero
    max'' (x ∷ xs) = x ⊔ max'' xs
    
    lt-lemma : ∀ {a b c : ℕ} -> (a ≤ b) -> a ≤ ( b ⊔ c )
    lt-lemma Nat.z≤n = Nat.z≤n
    lt-lemma {suc a} {suc b} {zero} (Nat.s≤s p) = Nat.s≤s p
    lt-lemma {suc a} {suc b} {(suc c)} (Nat.s≤s p)  with lt-lemma {a} {b} {c} p
    ...    | p' = Nat.s≤s p'
    
    lt-lemma² :  ∀ {a b c : ℕ} -> (a ≤ c) -> a ≤ ( b ⊔ c )
    lt-lemma² {a} {b} {c} p rewrite ⊔-comm b c = lt-lemma p
    
    max-good : ∀ {z : ℕ}  {xs : List ℕ } ->  z ∈N xs -> max'' xs ≥ z
    max-good {z} {[]} ()
    max-good {.x} {x ∷ xs} (here refl) = m≤m⊔n x (max'' xs)
    max-good {z} {x ∷ xs} (there p) with max-good {z} {xs} p
    ...                                 |  p' = lt-lemma² p'
    
    
    {-
    max-good : ∀ {z : ℕ}  {xs : List ℕ } ->  z ∈N xs -> max xs ≥ z
    max-good {z}  {[]} ()
    max-good {z} {x ∷ xs} p with max (x :: xs)
                                     | x =  ?
                                     | max xs = {!!}
    -}
    
    injnat : {a : ℕ} {b : ℕ} -> suc a ≡ suc b -> a ≡ b
    injnat refl = refl
    
    cupimpl : {x : ℕ} {y : ℕ} -> x ⊔ y ≡ x -> x ≥ y 
    cupimpl {zero} {zero} _ = Nat.z≤n
    cupimpl {zero} {suc y} = λ ()
    cupimpl {suc x} {zero} _ =  Nat.z≤n
    cupimpl {suc x} {suc y} p = Nat.s≤s (cupimpl (injnat p)  )
    
    cupimply :  {x : ℕ} {y : ℕ} -> x ⊔ y ≡ y -> y ≥ x
    cupimply {x} {y} p rewrite ⊔-comm x y = cupimpl p
    
    
    max-tup : (ℕ × ℕ) -> ℕ 
    max-tup (x , y) = x ⊔ y  
    
    KeyList : (k : Set) -> (a : Set) -> Set
    KeyList k a = List (k × a)
    
    filterPrices' :  (prices : KeyList ℕ ℕ) -> (length : ℕ) ->  KeyList ℕ ℕ 
    filterPrices' prices l = filter (λ { (p , x) -> p ≤? l} ) prices
    
    sub : {a b : ℕ} -> (a ≤ b) -> ℕ
    sub {0} {b} Nat.z≤n = b
    sub (Nat.s≤s p) = sub p
    
    -- Vec of prices?
    
    rod-cut : (prices : KeyList ℕ ℕ) -> (length : ℕ) -> ℕ
    rod-cut prices zero = zero
    rod-cut prices l with filterPrices' prices l
    rod-cut prices l | [] = zero
    rod-cut prices l | prices' = foldr _⊔_ 0  ( ( Data.List.map  (λ {( p , l2 ) -> {!!}  }) prices') )
    -- rod-cut prices' (sub p l)
    
    filterPrices :  (prices : KeyList ℕ ℕ) -> (length : ℕ) ->  KeyList ℕ ℕ
    filterPrices [] l = []
    filterPrices ((l , p) ∷ prices) l₂ with l ≤? l₂ 
    ...                                   | yes _ = (l , p) ∷ filterPrices prices l₂
    ...                                   | no _  = filterPrices prices l₂
    
    
    
    lookupk : ∀ {a : Set} -> ℕ -> List (ℕ × a) -> Maybe a
    lookupk key ((k , a) ∷ xs) with key ≟ k
    ...                          | yes _  = (just a)
    ...                          | no _ =  (lookupk key xs) 
    lookupk key [] = nothing
    
    myfromMaybe : ∀ {a} {A : Set a} -> A -> Maybe A -> A
    myfromMaybe x (just x₁) = x₁
    myfromMaybe x nothing = x
    
    price : (prices : List (ℕ × ℕ)) -> (cuts : List ℕ) -> ℕ 
    price prices (c ∷ cs) = (myfromMaybe 0 (lookupk c prices)) + (price prices cs)
    price prices [] = 0
    
    
    {-
    filterAll : {A : Set} -> (P : A -> Set) ->  (P? : Decidable P)  -> (xs : List A)  -> All P (filter P? xs)
    filterAll P? xs = ?
    -}
    
    {-
    
    myinv : ∀ {A : Mat n ℚ} {x : Vec n ℚ} -> Maybe (b : Vec n bQ) 
    matinv-pf : ∀ {A : Mat n ℕ} {x : Vec n  ℕ} -> matmul A (myinv A x) ≡ x
    
    
    
    fourier motzkin is an obvious 
    
    
    -}
    
    
    {-
    
    Stream ℚ
    
    
    
    converges : (s : Stream ℚ) -> ∀ (ε:ℚ) -> ∃ (n : ℕ) -> ∀ (m : ℕ) -> | s !! n - s !! m| ≤ ε
    converges 
    
    
    -}
    
    
    {-
    record Mem
      field
      fun : a -> b
      dict : Map a b
    
    memo : (a -> b) -> (Mem a -> b)
    
    
    evalmemo {f, d } a = maybe (find a d) (f a)
    
    
    memofix
    
    fix : 
    -}
    
    {-
    
    record myin
      left : myin a (a , b) 
      right : myin b (a , b) 
    
    -}
    
    
    -- max-tup-good : 
    
    -- simplein : 0 ∈ (1 ∷ 2 ∷ 0 ∷ [])
    -- simplein = ?
    
    
    
    -- rat : 
    -- rat = 3 ÷ 4
    
    {-
    record Rat : Set where
      field
        numerator : Data.Nat.Nat
        denominator : Nat
    -}
    
    -- \bN \bQ
    
    
    
    
    
    
    



    
    p1 : (x : ℕ) -> ℕ
    p1 x = x * x + 2 * x + 1 
    
    p2 : (x : ℕ) -> ℕ
    p2 x = x + 1
    
    lem : {x : ℕ} -> (x + 1) * (x + 1) ≡ (x * x + 2 * x + 1) 
    lem {x} rewrite *-distribʳ-+ (x + 1) x 1 |  *-distribˡ-+ x x 1 | +-identityʳ x | *-identityʳ x | +-identityʳ (x + 1) | sym (+-assoc (x * x + x) x 1) | sym (+-assoc (x * x) x x)
       = refl
    
    
    --    (x + 1) * (x + 1) ≡⟨ *-distribʳ-+ (x + 1) x 1 ⟩  x * (x + 1) + (x + 1 + 0)  ≡⟨ *-distribˡ-+ x x 1 ⟩  {! ?!} 
    
    
    
    divp1p2 : {a : ℕ} -> (p2 a) ∣ (p1 a)
    divp1p2 {a} = divides (a + 1) (sym (lem {a}))




Proof that output of one function is always a integer divisor of another function. Goofy Polynomial division kind of.




Reflecting Rings




Is this not also somewhat reminiscent of Free Monoids being lists. via foldMap



    
    class CommRing a where
      plus :: a -> a -> a
      times : a -> a -> a
      sub :: a -> a -> a
      idplus : a
      idtimes : a
      
    newtype Poly = Poly ZipList Int
    instance CommRing Poly where
      idplus = [1]
      idtimes = [0]
      sub x y = (-) <






    
    gt; x <*> y plus x y = (+) <






    
    gt; x <*> y times [] _ = [] times _ [] = [] times xss@(x: xs) yss@(y : ys) = x * y : (times xs yss + times xss ys) -- finally tagless style? Similar I suppose. -- kind of Poly is the initial version of CommRing -- reflect :: (forall a. CommRing a => a -> a) -> Poly reflect f = f idplus apply :: Poly -> (forall a. CommRing a => a -> a) apply Tree a = Leaf a | Node Tree a Tree a reflect :: (forall a. Tree a -> Tree a) -> CartCat apply :: CartCat -> Tree a -> Tree a class Reflection x where type Contr :: Constraint type Rep :: * reflect :: (forall a. Constr a => a -> a) -> x apply :: Constr a => x -> a -> a -- reflect . apply = id -- apply . reflect = id class Applicable f a b where apply :: f -> a -> b instance Applicable Int Int Int where apply = (+) instance Reflectable Int where Constr = Applicable reflect f = f 0 -- count # of applications --Catgoeyr? -- multiple applications reflect :: (forall a. (a -> a) -> a -> a) -> Int reflect f = f (+ 1) 0 reflect -- reflect of representables reflect :: Represetnable f => reflect = tabulate reflect :: Enumerable x => (x -> a) -> Table x a




Case splitting on forall contexts.




a -> a  => case to id




so of weakened function extensionality




{t :: forall a. a -> a} -> t == id




introduce the free theorems as




Laarhoven's simple reflect.




Maybe sometimes have to probe multiple times.




We're very often trying to notice polymorphism at the typeclass level.




newtype NotePolyMorphic -- DO NOT export.




-- safety of incoherence use is guranteed by the unexported NotPolymorphic unification, which will fail unless a was actuall polymorphic




{ Incoherent } (a ~ (NotPolymorphic ,b) => IsUniversal a True




IsUniversal a False
