---
author: philzook58
comments: true
date: 2019-05-10 17:52:08+00:00
layout: post
link: https://www.philipzucker.com/?p=2018
published: false
slug: Type Algebra II
title: Type Algebra II
wordpress_id: 2018
---




I did not appreciate how much has already been done here. That is for the best.







[www.cs.ox.ac.uk/people/daniel.james/iso/iso.pdf](https://www.google.com/url?sa=t&rct=j&q=&esrc=s&source=web&cd=1&ved=2ahUKEwi99ZCl347iAhURT98KHXdWDPMQFjAAegQIAhAC&url=http%3A%2F%2Fwww.cs.ox.ac.uk%2Fpeople%2Fdaniel.james%2Fiso%2Fiso.pdf&usg=AOvVaw0jfC0LqhLdhEbQmsMnImwa)







There is a chapter in plfa. They go on to talk about embeddings, which I guess are prisms...?







[https://plfa.github.io/Isomorphism/](https://plfa.github.io/Isomorphism/)







[https://kseo.github.io/posts/2016-12-25-type-isomorphism.html](https://kseo.github.io/posts/2016-12-25-type-isomorphism.html)







Ok. I don't feel that most of these are hitting quite the same points I did. Jacque Carette's got closest.







Hmm. Emily Pillmore and Alexander Konovalov are giving a talk at lamdbaconf on "Isomorphic Reasoning". I also feel like they are going to a more high powered approach. Category theory and rankntypes. Worrying about forall a. a -> a and such.







Should put the big identities into Iso axioms







Can I derive Free Theorem Isos using reified Forall maybe? + quantified constraints?







Could also actually hide the constructor to Iso. Get a more legit proof system







FreeThereomIso (a -> b), FreeTheoremIso Forall







swithc to to from for to avoid impredicative problems













[https://www.twanvl.nl/blog/haskell/isomorphism-lenses](https://www.twanvl.nl/blog/haskell/isomorphism-lenses)







Huh van Laarhoven also has a post talking about the exists tuple













Reflection into GHC.Typelits. Some calculations are easier to verify than derive. For example, division. We can easily reflect into and out of the GHC typelits system if it is convenient. I do not see how to reflect proofs into and out of the system though.







Same thing for SNat and Eq. I see no direct way to reflect proofs, although we can reflect answers. Eq style proofs are largely driven by implicit unification (the theory of uninterpeted functions). Perhaps we could reify unification into Dict. Perhaps if we used leibnitz equality style, which has explicit unification... Leibnitz equalit forall f. f a -> f b, is rather similar to the Lens/Iso type signature. We could perhaps build a typeclass that abstracts over both. Although Lens requires a Functor instance... hmm







(a ~~ b) ->   







    
    <code>data MyGadt a where
      MyInt :: (a ~~ Int) -> MyGadt a
      MyBool :: (a ~~ Bool) -> MyGadt a
    type a ~~~ b = forall f. f a -> f b
    data MyGadt a where
      MyInt :: (a ~~~ Int) -> MyGadt a
      MyBool :: (a ~~~ Bool) -> MyGadt a
    data MyGadt a where
      MyInt :: MyGadt Int
      MyInt :: MyGadt Bool
    
    -- is this right? is there a functor form of Iso or does it require more? You're going to need to newtype wraper specialized functor instances.
    mycase1 :: forall f. Functor f => MyGadt1 a -> f Int -> f Bool -> f a 
    comatch :: Contrvaraint f =>
    promatch :: Profunctor (Invaraint?)
    mycase2 :: forall f. MyGadt2 a -> f Int -> f Bool -> f a
    mycase2 (MyInt f) x y = f x
    mycase3 (MyBool f) x y = f y 
    mycase3 :: forall f. MyGadt3 a -> f Int -> f Bool -> f a</code>







We can reflect certificates, which are something close to reified proofs. 







Negative numbers and Fractions







Exists and Forall. Category theory perspective. From an algebraic persepctive, exists b. is a sum type over all b, and forall a. is a product type over all a.







By some fishy reaosning:







exists b. (Finite b) => (b -> a) = \sum_b a^b ~ List a 







exists b. b ~ 1 + 2 + 3 + 4 + 5 ... 







forall a. (a -> a) = \prod_a a^a = doesn't make much sense that this is uniquely inhabvited.







forall r. (a -> r) -> r ~ \prod_r r^(r^a) - this makes no sense.













kan extensions librayr has Yoneda and Coyoneda types







Also it has Kan extensions for that matter.



