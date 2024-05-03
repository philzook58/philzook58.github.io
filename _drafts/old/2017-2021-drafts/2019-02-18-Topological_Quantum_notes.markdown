---
author: philzook58
comments: true
date: 2019-02-18 22:41:01+00:00
layout: post
link: https://www.philipzucker.com/?p=1660
published: false
slug: Topological Quantum notes
title: Topological Quantum notes
wordpress_id: 1660
---












I'm honestly a little puzzled on how Feynman diagrams can be represented this way (the intrinsic symmetry intended between particles in a Feynman diagram confuses things for me), but they are definitely relatives.




 




The "feel" of category theory takes focus away from the objects and tries to place focus on the morphisms. There is a style of functional programming called ["point-free"](https://wiki.haskell.org/Pointfree) where you avoid ever giving variables explicit names and instead use pipe-work combinators like `(.)`, `fst`, `snd`, or `(***)`. This also has a feel of deemphasizing objects and many of the combinators that get used have categorical analogs so there is a connection there.




Representation theory, Slater and his determinant. It is difficult to understand how people were seeing things in such intellectually turbulent times.




The braiding itself doesn't necessarily look like it should include association structure







FibOp a b = FibOp { unFibOp :: forall e. FibTree e a -> Q FibTree e b }







id = FibOp pure







f . g = (unFibOp f) <=<  (unFibOp g)







par f g = FibOp (lmap (unF f) >=> rmap (unF g))







alpha = fmove







alpha' = fmove'







The Identity particle is in a sense not there. When it is combined with anything, it gives that thing back.







unit :: FibTree a b -> Q FibTree a (Id, b)







counit :: FibTree a (Id, b) -> Q FibTree a b







Interpretting Categroies. Anything that follows the category typeclass. We can generate diagrams for example. This is a ctagory of the drawings themslves or the code to generates drawings.







newtype CFibOp a b= CFibOp { forall e. FibTree e (Tuplize a) -> ... Tuplize b           }







type family Tuplize a where







Tuplize x' : [] = x'







Tuplize  x ': xs = (x , Tuplize xs)







-- this is possible but a pain.







par f g = rightAssoc ? f >=> rmapN @n? g







Take n







Drop n







type FBit = FibTree Tau (Tau, (Tau,Tau))







simpleOps = [bmove , rmap bmove,







bmove' ,   rmap bmove'] :: [FBit -> Q FBit]







allOps =  -- it's ineffiicent. Whatever.







fzero = TTT TLeaf (TTT TLeaf TLeaf)







fone = TTI TLeaf (ITT TLeaf TLeaf)







evalDistQBitOp op sx sy sz







findQBitOp sx sy sz eps =  filter (evalDist sx sy sz > eps) (apply  simpleOps      -- Brute force tree search -> use list nondeterminsm







kitaevSolovay ::







2QBits = (FBit, FBit)?







NQBits =







If they are reassociable they are in a relationship







Does DFS and reassociates accordingly. Interesting.







class Reassociable a b where







reassociate :: FibTree e a -> Q FibTree e b







class Reassociable a b leftovera leftoverb -- recurse into here. Append the leftovers. and then do the right branch.







newtype FibOp a b = FibOp ((Reassociable a a', Reassociable b' b) => FibTree







e a' ->Q  FibTree e b')







newtype FibOp a b a' b' = FibOp ((Reassociable a a', Reassociable b' b) => FibTree e a' ->Q  FibTree e b')







newtype FibOp a a' b'= FibOp ((Reassociable a a' => FibTree e a' ->Q  FibTree e b)







Maybe just ressaicate on the input, so that the internal tree shapes are specified.







Hmm. This is actually interesting for many catergories. The association is mostly just a pain. It's swapping and braiding that is interesting.







Or maybe it is a constrained category. We can compose k a b   k b' c Reassociable b b'







* * *







Mind expansion section:







Functor composition







 




The Monoid typeclass is Haskell is a typeclass that abstracts the concept of list appending. List appending is an operation associative ((x <> y) <> z) = (x <> (y <> z)) and has a identity x <>`[]`=x.




 




A category is Monoidal if it has a "product" associate with it. The monoidal product often has the connotation of some kind of parallelism or independency.




$latex (f \circ f') \otimes (g \circ g') = (f \otimes g) \circ (f' \otimes g') $




In Haskell notation:




 




 




In matrix notation.




$latex (A_1 A_2) \otimes (B_1 B_2) = (A_1 \otimes B_1) (A_2 \otimes B_2)$




As a side note, the tensor product and functor composition can be identified if you work with the Linear library. We'll talk more about that on another day.




 




Like maps and reduction operations are good primitives for homogenous parallelism, par is a good primitive for heterogenous parallelism. See Conal Elliott's functor




Examples of monoidal products:






  * Hask tupling


  * Tensor Product for Vect


  * Direct Product for Vect


  * Functor Composition


  * Functor Product


  * Anyon Product


  * Horizontal stacking of diagrams




 




Similarly for a category to be monoidal means it has an BiFunctor that is associative and has a unit. One interesting extension is to consider what if that equality doesn't hold on the nose? What if there is just a way to transform between the two sides of the previous identity. What does it mean for a a bifunctor to be associative? It means there is a natural isomorphism between the different choices of association. $latex \alpha_{A,B,C}$




In Hask, this isomorphism is given by the assoc function.




assoc is a natural transformation. This means it is a morphism indexed by objects.




assoc :: forall a b c. ((a,b),c) -> (a,(b,c))




assoc ((x,y),z) = (x,(y,z))




assoc . ((f *** g) *** h) = (f *** (g *** h))




In our FibOp category, fmove is our associator.




We can pull the coherence conditions from wikipedia and show the implementation in Haskell https://en.wikipedia.org/wiki/Monoidal_category




![Monoidal category pentagon.svg](https://upload.wikimedia.org/wikipedia/commons/thumb/8/82/Monoidal_category_pentagon.svg/700px-Monoidal_category_pentagon.svg.png)




leftbottom :: (((a,b),c),d) -> (a,(b,(c,d))))




leftbottom = assoc . assoc




topright :: (((a,b),c),d) -> (a,(b,(c,d))))




topright = (id *** assoc) . assoc . (assoc *** id)




![](https://upload.wikimedia.org/wikipedia/commons/thumb/e/e9/Monoidal_category_triangle.svg/800px-Monoidal_category_triangle.svg.png)




rightunit :: (a,()) -> a




rightunit (a, _) = a




rightunit' :: a -> (a,())




rightunit' x = (x,())




(id *** leftunit) . assoc = rightunit *** id




class Monoidal




par ::




assoc




assoc'







type Id = ()







https://hackage.haskell.org/package/data-category-0.7/docs/Data-Category-Monoidal.html




It would have been aesthetically pleasing to use `()`. for the identity particle rather than `Id` as I have previously.




I have not defined the left and right unitors yet




rightUnit :: FibTree e (a,Id) -> Q (FibTree e a)




rightUnit (TTI t _) = pure t




rightUnit (III t _) = pure t




rightUnit' t@(TTT _ _) = pure (TTI  t ILeaf)




There is some confusion that can result from the fact that `(a,b)` is the Haskell tuple type, the thing that ends up with a data representation in memory, whereas <`a`,`b`> is an abstract pair of two Haskell types. In the case of the standard Haskell monoidal product `(***)`, this bifunctor $latex \otimes$ is a functor from the abstract pair $latex <,>$ to the haskell type `(,)`.




 




As a practical aspect, if you use good categorical typeclasses that s. As any example, one can use the same program to run some some quantum computation and draw the circuit, by using different categories.  Unfortunately, through accidents of history or for the sake of simplicity, the stock Category typeclass in base is often not expressive enough to always get you what you need.




LinOp r b a = LinOp - Has the makings of a sparse format vector. Not totally insane anyway.




id = LinOp pure




(.) =




 




LinOp is a very index-y way of talking about vector spaces. There are alternatives




Diagrams package.




newtype Diagram a b = Diagram (getDiagram :: SVG)




horizontaland vertciual composition




|||




===




id = Diagram (line




newtype deriving?







 







Also since the rules are the same for different categories with the same powers, optimizations can be applied across them.The linear operators associated with the anyon vector spaces form a category. There is a natural identity and a natural notion of composition.







 




From an applied perspective, this is an excellent use of category theory. Category theory is a unified language capable of dicussing many things. See shows a methodology to take ordinary haskell functions, compile them to their descripition in terms of a ctageorical typeclass, and reinterpret them into new categroies. 




 




 




#### Functors




https://www.math3ma.com/blog/what-is-a-functor-part-1




Category theory is a science of analogy. Functors are the analogies. One precision way to define what analogy means is that Processes (morphisms) in one "thing" map to processes in another "thing". Functors are these maps between categories with good structure.




It is important to realize






  * Standard Haskell Functors. These are maps from Hask to Hask, so this is an endofunctor. It doesn't matter if you fmap (f . g) or (fmap f) . (fmap g)




  * homomorphisms. Maps between


  * Representation theory. You can associate matrices with groups such that the matrices obey the group multiplication laws. Multiplying groups. gh = \phi(g) \phi(f)


  * Free and Forgetful Functors


  * Syntax and semantics. I don't grok this one. Manipulations of the syntax mean some process in the category of their meaning




Bifunctors




http://hackage.haskell.org/package/base-4.12.0.0/docs/Data-Bifunctor.html




lmap and rmap make Fibtree e (a,b) kind of a bifunctor. Except that they carry that monadic context. Still, you see where i was coming from I hope. Maybe it is for the best to just not bring this up.




#### Natural Transformations




Natural transformations are families of morphisms indexed by objects that. They are a way of transforming one functor to another functor.




Natural transformations are morphisms in the target category indexed by objects in the source category of the functors in question.




There is a category where the objects are functors and the morphisms are natural transformations.




forall a. (Functor f, Functor g) =>f a -> g a.




In Hask, natural transformations between Functors can be expressed as polymorphic functions of the shape.




`type (~>) f g = forall x. f x -> g x`  




This function changes the structure without seeing the objects being held inside the structure.




The law a function `nat` has to obey to be natural transformations is




nat . (fmap f) = (fmap f) . nat




The type of the first (fmap f) is f a -> f b




The second is  g a -> g b




for example,




forall a. [a] -> Maybe a




nat1 [] = Nothing




nat1 x : xs = Just x




For every particular choice of type `a` there is a distinct function.




https://bartoszmilewski.com/2015/04/07/natural-transformations/




Because of this polymorphism, Natural transformations have the feel of pure structural transformations. They sometimes feel like they do very little, things that you might pass over without even mentioning.




currying




(a->b)->c ~> (a,b)->c




forall a. [a] -> Maybe a




nat2 _ = Nothing




Generalizing, natrual transfromations in categories other than (->)




forall a b. k (a,b) (b,a)




 




Category are kind of:






  * an alternative to set theory


  * A way to talk about processes


  * An algebraic theory


  * a presentation/alternative of logic and proof


  * A way to talk about functional programming




 




If you don't use the newtype Compose, then it is a strict monoidal category. However, if you do, then there are slightly non trivial associators.




The Identity functor is the unit object for this monoidal category.




There is a really interesting style in Haskell, where the vector tensor product is the same thing as functor composition.




I think it probably is possible to unify functor composition and the other categories under a single typeclass in principle. It will make the typeclass quite confusing though. The fact that the kindedness is different is also going to be a problem.




I haven't tried honestly.




 




Category as programming. Bartosz. The Category typeclass. Point-Free style. Names are considered tough and somewhat inelegant. A name is arbitary. A rose is a rose by any other name. The human mind likes them though. A leftover of address locations? Compilation allows naming and also removes the need to name things sometimes. Assembly needs names for everything. Lambda calculus.  




In the ethos of category theory, you don't want to focus on the objects. Actually you want to focus on the functors. Actually you want to focus on the natural transformations




http://pointfree.io/




Conversion to point free form is mechanical




 




I get into unpleasant conversations when I try to express my opinion that functional programming languages are more pleasant that imperative languages. If I point out some thing I consider a nice feature, a skeptic will be able to find some way to simulate that feature, or not agree that such a feature is even good. What is wrong with the for loop? That it is too general? But it let's you write extremely direct and fast code. Yes... but the generality is bad, it doesn't express your purpose. It expresses the purpose of iteration. Yes...




Set theoretical style isn't wrong. Set theory and category theory are in a similar relationship as imperative and functional programming. In both cases there are the proselytizers that are more effective than me.




I think at the outset, it isn't clear at all the benefits. It is emergent properties at scale. The "goodness" of category theory is dependent on the experimental opinion of people who have tried it, not on an obvious inherent goodness of the definitions. That's true of many axiomatic systems though. The ones that are good are the ones that after spending a lot of time proving things about the system




A language or design pattern is good only at scale. It is a subjective opinion. People who have spent a long time and gained expertise stop seeing the problems. Assembly isn't that bad if you only need to write a sum function. And you can write it blazingly fast with clever tricks. But at scale it is considered unacceptable.




In set theoretical style mathematics, your axioms define the elements. Then you turn your proof cranks and start deriving lemmas and theorems, some of which are widely considered to be the core theorem. The core theorems of some theory tend to be invoked in almost every proof you do in that theory. These core theorems often take the form of a universal property.  focus on describing objects. The category theory style has a tendency to take as the definition the most vital properties. The category theory style takes these universal properties as the definition of what you are talking about.




If you're comfortable with abstract algebra, Category is kind of like a Group with side conditions for multiplication.




 




 The world probably doesn't need another post describing categories, but I don't think I've written one. Not at this stage of my journey.




Category theory gives a language helps to make explicit and museable correspondences and operations that we consider to just be analogies or no-ops. There is power and deeper understanding in both directions. Why two things are one and why one thing is actually two. For example, Concepts that might collapse be lines in 2D can become lines and planes in 3D. Or one might realize that .




A place in physics where this is rampant is calling anything and everything a Green's function. I think this is more confusing than helpful.




Representation theory, Slater and his determinant. It is difficult to understand how people were seeing things in such intellectually turbulent times.




Category as Foundations and logic. What is math? Formalization. Logic from Aristotle to Frege. Set Theory. My philosophical opinion is that even these things aren't perfect and god given. There is no capitoal letter Foundation. There are choices of foundations. And the final jump between human undertsanding, mind and informal language to the axioms / mechanics (it's even pre-axiom that we're talking here. Substitution mechanisms). Every time you formalize some aspect of it, there seems to me an infinite regression of how do we understand that formalization. The act of nailing it down seems impossible by construction. There is a lot I don't understand here and a lot of work by passionate people.




Like Set theory, category theory brings it's own mindset. Constantly comparing against your known library of categorical patterns. Searching for compositional properties everywhere. Trying to make objects opaque blobs.




Category as an abstraction of functions. Functions without worrying about the details of what exactly the things they are functions from or to. We sometimes want a theory of something to throw out the unnecessary details.




Categories as Graphs. Cayley Diagrams. A graph can be described as a group if every node have the same actions available to it.




Categories make proofs fall apart like cooked turkey.




 




Duality




Duality is a bog. A beautiful bog. It's like a siren that makes your eyes turn white and dream your being fed grapes while bog water chokes the life out of you.




It's such goddamn numerology. But it is kind of likely to work, because 2 is such a good number. 137 isn't.




https://en.wikipedia.org/wiki/Duality




https://en.wikipedia.org/wiki/List_of_dualities#Mathematics




Duality is so simple. For every duality you find, you add a factor of two to the ways of thinking of things. This leads to a cobinatorial explosion of abstraction that will destroy you.




Dualities I know categories for:




Vector and Linear functionals




Dualities I don't:




Points and planes - prohective




Hodge




Poincare




Electromagnetic, Particle Vortex, Particle Wave, Circuit duality, Kramers-Wannier




And clearly they are all related in various ways./ Very frustrating and tantalizing




Vectors. Functors. (I'm gonna write a longer form article about this someday)




 




* * *




Parallel differentiable functions




Kronecker Product of vectors -- unit = 1-d vector space.




Direct Sum - unit = 0-d vector space.




type DSum = Product -- hmm I could do the same here as for Kron




-- QuadOp = \(V,V -> Double) -> (V,V -> Double) -> Double




-- forall r. (V, V -> r) -> r --Kind of a flipped lens.




-- (V, V -> V') -> V' -- quadop




Functor Composition - Unit = Identity




type Kron = Compose




(Kron (Kron V2 V2) V2) Complex Double  -- a 3 qubit vector space




swap = Compose . sequenceA . runCompose




assoc :: Compose (Compose f g) h -> Compose f (Compose g h)




assoc (Compose (Compose f)) = Compose (Compose f)




cnot (Compose (V2 (V2 x y) s@(V2 a b) )) = V2 (V2 y x) s




sigz =




sigy =




sigx =




It's laborious, not crazy efficient, but still kind of aesthetically pleasing. One oculd wotk at automating reassociation just like we've done here.




An index free style. vector spaces should be written as polynomials in base vector spaces, not by their integer size.




 




 



    
    class ReAssoc a b
       reassoc :: a -> b
    
    Reassoc' a b () => ReAssoc a b
       reassoc x = fst (reassoc x)
    
    class ReAssoc a b c | a b -> c where -- a ~> (b,c)
            reassoc :: a -> (b,c) -- leftovers
    
    class LeftMatch a b c | a b -> c where -- make the leftmost porton of a match b, turning it into c
        leftmatch :: a -> c
    
    The leftovers might make sense. I just don't need to give it's value. just compute the type
    
    Leftmatch Tau Tau Tau
    LeftMatch (Tau,a) Tau (Tau,a)
    -- This let's us destroy the index b down to base case
    LeftMatch a l (l,r'), LeftMatch r' r r''   => LeftMatch a (l,r) (l,r'')  -- I don't know where to place the match on r. Wait. Yes I do. Because once I've matched, now i can just rmap 
      leftmatch x = x' = leftmatch @l x in rmap leftmatch @r x'
     
    -- could i do a leftmatch and right match kind of in parallel? M<aybe
    
    -- LeftMatch (l,r) Tau c, LeftMatch (c,a) Tau c' => LeftMatch ((l,r),a) Tau c' -- I can gurantee something is wrong
    -- no the recursive clal makes not sense. I don't need to match in a, because tau won't be there
         (lmap leftmatch) >=> leftmatch
    LeftMatch (l,r) Tau c => LeftMatch ((l,r),a) Tau (c,a) -- This is basically pullleft?
    
    PullLeft a c
    c ~ (Tau, c')  => LeftMatch a Tau c
    
    
    -- it's basically pretty simple then
    -- Once we've built the basic 
    -- the base case uses PullLeft
    -- The recrusive case uses leftmatch on the left subpattern, the rmaps in leftmatch on the right leftovers.
    
    LeftMatch a l (l,r'), LeftMatch r' r r''   => LeftMatch a (l,r) (l,r'')  -- I don't know where to place the match on r. Wait. Yes I do. Because once I've matched, now i can just rmap 
      leftmatch x = do
                     x' <- leftmatch @l x
                     rmap leftmatch @r x'
    
    
    then
    
    data FibOp a b where
       ReAssoc a a' => (FibTree c a') -> Q (FibTree c b) -> FibOp a b
    
    This doesn't quite work we still need a custom compose?
    compose :: ReAssoc b b' => FibOp b' c -> FibOp a b -> FibOp a c
    
    Uh, maybe not. FibOp's a stays pretty polymorphic. So the application of compose will typically unify b with the output, and 
    It might work. I'm not sure.
    
    
    
    
    
     LeftMatch (l,r) (Tau,a)  => LeftMatch ((l,r),a) (Tau,a) (Tau,c)
    LeftMatch ((a,b),c) (() -- Maybe we do need the leftover) 
    
    class ReAssoc a b where
       reassoc :: a -> b
    reassoc :: LeftMatch a b b => a -> b
    reassoc = leftmatch   
    instance ReAssoc a (l,r) 
       reassoc x = x' = leftmatch x @l
                        rmap (reassoc @r x')
    
    
      ReAssoc a l c' , ReAssoc c' r c''   =>  ReAssoc a (l,r) c''
              reassoc a = let (l,c') = reassoc a in
                          let (r,c'') = reassoc c' in
                          ((l,r), c'')
     -- lmap reassoc
    
    
    ReAssoc a () a where
        reassoc x = (x,())
    ReAssoc (Tau, a') Tau a'
       reassoc = id
    ReAssoc (Id, a') Id a'
       reassoc = id
    
    ReAssoc a a () -- probably overlapping, but it is fine.
       reassoc = id
    
    -- One way might be to RightPull/canonicalize. Tnen write an instance that turns a canoncalized instance
    
    
    
    ReAssoc l Tau c => ReAssoc (l,r) Tau (c,r)
       reassoc (l,r) = (_, c) = reassoc l
                       (Tau,  )
    
    
    
    ReAssoc a Void a
    




 




* * *




 




For small, sparse manipulations this can be quite wasteful. Converting an arbitrary  anyon tree into the standard basis will be dense. Now, having said that, an actual quantum computation probably WILL be dense (a big tangled mess) since you're trying to exploit that dense matrix vector product to achieve




One interesting thing about constructing the tree type this way is that we get we get sort of a bounded polymorphism. Although we make operators that use polymorphic anyon types, the only possible things that can go in those slots are actually constructible anyon trees. We also get access to the type in there by pattern matching on the constructor.




One way to make this seem not so weird may be to think of the example of a probability vector. Each coefficient would be the probability that Jerry chooses some particular emoji for example. There are less kooky examples of constructions like this from mathematics, such as forming formal sums over simplices in a triangulated structure.




The Free vector style feels significantly more symbolic/algebraic than the array based approach. Because we are still using floats, there is a numeric aspect.




The basic operations we want to be able to use on the trees are braiding moves and association moves. Braiding physically corresponds to taking to particles and braiding them around each other. Clockwise and counterclockwise braiding is distinct. The worldlines of the particles get tangled on each other.




We're tackling two things here. A lot of what we're doing is similar to deal with Vec n a compared to just working with List. The types constrain you from forming ill formed vector expressions where dimensions don't match, at the cost of a significant amount of type machinery burden. Well typed vector spaces are a hog tackle unto themselves. We could have written our anyon vectors with far less type safety or in python is essentially the same way. But I think the categorical puns are quite nice, and the types saved me from writing nonsense multiple times.




Under and over braidings are not equivalent.




 




For small, sparse manipulations this can be quite wasteful.  Now, having said that, an actual quantum computation probably WILL be dense (i.e. a big tangled mess of braiding) since you're trying to exploit that dense matrix vector product to achieve quantum speedup.




An interesting question is optimal evaluation. Under some cost scheme, can one derive an optimal evaluation? Going from the bottom of the diagrams up is arbitrary. You can evaluate from left to right, right to left. You can simplify little clusters. It is possible to take a trivial loop and then tangle it up with braiding moves. You can classically search for those moves. Knot untangling as far as we know is a difficult question. https://arxiv.org/abs/math/9807016 https://en.wikipedia.org/wiki/Unknotting_problem




One thing that topological quantum circuits have over the typical ones is the a tiny small hope that there may exist significant algebraic optimizations you can perform classically. An arbitrary gate set does not obey all that many algebraic rules.




In the categorical language, this optimization problem does not appear all that much different from  program optimization.




Pretty Print trees.



    
    {-# LANGUAGE DataKinds #-}
    
    data IsingAnyon = Id | Tau
    
    data SIsingAnyon where
       SId :: SIsingAnyons 'Id
       STau :: SIsingAnyons 'Tau
    
    class Splitable a b c where
       braidnum :: Complex Double
    
    
    data AnyonVec leaves where
       Node :: IsingAnyon -> AnyonVec a -> AnyonVec b -> AnyonVec (a,b) -- we would like to enforce that isingany can split into a b, but this is tough
       Leaf :: AnyonVec c
    
    -- braid left and braid right
    
    braid :: Splittable a b c => Anyon c (a,b) -> Vec (COmplex DOuble) (Anyon c (b,a))
      braid TTI x y = TIT y x
      braid TIT x y = TIT y x
      braid ITT x y = ITT y x
      braid TTT x y = TTT y x
      -- braid (Node part) impossible
    
    braid :: Anyon c (a,b) -> Vec (Complex DOuble) (Anyon c (b,a)) -- no need for splittable. Just put the data right in here? Wait we want to only braid leaves
      braid TTI x y = TIT y x
      braid TIT x y = TIT y x
      braid ITT x y = ITT y x
      braid TTT x y = TTT y x
    
    -- SIsing force b and a to be pure particles and not composite tree.
    braid :: SIsing a -> SIsing b -> Anyon c (a,b) -> Anyon c (b,a)
    braid _ _ x =  
    braid :: (SIsing a, SIsing b) => Anyon c (a,b) -> Anyon c (b,a)  -- make it implicit
    
    
    -- higher order braid should allow you to braid entire subbranches... maybe you can?
    
    
    -- maybe putting explcit kind notation would work (b :: IsingAnyon). (a,b) is not an IsingAnyon
    
    class IsingBraid where
      braid
    
    instance IsingBraid Anyon 'Tau ('Tau,'Tau) where
    
     
    -- a nightmarish number of combos. 5*5? Maybe this is it?
    -- the interior line is the middle letter
    f-move :: Anyon r (a,(b,c)) -> Vec (Anyon r ((a,b),c))
    f-move (ITT  a  (TTI b c)) = 
    f-move (ITT  a  (TIT b c)) = 
    f-move (ITT  a  (TTT b c)) = 
    
    f-move (TTT  a  (TTI b c)) = 
    f-move (TTT  a  (TIT b c)) = 
    f-move (TTT  a  (TTT b c)) = 
    
    f-move (TIT  a  (TTI b c)) = 
    f-move (TIT  a  (TIT b c)) = 
    f-move (TIT  a  (TTT b c)) = 
    
    
    
    data AnyonVec root leaves where -- This is more generic. But we can't force Splitting rules? Is that a problem?
       Node :: SIsingAnyon c -> AnyonVec a l -> AnyonVec b l' -> AnyonVec c (l,l') -- we would like to enforce that isingany can split into a b, but thisis tough
       Leaf :: SIsingAnyon c -> AnyonVec c c
    
    data AnyonVec root leaves where -- IsingTree, Aren't the 
       ITT :: SIsingAnyon 'Id -> AnyonVec 'Tau l -> AnyonVec 'Tau l' -> AnyonVec 'Id (l,l') -- we would like to enforce that isingany can split into a b, but thisis tough
       TTI :: SIsingAnyon 'Tau -> AnyonVec 'Tau l -> AnyonVec 'Id l' -> AnyonVec 'Id (l,l')
       TIT :: SIsingAnyon 'Tau -> AnyonVec 'Id l -> AnyonVec 'Tau l' -> AnyonVec 'Tau (l,l')
       TTT :: SIsingAnyon 'Tau -> AnyonVec 'Tau l -> AnyonVec 'Tau l' -> AnyonVec 'Tau (l,l')
       Leaf :: SIsingAnyon c -> AnyonVec c c
    
    -- step one, build data strucutre inhabited only by valid trees
    -- why do we even need the type parameters? To match up with other notions.
    data IsingTree root leaves where
       ITT :: AnyonVec 'Tau l -> AnyonVec 'Tau l' -> AnyonVec 'Id (l,l') -- we would like to enforce that isingany can split into a b, but thisis tough
       TTI :: AnyonVec 'Tau l -> AnyonVec 'Id l' -> AnyonVec 'Id (l,l')
       TIT :: AnyonVec 'Id l -> AnyonVec 'Tau l' -> AnyonVec 'Tau (l,l')
       TTT :: AnyonVec 'Tau l -> AnyonVec 'Tau l' -> AnyonVec 'Tau (l,l')
       -- III :: AnyonVec 'Id l -> AnyonVec 'Id l' -> AnyonVec 'Id (l,l') -- maybe shouldn't exist. uneccessary. Does really help for monoidal instance
       TLeaf :: AnyonVec 'Tau 'Tau
       -- ILeaf :: AnyonVec 'Id 'Id -- maybe shouldn't exist
    -- could add a particle count parameter.
    
    type Vec a b = [(a,b)]
    type Q = Vec (Complex Double)
    
    smul s = map (\(a,b) -> (a*s, b))
    vadd = (++)
    
    type QAnyon = Q IsingTree
    
    {-
    instance (Num (Q b) => 
       (+) = (++)
    -} 
    
    type Dual a b = b -> a -- aka Reader
    type QDual = Dual (Complex Double) 
    type DAnyon = QDual QAnyon
    
    type Expansion r a b= [(Dual r (Vec r a), Vec r b)] -- a sum  |b><a| expansion of an operator
    
    eapply :: Expansion r a b -> Vec r a -> Vec r b 
    eapply e v = concatmap (\(d, v') -> smul (d v) v') e
    
    
    eid :: Enum c => Expansion r (Anyon c (a,b)) (Anyon c (a,b))
    eid = enum
    
    eid :: Enum a, Num r => Expansion r a a
    eid = map (\e -> (\v -> map fst $ filter (\(c, e') -> e == e') v,  pure e )  ) enum
    
    -- traversing down the tree, kind of the kron product of indenpedent maps
    bimap :: (Anyon c' a -> Vec Anyon c' a') -> (Anyon c'' b -> Vec Anyon c'' b') -> Anyon c (a,b) -> Vec (Anyon c (a',b'))
    lmap f = bimap f pure
    rmap f = bimap pure f
    
    
    -- rmap . rmap . rmap braid -- would braid the rightmost pair
    -- lmap . rmap f-move -- perform f-move down somewhere
    
    
    
    instance Enum (Anyon 'Tau a), Enum (Anyon 'Id a) => Enum (AnyonVec 'Tau (a,b))
    -- list all the ways to get Tau at the root.
    
    
    -- the basic build block of a dual vector
    -- we hsould lock away the implementation of IsingTree and only export fuse, braid, f-move, split
    -- I don't want you to reach under the vector and fiddle
    
    -- bubbles collapse
    fuse :: (SIsing, SIsing b) => Anyon c (a,b) -> Anyon c c
    fuse (TTT _ _) = TLeaf
    fuse (TIT _ _) = TLeaf
    fuse (TTI _ _) = TLeaf
    fuse (ITT _ _) = ILeaf
    
    
    -- basically just equality
    dot :: (Anyon c a) -> (Anyon c a) -> (Anyon c c)  
    
    -- dot is the obvious way to construct Duals.
    dot' :: (Anyon c a) -> (Anyon c a) -> Complex DOuble  -- -> Q (Anyon c c) -- Maybe?
    dot' x y | x == y = 1
             | otherwise = 0
    
    
    
    
    
    -- then it is our job to rearrange things so that join works using f-moves and r-moves
    -- Automating this is a job for type level programming :(
    -- dualexample =      
    
    
    
    AnyonOp = [(Dual Vec,  )]
    
    instance Category (Anyon) -- has to handle (,,,) -> (,,,,)
    -- anyonvec as is always has unique root.
    
    Category ((Anyon c _) -> Anyon c _) where
       (.) = (.)
       id = id
    
    Category Anyon c -> Vec Anyon c -- linear maps.
    
    instance Monoidal (Anyon Id _ -> Anyon 'Id _ ) -- is it gonna get pissy about this? Probably.
      type Unit = 'Id
      III -> III
      lunit TIT _ x -> x
      lunit TT _ x -> x 
    
    instance Braided (Anyon a _ -> Anyon a _)
    
    -- Then lift this instance to the vector version?
    -- Well, really the vector version comes first
    
    
    
    Category 
    
    -- by this definition braid and f-move are part of the category
    -- and mkae the category braided monoidal
    
    
    Do Shor.
    
    
    




 
