---
author: philzook58
comments: true
date: 2019-07-02 16:23:17+00:00
layout: post
link: https://www.philipzucker.com/a-short-skinny-on-relations-towards-the-algebra-of-programming/
slug: a-short-skinny-on-relations-towards-the-algebra-of-programming
title: A Short Skinny on Relations & the Algebra of Programming
wordpress_id: 2030
categories:
- Haskell
tags:
- algebra
- categorytheory
- formal methods
- haskell
---




I've been reading about the Algebra of Programming lately and _lovin' it_. See [J.N. Oliveira's draft text](http://www4.di.uminho.pt/~jno/ps/pdbc.pdf) in particular and the links in the references. I've started exploring the stuff from this post and more over here: [https://github.com/philzook58/rel](https://github.com/philzook58/rel)







## Why and What?







Relations can expand the power of functional programming for the purpose of specification.







The point of a specification is to be able to write down in a very compact and clear way your intent for a program, more clearly and compactly than a full implementation could be written. It therefore makes sense to add to your specification language constructs that are not necessarily executable or efficient for the sake of compactness and clarity.  When one needs executability or efficiency, one writes an implementation whose behavior you can connect to the spec via a formal or informal process.







Functional programming, with it's focus on the abstraction of the mathematical function, is a good trade-off between executability, efficiency, and expressibility. It lies in a reasonable location between the ideas amenable to reasoning by a human mind and the command-driven requirements of the machines.







Functions are a specialization of relations. Relations extend the mathematical notion of functions with constructs like nondeterministic choice, failure and converse. These constructs are not always obviously executable or efficient. However, they greatly extend the abilities of reasoning and the clarity of expression of a specification.







The point-free style of reasoning about functions extends to a point-free style reasoning about relations, which is known as [relation algebra](https://en.wikipedia.org/wiki/Relation_algebra). There are rich analogies with databases, category theory, linear algebra, and other topics. 







Plus, I think it is very neato for some reason. If anyone ever thinks something is really neato, isn't it worth giving it a listen?







### A Simple Representation of Relations in Haskell







The simplest description of relations is as a set of tuples. So first let's talk a bit about the options for sets in Haskell.







#### Sets in Haskell







There are a couple different reasonable ways to represent sets in Haskell. 







  * `[a]` or `Vector a`
  * a -> Bool
  * `Set a` -- a tree based Set from the [containers](http://hackage.haskell.org/package/containers-0.6.2.1/docs/Data-Set.html) package.






These have different performance characteristics and different power. The list `[a]` is very simple and has specialized pleasant syntax available. The indicator function `a -`> `Bool` gives you no ability to produce values of type `a`, but can easily denote very sophisticated spaces. `Set a` is a good general purpose data structure with fast lookup. You might also choose to mix and match combinations of these. Interconversion is often possible, but expensive. This is not a complete list of possibilities for sets, for example you may want a representation with a [stronger possibility for search](http://eptcs.web.cse.unsw.edu.au/paper.cgi?MSFP2014.3).







#### Relations in Haskell







We can directly use the definition of relations as a set of tuples with the above






    
    <code>type Rel a b = [(a,b)]
    type SetRel a b = Set (a,b)
    type FunRel a b = (a,b) -> Bool</code>







But we also have the option to "curry"  our relation representations, sort of mixing and matching properties of these representations.






    
    <code>type List a b = a -> [b] -- Commonly seen type  in List monad/logic programming
    type MapRel a b = Map a (Set b)</code>







You might also choose to package up multiples of these representations, choosing the most appropriate as the situation requires, see for example the [relation](http://hackage.haskell.org/package/relation-0.2.1/docs/Data-Relation.html) package, whose type holds both `Map a (Set b)` and `Map b (Set a)`.







Despite fiendishly poor performance, for simplicity and list comprehension syntax we are going to be using `type Rel a b = [(a,b)]` for the remainder of the post.







I'm also taking the restriction that we're working in bounded enumerable spaces for ease. I assume such a requirement can be lifted for many purposes, but finite spaces like these are especially well tamed. The following typeclass and definition is very useful in this case.






    
    <code>type BEnum = (Enum a, Bounded a) 
    enumAll :: (BEnum a) => [a]
    enumAll = [minBound .. maxBound]</code>







#### Functions and Relations







Functions can be thought of as relations with the special property that for each left part of the tuple, there is exactly one right side and every possible left side appears. The relation corresponding to a function $latex f$ looks like $latex F = \{(x,y) | x \in X, y \in Y, y = f (x)\}$.






    
    <code>tabulate :: (BEnum a) => (a -> b) -> Rel a b
    tabulate f = [(x, f x) | x <- enumAll]</code>







There is a natural and slightly clever lifting of function composition to relations. We now check whether there exists a value that is in the right side of one and the left side of the other. 






    
    <code>rcompose :: Eq b => Rel b c -> Rel a b -> Rel a c
    rcompose xs ys = [ (a,c)  | (a, b) <- ys, (b', c) <- xs, b' == b]
    
    rid :: (Enum a, Bounded a) => Rel a a
    rid = tabulate id</code>







Because of these two operations (and their properties of associativity and absorption), [FinRel is a category](https://ncatlab.org/nlab/show/Rel). We do however need the `Eq b` restriction to make `Rel` an instance of the category typeclass, so it does not quite fit the definition of [category in base](http://hackage.haskell.org/package/base-4.12.0.0/docs/Control-Category.html). It is a [constrained category](http://hackage.haskell.org/package/constrained-categories).







We can lift the common arrow/categorical combinators up to relations for example.






    
    <code>-- arrow/category combinators
    rfan :: Eq a => Rel a b -> Rel a c -> Rel a (b,c) 
    rfan f g = [ (a, (b,c)) | (a,b) <- f, (a',c) <- g, a == a']
    
    rfst :: BEnum (a,b) => Rel (a,b) a 
    rfst = tabulate fst 
    
    rsnd :: BEnum (a,b) => Rel (a,b) b 
    rsnd = tabulate snd
    
    rleft :: (Enum a, Bounded a) => Rel a (Either a b) 
    rleft = tabulate Left
    
    rright :: BEnum b => Rel b (Either a b) 
    rright = tabulate Right
    
    reither :: Eq a => Rel a c -> Rel b c -> Rel (Either a b) c 
    reither f g = [(Left a, c) | (a,c) <- f] ++ [(Right b, c) | (b,c) <- g] 
    </code>







With these combinators, you have access to many functions on basic non-recursive algebraic data types. By combining them in a point free style, you can build some other useful combinators.






    
    <code>--- goofy inefficient definitions
    dup :: (Eq a, Eq b, BEnum a, BEnum b) => Rel a (a,a)
    dup = rfan rid rid
    swap ::(Eq a, Eq b, BEnum (a,b)) => Rel (a,b) (b,a)
    swap = rfan rsnd rfst
    par :: (Eq a, Eq c, BEnum a, BEnum c) => Rel a b -> Rel c d -> Rel (a,c) (b,d) 
    par f g =  rfan (rcompose f rfst) (rcompose g rsnd)</code>







#### An Aside: Relations, Linear Algebra, Databases







The composition operation described above is not so unfamiliar as it may first appear. 







Relation algebra has a [great similarity to linear algebra](https://arxiv.org/pdf/1809.00641.pdf). This connection can be made more clear by considering sparsity patterns of matrices and tensors. Sparsity patterns are a useful abstraction of linear algebraic operations. Instead of considering matrices of numbers, instead the entries are "zero" and "possibly nonzero" or, if you prefer, a matrix of boolean values corresponding to those same questions.







The ordinary row times column matrix multiplication corresponds to relation composition. Replace * with AND  and + with OR. If any of the numbers is zero, then multiplying them will result in zero. In summing two numbers, if either is possibly nonzero, then the result is possibly nonzero. 







Another interesting way of looking at it is that we are replacing the summation binding form $latex \sum_i$ with the logical  quantifier $latex \exists_i$. Both introduce a scoped "dummy variable"  i and have a lot of syntactic similarity. Other related forms include $latex \lambda i$, $latex \forall i$, $latex \int di$,  $latex \max_i$ .







There is also an analog of the point free relation algebra in linear algebra. Linear algebra has the most widely used point free notation in the world, matrix notation. Consider the expressions $latex Ax=b$ and $latex X = ABC$ as compared to $latex \sum_j A_{ij} x_j = b_i$ and $latex X_{il} = \sum_{jk} A_{ij} B_{jk} C_{kl} $. Matrix notation is SO much better for certain calculations. Other pieces of the matrix notation include transpose, inverse, Kronecker product, the Khatri-Rao product, and Hadamard product. Their properties are more clear in the index free form in my opinion. I believe even massive tensor expressions can be written index free using these operators. There are also analogies to be drawn between the [graphical notations in these different fields](http://math.ucr.edu/home/baez/rosetta.pdf).







Databases can be thought of very similarly to sparse matrices. In principle, you could enumerate all the possible values for a column of a database. So you could think of a database as a giant matrix with a 1 if the item is in the database and 0 if not. Databases are very very sparse from this perspective, and you would never store them this way. The join operation is a relative of relational composition, however join usually operates via looking at the column names, whereas our join is position based.







[Query optimization](https://en.wikipedia.org/wiki/Query_optimization) in databases has interesting analogs in sparse linear algebra.  For example, the Taco compiler [http://tensor-compiler.org/](http://tensor-compiler.org/) is doing something very akin to a query optimizer.







#### Inverting Relations







Unlike functions, Relations are always "invertible".  We call this the converse of a relation. When a function is invertible, it corresponds to the converse. In terms of the tuples underlying our representation, it just swaps them. Relations also possess operations `trans` and `untrans` that may be thought of as a kind of currying or as a partial inverse on a single parameter.






    
    <code>converse :: Rel a b -> Rel b a
    converse = [(b,a) | (a,b) <- r]
    
    untrans :: Rel a (b,c) -> Rel (a,b) c
    untrans r = [((a,b),c)  | (a, (b,c)) <- r]
    
    trans :: Rel (a,b) c -> Rel a (b, c)
    trans r = [(a, (b,c))| ((a,b),c)  <- r]</code>







Orderings can also be lifted to relations $latex (\leq) = \{(a,b) | a \leq b\}$. The composition of relations also respects the usual composition of ordering.






    
    <code>reflectOrd :: (Ord a, BEnum a) => Rel a a
    reflectOrd = [(x,y) | x <- enumAll, y <- enumAll, x <= y]</code>







Nondeterministic choice is sometimes represented in Haskell using Set returning functions `a -`> `[b]`. You may recall this from the context of the List monad. In fact in this case, we have an isomorphism as evidenced by `tabulateSearch` and `searchRel`. 






    
    <code>tabulateSearch :: BEnum a => (a -> [b]) -> Rel a b
    tabulateSearch f = [(a,b) | a <- enumAll, b <- f a]
    
    searchRel :: Eq a => Rel a b -> (a -> [b])
    searchRel r a = [b | (a', b) <- r, a == a']</code>







Similarly partial functions can be reflected into relations






    
    <code>tabulatePartial :: BEnum a => (a -> Maybe b) -> Rel a b
    tabulatePartial f = [(a,b) | a <- enumAll, b <- toList (f a)]</code>







A useful trick is to lift sets/subsets to relations as a diagonal relation. $latex \{(a,a) | a \in S \}$. Projection onto the set can be achieve by composing with this relation. The identity results if you are talking about the entire set S. 






    
    <code>diagRel :: [a] -> Rel a a
    diagRel = map dup where dup x = (x,x)
    
    leftSet :: Eq a => Rel a b -> [a]
    leftSet = nub . (map fst)
    
    rightSet :: Eq b => Rel a b -> [b]
    rightSet = nub . (map snd)</code>







#### Comparing Relations







We can compare sets by asking if one is a subset of the other $latex A\subseteq B$ . Relations can also be compared by this operation, which we call relational inclusion.






    
    <code>rSub :: (Eq a, Eq b) => Rel a b -> Rel a b -> Bool
    rSub xs ys = and [x `elem` ys | x <- xs]
    
    x <~ y = rSub x y</code>







A subservient notion to this is relational equality.






    
    <code>
    rEq :: (Eq a, Eq b) => Rel a b -> Rel a b -> Bool
    rEq xs ys = (xs `rSub` ys) && (ys `rSub` xs)
    
    x ~~ y = rEq x y</code>







Relational algebra is chockful of inequality style reasoning, which is richer and slightly more complicated than equality style reasoning. This is one of the benefits of moving from functional descriptions to a relational description.







Relations also form a [lattice](https://en.wikipedia.org/wiki/Lattice_(order)) with respect to these comparisons. What the hell are lattices? In the context of finite relations, lattices may be over powered mathematical machinery, but it really is useful down the line.  They give you binary operators that play nice with some kind of ordering, in our case relational inclusion. These two operations are the meet and the join, which find the greatest lower bound and least upper bound  of the operands respectively. For our relations, these correspond to the more familiar notion of set intersection and union. The intersection of two sets is the biggest set that is in both of them. The union is the smallest set for which both sets are a subset of it. 






    
    <code>meet' :: (Eq a, Eq b) => Rel a b -> Rel a b -> Rel a b
    meet' xs ys = [x | x <- xs, x `elem` ys] -- intersection
    
    join' :: (Eq a, Eq b) => Rel a b -> Rel a b -> Rel a b
    join' p q = nub (p ++ q) -- union
    
    
    instance (Eq a, Eq b) => Lattice (Rel a b) where
        x /\ y = meet' x y
        x \/ y = join' x y
    </code>







Using meet/join vs intersection/union becomes more interesting when the domain is fancier than relations over finite domains. Issues of infinity can make this interesting, or when using a representation that can't explicitly represent arbitrary unions or intersections, but that instead has to approximate them. My favorite example is polyhedra. Polyhedra are not closed under unions. So in this case the join and union do not coincide. You need to take a convex hull of the union instead, which is the best approximation.  Concretely, polyhedra can be represented as a list of their vertices, which generate the polyhedron. There is no way to express a union in this representation. Concatenating the lists represents taking the convex hull of the union.







An additional property that a lattice may possess is a largest and small element, called top ($latex \top$ ) and bottom ($latex \bot$). Our finite domain relations do have these.






    
    <code>instance (Eq a, Eq b, BEnum a, BEnum b) => BoundedMeetSemiLattice (Rel a b) where
        top :: (BEnum a, BEnum b) => Rel a b 
        top = [(x,y) | x <- enumAll, y <- enumAll]
    -- all possible tuples
    
    -- because of superclass constraints :(
    instance (Eq a, Eq b) => BoundedJoinSemiLattice (Rel a b) where
        bottom :: Rel a b -- no tuples
        bottom = [] </code>







#### Relational Division







And now finally we get to one of the most interesting, powerful, and confusing operations: relational division. Relational division is a kind of pseudo inverse to relational composition. In linear algebra, the pseudo inverse is a matrix that does the best job it can to invert another matrix in a least squares sense. If the matrix is actually invertible, it equals the inverse. Relational division does the best job it can to invert a relational composition. Instead of taking least squares as a criteria, it ensures that the result doesn't over approximate. If you had the inequality $latex X \cdot Y \subseteq Z$ and you want to  solve for X, relational division is the thing that does that. The right division $latex Q = Z/Y$ is the largest relation such that $latex Q \cdot Y \subseteq Z$.  







A helpful example is the similar [operation of division in database tables](https://en.wikipedia.org/wiki/Relational_algebra#Division ). 







And here is an implementation that I think is correct. I've goofed it up a couple times, it is a rather confusing construct.






    
    <code>rdiv :: (BEnum a, BEnum b, Eq a, Eq b, Eq c) => Rel a c -> Rel b c -> Rel a b
    rdiv x y = [ (a,b)  | a <- enumAll, b <- enumAll, all (\c -> ((b,c) `elem` y)`implies` ((a,c) `elem` x)) (rightSet y)]</code>







There also exists a very similar operation of `ldiv`.







Relational division encapsulates many notions of searching or optimizing. I invite you to read more about it in J.N. Oliveira's text or the Bird & de Moor text.







### Properties and QuickCheck





![](http://philzucker2.nfshost.com/wp-content/uploads/2019/07/sketch1562042676469-576x1024.png)Oh. Mah. Glob. You guys. So many properties. (Artwork courtesy of David)





Relation algebra is so chock full of properties. This is a perfect opportunity for some [QuickCheck ](https://begriffs.com/posts/2017-01-14-design-use-quickcheck.html), a randomized property testing framework. There are so many more to test. I need to dig through to collect up all the identities.






    
    <code>type R1 = Rel Bool Ordering
    
    prop_ridleft :: Rel Bool Ordering -> Bool
    prop_ridleft x = (rid <<< x) ~~ x
    
    prop_ridright :: Rel Bool Ordering  -> Bool
    prop_ridright x = (x <<< rid) ~~ x
    
    prop_meet :: R1 -> R1  -> Bool
    prop_meet x y = (x /\ y) <~ x
    
    prop_meet' :: R1 -> R1  -> Bool
    prop_meet' x y = (x /\ y) <~ y
    
    prop_join_univ :: R1 -> R1 -> R1 -> Bool
    prop_join_univ x y z = ((x \/ y) <~ z) == ((x <~ z) && (y <~ z))
    
    prop_join :: R1 -> R1  -> Bool
    prop_join x y = y <~ (x \/ y) 
    
    prop_meet_univ :: R1 -> R1 -> R1 -> Bool
    prop_meet_univ x y z = (z <~ (x /\ y)) == ((z <~ x) && (z <~ y))
    
    prop_top :: R1 -> Bool
    prop_top x = x <~ top
    
    prop_bottom :: R1 -> Bool
    prop_bottom x = bottom <~ x
    
    prop_bottom' :: R1 -> Bool
    prop_bottom' x = (x <<< bottom) ~~ (bottom :: R1)
    
    prop_trans_iso :: Rel (Bool, Ordering) Word8 -> Bool
    prop_trans_iso x = untrans (trans x) == x
    
    prop_rdiv :: Rel Bool Ordering -> Rel Word8 Ordering -> Bool
    prop_rdiv g j = (j <<< (rdiv g j)) <~ g
    
    prop_con :: R1 -> Bool
    prop_con x = con (con x) ~~ x
    
    prop_rdiv' :: Rel Bool Word8 -> Rel Bool Ordering -> Rel Word8 Ordering -> Bool
    prop_rdiv' x g j = (x <~ (rdiv g j)) == ((j <<< x) <~ g) 
     </code>







### Bits and Bobbles







  * Relations over continuous spaces. Vector subspaces (Linear Relations), Polyhedra (Linear inequality relations).
  * Non Bool-valued Relations. Replace $latex \exists_x$ with $latex \max_x$. The weighted edgelist of a graph is a natural relation. By using composition we can ask about paths. We still have a comparison operator $latex \subseteq $ which now respects the ordering of weights
  * [Galois connections are cool.](https://www.sciencedirect.com/science/article/pii/S1567832612000525)
  * Relations combined with recursion schemes. Recursion schemes are the point free way of describing recursion.
  * Moving into infinite spaces. How do we cope?
  * Faster search. Some relations are best specified by functions, Maps,  others, mixes and matching. 
  * If you "singletonize" relations a la the Agda project [https://github.com/scmu/aopa](https://github.com/scmu/aopa), you get very interesting [interconnections with profunctor](https://github.com/philzook58/rel/blob/master/src/ProRel.hs)s, which people say are a [categorical generalization of relations](https://bartoszmilewski.com/2016/07/25/profunctors-as-relations/).
  * [Point-free DSLs are interesting and pleasant](http://conal.net/papers/compiling-to-categories/). Many worries about alpha renaming are gone, at the expense of point-free pain. A DSL like this may be necessary to choose good relational query plans






Edit: A follow up post on that type level angle here [http://www.philipzucker.com/relational-algebra-with-fancy-types/](http://www.philipzucker.com/relational-algebra-with-fancy-types/)







### References







  * [www4.di.uminho.pt/~jno/ps/pdbc.pdf](https://www.google.com/url?sa=t&rct=j&q=&esrc=s&source=web&cd=1&ved=2ahUKEwj03e7d9r7iAhVodt8KHaf1DAUQFjAAegQIAhAC&url=http%3A%2F%2Fwww4.di.uminho.pt%2F~jno%2Fps%2Fpdbc.pdf&usg=AOvVaw0rK14EmhIYhNl_Kar8jshY) JN Oliveira Program Design By Calculation draft
  * [https://themattchan.com/docs/algprog.pdf](https://themattchan.com/docs/algprog.pdf) algebra of programming textbook
  * [https://en.wikipedia.org/wiki/Relation_algebra](https://en.wikipedia.org/wiki/Relation_algebra)
  * [https://github.com/scmu/aopa](https://github.com/scmu/aopa)
  * [https://www.sciencedirect.com/science/article/pii/S1567832612000525](https://www.sciencedirect.com/science/article/pii/S1567832612000525) Programming from Galois Connections
  * http://www.cs.tau.ac.il/~msagiv/courses/asv/absint-1.pdf Abstract interpetation notes
  * [https://forum.azimuthproject.org/discussion/1828/lecture-4-chapter-1-galois-connections](https://forum.azimuthproject.org/discussion/1828/lecture-4-chapter-1-galois-connections) John Baez on Galois connections [https://www.azimuthproject.org/azimuth/show/Applied+Category+Theory+Course#Course](https://www.azimuthproject.org/azimuth/show/Applied+Category+Theory+Course#Course)
  * Backhouse algebra of programming for graphs [http://www.cs.nott.ac.uk/~psarb2/MPC/BasicGraphTheory.pdf](http://www.cs.nott.ac.uk/~psarb2/MPC/BasicGraphTheory.pdf)
  * [http://relmics.mcmaster.ca/html/index.html](http://relmics.mcmaster.ca/html/index.html)






Edit : A math exchange question about `a -> [b]` relational type. [https://math.stackexchange.com/questions/3360026/can-division-be-expressed-intensionally-in-relation-algebra/3361351#3361351](https://math.stackexchange.com/questions/3360026/can-division-be-expressed-intensionally-in-relation-algebra/3361351#3361351)








Edit: An interesting comment and related library from /u/stevana


[Comment](https://www.reddit.com/r/haskell/comments/c8bdpk/a_short_skinny_on_relations_towards_the_algebra/eslwxp7/) from discussion [A Short Skinny on Relations towards the Algebra of Programming - Hey There Buddo!](https://www.reddit.com/r/haskell/comments/c8bdpk/a_short_skinny_on_relations_towards_the_algebra/).






