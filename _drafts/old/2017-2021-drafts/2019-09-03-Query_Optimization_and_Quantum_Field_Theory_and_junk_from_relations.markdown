---
author: philzook58
comments: true
date: 2019-09-03 22:24:11+00:00
layout: post
link: https://www.philipzucker.com/?p=1984
published: false
slug: Query Optimization and Quantum Field Theory and junk from relations
title: Query Optimization and Quantum Field Theory and junk from relations
wordpress_id: 1984
---




### Junk from second relation article







I think that post gets the beauty of the concepts across well, partially thanks to list comprehension syntax. 







One way to do this is with syntax. The english sentence "The set of tuples of all integers and their successor" does convey something from me to you and has meaning. It is quite difficult to get a machine to take something like this in and even for the usage of humans it is both somewhat verbose and imprecise. Hence we have developed formal symbolic languages to express ideas like these in a more precise way.







What exactly does separate numerical and symbolic computing. How is a double any less symbolic? It's a bizarre collection of 64 bits that have operations that vaguely resemble those of numbers. Is interval arithmetic symbolic or numeric? Polyhedral computation? Is a BDD symbolic?







And yet there does seem to be a distinction in my mind at least.







basically so you can avoid replicating the functionalty that has already been paid for and written for the language to exist. After all, interpreters/compilers for any languages are writeable in any other language that is Turing complete, so they are different only in what is low hanging fruit. How boring.







There are a couple of things interesting about this. 







  * It's fun to dink around in the type system.
  * The forall quantifier in the type.
  * The type system gives us a rich symbolic manipulation system, one way of avoiding the finite constraint and making it more efificent, albeit less automatic.
  * The connection to already seen concepts and data types in Haskell libraries.






You could do this anyway with smart constructors, for example . The big difference comes in on the pattern match. The smart constructor sort of loses information. With GADTs, you don't lose that type information. The type system knows that when it sees the constructor there were only so many types that could have done it.






    
    <code>type PetSerialNum = Int
    data PetName a = Barker PetSerialNum | Meowby PetSerialNum
    data Pet = Dog | Cat
    
    barker :: Int -> Name 'Dog
    barker = Barker
    meowby :: Int -> Name 'Cat
    meowby = Meowby
    
    data Name' a where
       Barker :: Int -> PetName 'Dog
       Meowby :: Int -> PetName 'Cat
    
    getCatId :: PetName 'Cat -> Int
    getCatId (Meowby x) = x </code>







We can take a dependently typed approach to relations. This is very similar to what can be found in the Agda Algebra of Programming library [https://github.com/scmu/aopa](https://github.com/scmu/aopa). 







One interesting trick for embedding Set style thinking into relational algebra is the idea to replace any set with a relation that is just two copies of the set. $latex R = {(a,a) | a \in S}$. This is a kind of projection or guard relation. When you compose it with another relation, only those components that are within the guard relation will remain in the result. I think the identity relation specialized to a data type can be called a "doubleton". It is a singletonized data type with two copies of the type parameter.







When you type check a program, even languages without very fancy types, you/the compiler are working together to prove something.  This is a reasonable notion. When the result of a function has type int, that fact is proved by making sure it . These systems are fairly ad hoc however and it is rather difficult to summarize exactly what has been proved other than restating exactly the typing rules. When you compile a C program and it successfully type checks, you have proven to me that baring errors within the implementation of the type checker certain problems cannot occur in my program. I do not accidentally add a bool and an int.







I'm not sure that thinking in this way is the best conceptual road for the weirdness that lies within the Curry-Howard correspondence, but it at least points are that type checking and inference are demonstrating the truth of some facts, even in the simply typed case.







There are more common types in Haskell with this kind: Category, Arrow, and Profunctor. What we are doing is definitely connected to all of these, but not directly. Our relations do not implement any of these typeclasses.







#### Translating Functions to Relations







The thing is, the beauty and the pain of functions is that they are fairly opaque. They also are constrained to be functions. 







Kind of the immediate purpose of relations was that they are like functions, but more flexible. So we should figure out how to lift functions to relations. It is a fairly mechanical process.







This proposition might be able to be shown or not. If you can find a value for that type, only then those elements are a part of R. You can write down the type `Not 'True 'True`. You are not going to be able to find a value to inhabit this type.  







### Building Relations out of Relations. Fancy Cartesian Arrow Stuff. Relational Algebra -







There is a sense that the more you can avoid looking at the sticky details inside 







What is an algebra? It's a rich system of manipulation that allows you to know things that aren't obvious at the outset. Anything that feels similar enough to high school algebra to be reasonably be called algerba is an algebra.







The algebra of relations is very cool.  If you avoid defining too many primitive relations like the above and build them out of combinators, you expose a rich high level manipulation. Otherwise you are stuck in the pattern matching dreck.







We can mix and match the relational reasoning and the singleton style reasoning. The relational reasoning operates at a higher level.







Actually, maybe they shouldn't and the incoming relation should come in the same way as ordinary parameters. In this way, there is going to be a record of how the relation was built in the type of the relation. 







There is something very aesthetically pleasing about finding composition in all things. 







Recursion schemes. We don't need recursion schemes necessarily to do recursion. Check out the definition of append. However, if we want to manipulate recursion in the algebra of programming style we do.













A lot of the coolness of the algebra of programming comes from realizing the point free necessity of the arrow like operators.







Category theory informs this definition what does it mean to be a tuple or sum type? My small exposure to category theory is the thing that informs me of an alternative formulation of a product type is not the tuple constructor `(,) :: a -> b -> (a,b)` and fst /snd, which I think is the more obvious answer, but instead we can use fst, snd and `fan :: . fan` can be found in Control.Arrow and can be represented with the following diagram. 







Similarly, the first approach to the essence of a sum type is `Left` `Right` and `either :: (a -> r) -> (b -> r) -> Either a b -> r`







### Categorical Operators. Relational Operators / Algebra. 













The two slot kind k :: a -> b -> *  

(->) is the canonical example. We gotta use (->) to do anything and most general things have examples in (->).  

There are three main type classes to talk about  

No type class  

Category







Profunctor  

Since we're working with datakinds, which do not have inhabitants, you will not be able to produce values of type (a->b). You can take them in as hypotheticals though.  

Or maybe you can make those functions because they are basically void.







Arrow - arrow is a little oddball because of the requirement of arr : (a -> b) -> k a b  
The intent there was to have the analog of monadic return / fmap. If you have a pure function, we can lift it into the context. 







newtype Terminal a (b :: ()) = Terminal (Top a b)  
newtype Initial (a :: Void) b = Initial (Bottom a b)







Galois connections get their name from the correspondence between Symmetry Groups and Extension Fields. But fuck that.







Or it can be defined via indirect equality.













There are often a couples forms of definitions depending on whether they quantify over elements or entire relations. There seems to be a general feeling that the definition that quantifies over relations is the more elegant one?







Even for finite sets, where we really can enumerate all of the elements, it can be completely infeasible to actually do so. There are just too many of them to make an entry apiece in a data structure held in memory.  
The intervals . It is entirely reasonable to restrict yourself to intervals. Then you only need to store the left and right end of the interval regardless of how big the set itself is. However, then you can't perfectly form the union of two intervals. That is not necessarily an interval. But you can find the best approximating interval to the actual union. This new interval is the join







The point of the right division is that






    
    <code>curryRan :: (Procompose p q :-> r) -> p :-> Ran q r
    uncurryRan :: (p :-> Ran q r) -> Procompose p q :-> r
    </code>







The indirect version of the same property is. Nope nevermind. This is exactly what these two are.






    
    <code>forall x. (x :-> Ran g j) <-> (x <<< j :-> j) </code>







### Relational Division and Kan Extensions. Galois Connections







[http://hackage.haskell.org/package/profunctors-5.4/docs/Data-Profunctor-Ran.html](http://hackage.haskell.org/package/profunctors-5.4/docs/Data-Profunctor-Ran.html)







Kan extensions are a funny fellow and completely defy  
If we consider functor composition to be functor multiplication,  
a Kan extension is functor division.







Similar to the lattice idea above, where true set intersection and union were unavailable , so we did the best we could do, Kan extensions 







Kan extensions vs Galois Connections. Kan Extensions are deeply entrenched in the category theory terminology. Galois connections are the analog/example that exists in Lattice theory and is relatively more straightforward to think about, because you don't have to unwrap quite so many subtle definitions in your head.







Sometimes you want to invert a function that does not actually have an inverse.







Like y = x^2 has two points in the inverse image of y=1. But in the interval arithmetic, you can't represent 2 points. The best you can do 







There are a couple different equivalent formulations of kan extensions







The Kan extensions in the kan-extension package (adjunction?) are special cases







Huh. Yeah. Regular ol function inverse is an example. Any function is monotonic with resepct to the set ordering if you consider







How do we actually define this function inverse in more generic terms? Well, we want the "best" approximation. 







Another place we can do this, in a simpler and yet somehow more confusing setting, is the natural numbers. 







Rounding. A rounded integer is actually representing the entire set between [x-0.5,x+0.5)







Profunctors are described as a categorical generalization of relations [https://bartoszmilewski.com/2016/07/25/profunctors-as-relations/](https://bartoszmilewski.com/2016/07/25/profunctors-as-relations/),  but to be honest, I kind of don't get it. Despite many of our constructions appearing in the profunctor package, the profunctor typeclass itself appears to not play a role in our formulation. There just isn't a good way to dimap under our relations as written, unless you construct free profunctors.







Get to abuse the facilities of the type system for convenient purposes. In order to deal with infinite domains or very large finite domains, you need a way of describing and manipulating them compactly. The type system gives us a natural syntactic description of our domains. Sometimes I think that most programming cleverness boils down to finding a good way to hack the preexisting language facilities to do something they weren't necessarily intended to, using them as a kind of ubiquitous library.







I'd like to think the formulation of relations in this manner can be used to do something practical, but I'm skeptical it is viable for large scale problems. I'd love to be proved wrong.







In that approach, you build a singletonized version of every data type that reflects the value up into the type system by construction.







------------







[http://www.cs.ru.nl/B.Jacobs/CLG/JacobsCoalgebraIntro.pdf](http://www.cs.ru.nl/B.Jacobs/CLG/JacobsCoalgebraIntro.pdf) coalgerba as transition system. a -> f a. f may represent non dterminsims, partilaity.







Term rewriting is an interesting set of relations







Abstract rewriting is almost pure relational algerba. It is properties to discuss about relations from a to a. Closure. Confluence. 







Term rewriting is working on syntax trees. This is similar to what i was pushing at with the unification stuff. The rules can implcility, explicitly be in any context?







Maude, Nipkow book [https://www21.in.tum.de/~nipkow/TRaAT/](https://www21.in.tum.de/~nipkow/TRaAT/)







Union-find and substitutions. Union find has the lazy parent pointer pushing. They are building tree structures that do the same thing.







OBDD library uses an intmap rep. Bohm-Berarducci and fix. Didn't seem to be all that similar. Well kind of. Fix f ~ forall r. (f r -> r) -> r which is similar to fix :: (a -> a) -> a (f ~ Identity does the trick).   This is basically the generic form of cata. This is the piece of the church encoding of Free that represents Roll . Takes (f a -> a) and f a -> . I wrote this down somewhere. \f -> cata f x is one direciton. x = f Fix is the other.  







Compose s f g a  Compose f (Compose (STRef s) g)







Indirect s f = Compose f (STRef s)  







[https://www.javerianacali.edu.co/eventos/international-school-rewriting-2018](https://www.javerianacali.edu.co/eventos/international-school-rewriting-2018) summer school







Rewrite rules as a category. 







Relations ~ linear algerba . Gaussian elminiation ~ Grobner basis. rewrite system knuth bendix







Word problems. Rewriting on monoid (tree structure flattened)







Universal algebra - talking about rewrite rules?













data AllVariance x where  
   Var :: (a -> AllVariance b) -> [(a, AllVariable b)] -> AllVariable (a,b)  
   Done :: AllVariable ()







{ a -> b -> c, a -> (b,c), b -> (a,c), (a,b,c) , a -> b -> c -> Bool  }







plus = {(+), \x y z -> x + y == z, (-), \x -> [(y, y + x)] , and others}







-- data structures  

data Expr = Var Int | Pair Expr Expr | Atom String







data = Var f | Compose Expr Expr | Id | 







data Expr a where  

    Var Int :: Expr a  

    Pair :: Expr a -> Expr b -> Expr (a,b)  

    Atom :: Expr (a :: String) 







unify (Var i) (Var j) env | i == j = Just env  

                          | otherwise = lookup* i env  

unify (Atom x) (Atom y) env | x == y = Just env  

                            | otherwise = Nothing  

unify (Pair x y) (Pair x y) = do   

                                env' <- unify x x' env  

                                unify y y' env'  

unify _ _ = Nothing  

what if relation is unification interface combined with  

env expansion







type Rel = unifyenv -> [newunifyenv]  

sooo pointful  

/\ = conj  

\/ = disj  

. = x === x'







type Rel = UnifyMap a b -> [UnifyMap a b]  

Rel ~~ Goal







UnifyMap where







UnifyMap a b -> UnifyMap b c -> Subst b (a,c) -> UnifyMap







trinagular in the sense that things higher in the tree…  

things lower in the tree can only be substitued for things higher. The types are scoped  

data Subst = Map String Term  

walk subs  

quantifier elimination for b.







data Rel a b = [(a -> Rel a b,  b -> Rel a b)]







data Rel a b = PosA a (b -> Rel a b) | PosB b (a -> Rel a b) | Ind Bool |   

we don't get to pick?







Pos a (b -> Bool) | PosB b (a -> Bool) | Ind a -> b -> Bool | 







b -> [a] requires b first. (1/(1-a))^b -- this is a monad  

[(a, b -> Bool)] interesting refactoring. 1/(1 - a*2^b)  

[(b, a -> Bool)] -- this is not a monad.  

[Either 1 2]  

[(a,b)]  

a -> b -> Bool  

[(b, a -> (Bool, Rel b a))]







-- indeed a slightly different stream  

compose :: Rel a b -> Rel b c -> Rel a c -- no Eq constraint  

compose f g = [ (a, gc ) | (a,fb) <- f, (b, gc) <- g, fb b ]







compose :: a -> [b] -- this one is a monad







a -> [(b, b -> a)]  

a -> [(b, b -> [a])]  

ComboRel = {   , Maybe (ListRel a b)







Haskell already has unification, at the type level. i should just use that







a source of fresh variables. Polymorphism pump  

fresh ~ (a, fresh')







singleton search?  

SNat a -> [exists b. SNat b]







(a ~ b, b ~ c, c ~ d, )  

Conjunction is easy  

Disjunction is the difficult one.







type family Unifies  

   Unifies a a = True  

   Unifies a b = False  

a ~ b == Unifies a b ~ 'True,  

a !~ b == Unifies a b ~ 'False







Nat ~ 'Z || 'S a 







conde







Clause (n+1) <= Clause 1 'S  

Clause 2 a <=   

Query '[(env, goals/predicates)] freshsrc 







conj = (,,,) (bind)  

disj = Even \/ Odd     (mplus) 







Complete disjunction is easy because doesn't actually branch  

indeterminate disjunction is harder. Need to copy all type variables







Copy (((V a, V b),V c) = ()







type family Run  

   Run (Disj x y) = '[]







type family Disj  

   Disj x y = [x, y]  

   Disj f g env = (f env1) ++ (g env2)







but a could be unified from under our feet. Program will fail if so, since   

CopyEnv   

   CopyEnv (Fresh a ': env) =  (a ~ (a',a'') , Fresh a' , Fresh a'' ) :' CopyEnv env  

   CopyEnv (b ': env) =  CopyEnv env  

   CopyEnv [] = []  

-- mark any unification as NotFresh. we also have to register any new vars in the env  

CopyEnv (NotFresh b) ': env =  Copyenv env  

CopyEnv a ': env = (a ~ (a',a'') , a', a'') :' CopyEnv 







failure of a branch. We can't really catch it.







unzip CopyEnv







appendo = [(x,xs,xxs)]







class Apply f a b where  

   apply :: f -> a -> b







Do I always need to be doing explicit first order stuff for







HOAS   

PHOAS  

Cat  

Tagless







appendo (x, xs, xxs ~ x ':xs)







data UniDSL env where  

    Fresh :: a -> UniDSL env -> UniDSL a ': env 







\x y -> (Unify x y) -- I'm suppose to tell you what you gave me?  

pattern matching a gadt is unification







instance (a ~ b) => Unify a b   

   unify :: a -> b -> ()







unify' = reflect unify reify







exists x xs. (x ': xs, x)







Fresh :: (a ->  DSL a ': env) -> DSL env







env -> '[env]







disj







->







type IntervalRel a b = (Interval a, Interval b)  

type IntervalRel r f g  = (f :*: g) (Interval r)  

concrete :: IntervalRel r f g -> ListRef (f r) (g r) -- enumerate  

abstract :: ListRel (f r) (g r) -> IntervalRel r f g -- outer interval abstraction







-- fine  

f a b ~ x  

z ~ (x,y)







Can't just try stuff though







BEnum ()







forall a. a ->







Eq  

(   ~   )  

Iso  

( ~~  )







TODO  

Pack  

Buy plane tickets  

Finish perciplex report sections  

empty car more - need to get packs in  

go to rei







UList  

type URel a b = {[(a,b)] -- [(a,b, varmap)]  

compose x y = [ (apply subst a, apply subst c) | (a,b) (b',c) , let subst = unify b b', if substs exists  ]  

replace equality with unification  

unif :: Unifiable a => URel (a,a) Bool --? URel (a,a) () -- URel (a,a) a  

appendo :: URel = []







unif = [ ((Var 0, Var 0), Var 0) ]  

unif = converse dup







id = [(Var 0, Var 0)]  

fan  

fst = [((Var 0, Var 1), Var 0)]  

snd =   

join = ++ -- can prune any patterns that are subsumed by the others though  

meet = [ (apply sub)  , (a,b) <- , (a',b') <-, let sub = unify a a', let sub = unify (apply sub b) (apply sub b') ]  

converse = same as before  

 rSub x y = (a,b) subsumed by (a',b'),   

 for every term p in x, there is a term q in y auch that y is more general than p  

  there is a term q in y such that everyx is a specialization of that term







With unification variables there is a partial ordering.  

meet and join







a can unify with everything it is bottom







class Unifiable x where  

  unify (x : xs) (y : ys) = do   

                            sub <- unify xs ys  

                            let x' = apply sub x  

                            let y' = apply sub y    

                            sub' <- unify x y  

                            return (sub ++ sub')  

    unify 







data UTerm x = UVar Int | TrueTerm x







data UTerm1 f = UVar Int | UFix f (UTerm1 f)  

UTerm (Const Int) == UTerm







data UList a b = Cons a b | Nil  

data UNat a = Succ a | Zero  

instance Unifiable a => Unifiable (UFix (UList a)) where  

  zipMatch (Cons) Nil = Nothing  

  zipMatch Nil Cons = Nothing  

  zipMatch (Cons x y) (Cons x' y') = let res = zipMatch x x'







data MyThing = Foo Int | Bar String Bool  

--> UInt | Bar







expand variable one layer.  

expand (Var) = [ (Con1 Var, Con2 Var  ]







subsumption lattice  

ULattice = Term {leftside :: (a,b), rightside :: (a,b) }  

x /\ y = unify the two terms  

x \/ y = term that can unify to both







Even single unifcation term is a relation. It is an abtraction that specifies and inifite set of things







top = a (a variable)  

bottom = unification failure







PowerSet construction on top => ListRel UVar







[URel] ->







The maybe relation  

data MaybeRel a b = Maybe (a,b)







compose Nothing _ = Nothing  

compose _ Nothing = Nothing  

compose (Just (a,b)) (Just (b',c)) | b == b' = (a,c)  

                                   | otherwise = Nothing  

Nothing is bottom  

there is no top?







Subsumption lattice is a very antural form of abstraction for synatx tree like structures  

Which includes algebraic data types







Another interesting lattice = the product lattice







Prod = { x :: [], y :: [], z :: [] }  

The full set Set (x,y,z) and {x ::[], y :: [], z :: []} are not equilabelent  

[Prod] gives evenough power.  

 Like low rank decomposition. Which I really wonder, will that give some kind of heuristic?  

"Never expand a kron"  

Equivalent of Interval arithemtic for finite sets.







data Join == ( , ) -- join is also product  

data Meet r1 r2 a b = (r1 a b, r2 a b)







-- becuase meet is g  

data Meet ProdRel FunRel ~~ [a], [b], a -> b -> Bool  

data Join r1 r2 = 







type Bottomed r a b = Maybe (r a b)  

type Topped ??  

data ProdRel a b = ProdRel [a] [b]  

data ConcreteRel a b = Maybe a b  

data JoinList r a b = [r a b] -- The "power" of a relation  

JoinList ()







Can we bring meet and join through these? Using distributive properties.  

Can we compose through these? I think so because of monotonicity of most things.







Yes, I should have a system for combining representations







Relation r2, Relation r2 => Meet r1 r2







-- candidates + filter (half functional rep)  

-- push candidates from factors, filter with set.







{left :: [a] rght :: [b], filter :: a -> b -> bool}  

compose = {as, cs  } 







id = {left :: [b], right :: [a] , filter = eq}  

or => { left :: [a], right :: [b] :: dense :: [(a,b)] :: }  

neq = left :: [a], right = [a] , filter = /=  

but really  

   (a,b,c,d) (,c,v,,d)  => one list per. The whole product table should be borken up





[a]





[b] [c] [d] ->  one list for every sudoku slot








data CSPRel   

  Leaf :: [b] -> [a] ->







Since csp is like Interval =>  

CSPRel r f g = f [r], g [r],  







typical CSP works in these spaces. I guess this is kmett's propagator thing  

/\  

\/  

Rel  

pumping the galois connection  

Arc consistency   

f . g







* * *







[Query optimization](https://en.wikipedia.org/wiki/Query_optimization) is the process of taking a database query and finding an efficient way to achieve it, both at an abstract logical level (relational algebra manipulations), and at the physical level (What algorithms to use, what indices do you have, other)







When you want to perform the sums in a big tensor algebra expression, it can matter a lot the order in which you do the sum. A bad choice can lead to intermediate data structures that are growing exponentially in size. Sometimes, that is unavoidable, but sometimes it isn't. Another important task is recognizing shared substructure in many expressions. That can avoid duplications of work.







The algebra of relations has a lot of similarity to linear algebra.







A database can be thought of as a big tensor, with a 1 for every entry in the database, and a 0 if it is not. Instead of addition and multiplication, The tensors are combined using boolean algebra. If we consider tensors with only non-negative entries, the connection is even closer. Multiplying two non-negative numbers is the same as an AND if we consider 0 to False and anything non-zero to be True. Sum is the same as an OR in the same manner. If you were interested only in the non-zeroness rather than an actual value, you can shortcut the summation operations as soon as you find a single non zero piece of the sum.













Another way to think about it is as matrix sparsity structure. It is not uncommon to have insanely sparse matrices. In that case, one wants to perform their operations in a manner as to best exploit the sparsity. The Taco compiler [http://tensor-compiler.org/](http://tensor-compiler.org/) is doing something very akin to a query optimizer. Tensors come in different formats (sparse of different column ordering, dense, low rank, hierarchical, others undreamed). Transforming between formats has cost. This is similar to transforming databases to new indices or whether it makes sense to do a hash join vs a sort join.







Roughly columns of databases correspond to indices on tensors.







The join operation corresponds to relational composition. 







$latex a(R \cdot S)c = [(a,c) | \exists b. aRb, bSc]$







Both $latex \sum$ and $latex \exists$ are binding forms that introduce new local dummy variables. You can change the name of a dummy without changing the meaning of an expression (alpha conversion) and you cannot refer to the dummy out of the scope of the binding form. The binding form operator sort of destroys that variable. Other examples of binding forms include integration $latex \int$, $latex \prod$, $latex \max$, $latex \min$, $latex \forall$, and lambda functions $latex \lambda$. 







Considering relations as matrices, this does correspond to a row times column multiplication, e.g. matrix composition.







The transpose operation is the same as the relational converse operation. Both do very little and are involutive.







Sums of tensors are like unions of databases of the same column. Products can be similar to intersections / joins.







Feynman diagrams for databases. Databases can be represented by vertices of different arity. Different column types are different particles.







The relation algebra is a point-free formulation of the calculus of relations. The point-free form of linear algebra is the standard matrix algebra, which does not explicitly state indices. $latex AB$ is the composition of matrices. It feels laborious to convert a tensor expression to a completely point-free style, but I believe it is possible. The trans-untrans operator let's you flip indices from the input to the output of a matrix/relation. The vec operator is a relative of these.  The kronecker product. The Khatri-Rao product as a fan. Despite the 







One of the most fascinating operators in linear algebra is the matrix inverse operations. The relation algebra has the notion of quotients of relations. These are not quite the same thing although they 







The matrix calculus is usually phrased in terms of equality, whereas the relation algebra is phrased in terms of a partial order of relations. How do we reconcile this? Relations are rarely perfectly invertible. We are used to the comfort of square full-rank matrices. The pseudo inverse is a candidate.







Linear algebra is just that: linear. Relation algebra doesn't really have that. 







Low Rank relations. It is not crazy that a relation might be decomposed into the composition of relations meeting in a mutual small domain. If this is the case, definitely such a fact can be abused to great effect.







Eigenvectors? Relational Counterpart unknown







Least Squares? Relational Counterpart unknown







See J.N. Oliveira's papers







Triangular relations. Partial Orders are triangular relations. Triangular matrices are important in linear algebra. They are more easily inverted. Gaussian Elimination proceeds by finding a decomposition into triangular matrices.







With appropriate infrastructure, all of these things can be embedded into a functional language, but the relation language makes it cleaner.  Relations extend the power of functional descriptions to non implementable ones.







It is only a slight shift from the idea of a command. If I give you an input, you give me an output.







All computer programming languages ultimately have to be run on machines.







Hence a relational specification may not be able to be directly run without some kind of transformation.Then through a formal or informal process, one writes an implementation that satisfies the spec. 







The dream is perhaps to one day have a language and compilation system that can capture all these goals at once.







Then the proof process connects in a formal way another form with new desirable properties (executability and efficiency at the expense of clearness and compactness). The dream is perhaps to one day have a language and compilation system that can capture all these goals at once. Haskell does a good job of being a very good compromise at both. You lose a little performance for massive gains in clarity and compactness, a worthy compromise. I have no metrics to show you. It is merely my opinion.







A specification of a sorting function may be something like "out of all possible permutations of the elements of the input, pick one that is sorted". Then by some transformations or laws you connect this spec to the same result as a more complex quicksort or whatever.







However, if you are going down the road of a separate spec, it makes sense to add to your specification language constructs that are not necessarily executable or efficient. Hence a relational specification may not be able to be directly run without some kind of transformation. t extends the descriptive abilities of a functional transformation.







Relations extends functions with nondeterministic choice, failure, converse . With appropriate infrastructure, all of these things can be embedded into a functional language, but the relation language makes it cleaner. The rough Church Turing Thesis is any sufficiently complex thing can embed any other sufficiently complex thing. But it might be an ass pain. We want happy asses don't we?







Why care about relations? You're a functional programmer. Functions are a specialization of relations.  Relations extend the power of functional descriptions to non implementable ones.







What if i told you that you . I and others are always seeking the means to express ourselves. What is the goal of programming languages? To bring the mind in synchrony with the computer. To be have the means to express your intent completely and easily. Dependenlty type languages like Agda and Coq have the ability to express very sophisticated intent at the price of ease of use. Haskell lives at a very useful point of the trade off curve.







Functional programming is a good paradigm because the concept of a function is an intuitive one. It is only a slight shift from the idea of a command. If I give you an input, you give me an output.







Functions live near efficiently 







All turing complete paradigms can emulate each other. I could write GHC in assembly. The cost is to the mind, the ease with which you can reach for different concepts. Programming languages are the water you swim in while programming.







Prolog in particular 







Relations interweave interesting analogies and techniques between disparate fields. Linear algebra, Database systems, functional programming, logic.







I think it is very neato for some reason. If anyone ever thinks something is really neato, isn't it worth giving it a listen?







To get started with relations, I feel you need to discuss the pointful underlying conceptual model. I don't see how I can understand without that.







liftSet :: [a] -> Rel a a  

liftSet = map dup







leftSet :: Eq a => Rel a b -> [a]  

leftSet = nub . (map fst)







rightSet :: Eq b => Rel a b -> [b]  

rightSet = nub . (map snd)







rtop :: (Enum a, Bounded a, Enum b, Bounded b) => [(a,b)]  

rtop = [(x,y) | x <- enumAll, y <- enumAll]







rbottom = []







rcompose :: Eq b => Rel a b -> Rel b c -> Rel a c  

rcompose xs ys = [ (a,c)  | (a, b) <- xs, (b', c) <- ys, b' == b]







rid :: (Enum a, Bounded a) => Rel a a  

rid = liftSet enumAll







rconverse :: Rel a b -> Rel b a  

rconverse = fmap swap







untrans :: Rel a (b,c) -> Rel (a,b) c  

untrans = map assoc where assoc (x,(y,z)) = ((x,y),z)







untrans :: Rel a (b,c) -> Rel (a,b) c  

untrans = map assoc where assoc (x,(y,z)) = ((x,y),z)







rmeet :: (Eq a, Eq b) => Rel a b -> Rel a b -> Rel a b  

rmeet xs ys = [x | x <- xs, x `elem` ys]







rjoin :: Rel a b -> Rel a b -> Rel a b  

rjoin = (++)







untrans :: Rel a (b,c) -> Rel (a,b) c  
untrans = map assoc where assoc (x,(y,z)) = ((x,y),z)






    
    <code></code>







  * Composing relations $latex R \cdot Q = {(a,c) | \exists b \in B. (a,b) \in R, (b,c) \in Q }$. Check that this does match composition of functions.
  * Identity relation $latex id_A = {(a,a) | a \in A}$
  * trans and untrans are the equivalent of currying. $latex (a,b)Rc \equiv aR'(b,c) $
  * Orderings can also be lifted to relations $latex (\leq) = {(a,b) | a \leq b}$ 
  * Sets/Subsets can be lifted to relations as a diagonal relation. ${(a,a) | a \in S }$. Projection onto the set can be achieve by composing with this relation. The identity results if you are talking about the entire set S. In this way, many set theoretical constructions can 
  * Relations have a notion of ordering corresponding to the subset ordering of their sets $latex R\subseteq Q \equiv \forall (a,b) \in R, (a,b) \in S$
  * Relations inherit the least upper bound and greatest lower bound from their originating lattices also.
  * Power and element relations. $latex \in = {(a,S) | a \in S, S \in P A }$. $latex \Lambda R = {(a,S) | (a,b) \in R, b \in S, S \in P B}$ These two constructions are ways of converting a relation to a function. Or sort of reifying set-like relationships. An element being in sets can be reified into a relationship. This is also interesting in that these bring clues as to how one could implement relations in a programming language, where basically you have functions more that you have relations. The power construction is similar to `a -> [b]` where you can think of `[b]` as kind of like an element of the power set of B.






The most primitive is `[a]`.  A slightly more interesting one if `a -> Bool` which represents a set.  This is similar to how reindexing a database is expensive.  The containers package holds an actual Set data type, which holds the elements in a search tree for fast querying and other operations. 






    
    <code>import Data.Set
    
    type ListSet a = [a]
    type FunSet a = a -> Bool -- FunSet
    type Set'''' a = Map a Bool -- a table of the above
    type Set''' a = (Set' a, Set'' a)
    
    enumAll :: (Enum a, Bounded a) => [a]
    enumAll = [minBound .. maxBound]
    
    set2set :: (Enum a, Bounded a) => Set'' a -> Set' a
    set2set pred = filter pred enumAll
    
    union :: Set'' a -> Set'' a -> Set'' a
    union pred1 pred2 s = (pred1 s) || (pred2 s) 
    
    intersect :: Set'' a -> Set'' a -> Set'' a
    intersect pred1 pred2 s = (pred1 s) && (pred2 s)
     
    empty :: Set'' a
    empty = const False
    
    full :: Set'' a
    full = const True
    
    singleton  </code>







rOrd' :: (Ord a, BEnum a) =>Rel a a







Point-Free Relations and Linear Algebra







The above combinators and relations, in combination with the lifted forms of the standard categorical combinators gives us a rich language






    
    <code>rfan :: Eq a => Rel a b -> Rel a c -> Rel a (b,c) 
    rfan f g = [ (a, (b,c)) | (a,b) <- f, (a',c) <- g, a == a']
    
    rfst :: (Enum a, Bounded a, Enum b, Bounded b) => Rel (a,b) a 
    rfst = map (fst . snd) rid
    
    rsnd :: (Enum a, Bounded a, Enum b, Bounded b) => Rel (a,b) b 
    rsnd = map (snd . snd) rid
    
    rleft = (Enum a, Bounded a) => Rel a (Either a b) 
    rleft = rmap Left rid
    
    rright = (Enum a, Bounded a) => Rel a (Either a b) 
    rright = rmap Right rid
    
    reither :: Eq a => Rel a c -> Rel b c -> Rel (Either a b) c 
    reither f g = (lmap Left f) ++ (lmap Right g)</code>







Linear algebra has the most widely used point free notation in the world, matrix notation. Standard matrix notation is a point free notation for linear algebra $latex Ax=b$ and $latex X = ABC$ as compared to $latex \sum_j A_{ij} x_j = b_i$ and $latex X_{il} = \sum_{jk} A_{ij} B_{jk} C_{kl} $







Both $latex \sum$ and $latex \exists$ are binding forms that introduce new local dummy variables. You can change the name of a dummy without changing the meaning of an expression (alpha conversion) and you cannot refer to the dummy out of the scope of the binding form. The binding form operator sort of destroys that variable. Other examples of binding forms include integration $latex \int$, $latex \prod$, $latex \max$, $latex \min$, $latex \forall$, and lambda functions $latex \lambda$. 







### Linear Algebra, Databases, and Relations







Relational algebra has a great similarity to linear algebra. This connection can be made more clear by considering sparsity patterns of matrices and tensors. Sparsity patterns are an abstraction of linear algebraic operations. Instead of considering matrices of numbers, instead the entries are "zero" and "possibly nonzero" or, if you prefer, a matrix of boolean values corresponding to those same questions.







DataBases, Boolean Matrices. Fin Rel. Either relations with only finitely many (non zero or non false) elements, or relations over finite domains which is slightly simpler. Composition of relations is closely connected with the idea of database joins. Joins are kind of a projected cartesian product. The boolean matrix picture is very interesting because it brings in a shadow of linear algebra. If we replace * with AND  and + with OR, then the ordinary row times column matrix multiplication is the same as composition of relations. Only if there is a True in the same location in the row of the first matrix and a column of the second is the entry of the output matrix also True. Another way of looking at this is as sparsity patterns. Sparisty patterns of matrices absrtact away the actual values and just tell you if an entry is zero or nonzero. We can sometimes guarantee the matrix product is zero in an entry of the output by looking at the sparsity pattern of the incoming matrices. DataBase engines, prolog, SAT solvers. CSP solvers.







Databases can be thought of abstractly in the same way. A Database holds entries and the entries can either be in the database or not. A database is usually insanely sparse. The index space of a column could be all possible names, or all possible timestamps, but you almost certainly will only have a few, maybe a million or billion or so. 






    
    <code>type LinRel r a b = [(a,b,r)]
    lincompose p q = [(a, c, x*y) | (a,b,x) <- p, (b',c,y) <- q, b == b']
    maxpluscompose p q = nub' [(a, c,  x + y) | (a,b,x) <- p, (b',c,y) <- q, b == b'] 
    -- shortest path.
    id = [(a,a,1) | a <- enumAll]
    maxnub =  -- important to have unique. compress maximum.
    linnub =  -- add together
    sub x y = all [ r <= r' | (a,b,r) <- xs, (a,b,r') <- ys, a == a', b == b']
    -- Use positive semidefinite as <= ? Needs square matrix though right?
    -- for all v w, v A w <= v B w ? = w (A - B) v <= 0 ?
    -- A * B^T ? det something? minor something? span(A) <= span(B)
    -- LinearRelations rather than linear operators. linear operators are functions. Multivalued?.  
    
    </code>







The relational model of databases. The mathematical model of databases is associated with the [Relational algebra ](https://en.wikipedia.org/wiki/Relational_algebra) of Edgar Codd. It is very related to relation algebra, but with some different feels and connotations.  The relations do not have a left and right side, but are instead organized by global column labels.







The join operation corresponds to relation composition. However, the standard join operation seems to be defined such that the joined upon columns remain in the result. Also join just uses all matching column names, whereas relation algebra composition disposes of the joined upon columns.







$latex a(R \cdot S)c = [(a,c) | \exists b. aRb, bSc]$







Another way to think about it is as matrix sparsity structure. It is not  uncommon to have insanely sparse matrices. In that case, one wants to  perform their operations in a manner as to best exploit the sparsity.  The Taco compiler [http://tensor-compiler.org/](http://tensor-compiler.org/)  is doing something very akin to a query optimizer. Tensors come in  different formats (sparse of different column ordering, dense, low rank,  hierarchical, others undreamed). Transforming between formats has cost.  This is similar to transforming databases to new indices or whether it  makes sense to do a hash join vs a sort join. The columns correspond to indices of tensors.







It is interesting that the standard matrix algebra contains only the composition product. The Meet is another plausible product. In the pointful tensor notation, sometimes we want to 







Standard matrix notation is a point free notation for linear algebra $latex Ax=b$ and $latex X = ABC$ as compared to $latex \sum_j A_{ij} x_j = b_i$ and $latex X_{il} = \sum_{jk} A_{ij} B_{jk} C_{kl} $







Both $latex \sum$ and $latex \exists$ are binding forms that introduce new local dummy variables. You can change the name of a dummy without changing the meaning of an expression (alpha conversion) and you cannot refer to the dummy out of the scope of the binding form. The binding form operator sort of destroys that variable. Other examples of binding forms include integration $latex \int$, $latex \prod$, $latex \max$, $latex \min$, $latex \forall$, and lambda functions $latex \lambda$. 







Considering relations as matrices, this does correspond to a row times column multiplication, e.g. matrix composition.







Relation division is similar in some respects to linear algebraic division. Relations are closer in feel to rectangular matrices rather than square matrices. Rectangular matrices have the notion of a pseudo inverse.







The sparsity pattern of the inverse (although more appropriately the sparsity pattern of the LU decomposition (reified Gaussian elimination) ) is a subject of much interest in sparse linear algebra.







Perhaps somewhat simpler to think about is the low rank decomposition. 







[Query optimization](https://en.wikipedia.org/wiki/Query_optimization) is the process of taking a database query and finding an efficient way to achieve it, both at an abstract logical level (relational algebra manipulations), and at the physical level (What algorithms to use, what indices do you have, other)







When you want to perform the sums in a big tensor algebra expression, it can matter a lot the order in which you do the sum. A bad choice can lead to intermediate data structures that are growing exponentially in size. Sometimes, that is unavoidable, but sometimes it isn't. Another important task is recognizing shared substructure in many expressions. That can avoid duplication of work.







The algebra of relations has a lot of similarity to linear algebra.







A database can be thought of as a big tensor, with a 1 for every entry in the database, and a 0 if it is not. Instead of addition and multiplication, The tensors are combined using boolean algebra. If we consider tensors with only non-negative entries, the connection is even closer. Multiplying two non-negative numbers is the same as an AND if we consider 0 to False and anything non-zero to be True. Sum is the same as an OR in the same manner. If you were interested only in the non-zeroness rather than an actual value, you can shortcut the summation operations as soon as you find a single non zero piece of the sum.







Sufficiently hairy tensor expressions can be more easily understood and mainpulated in a graphical notation. Feynman diagrams for databases. Databases can be represented by vertices of different arity. Different column types are different particles. Graphical notation for relations paper







The relation algebra is a point-free formulation of the calculus of relations. The point-free form of linear algebra is the standard matrix algebra, which does not explicitly state indices. $latex AB$ is the composition of matrices. It feels laborious to convert a tensor expression to a completely point-free style, but I believe it is possible. The trans-untrans operator let's you flip indices from the input to the output of a matrix/relation. The vec operator is a relative of these.  The kronecker product. The Khatri-Rao product as a fan. Despite the 







The Khatri-Rao product is relatively unencountered compared to the Kronecker product. It does make sense for the application of probability however. It is an operation that just doesn't really make sense in the square matrix domain, which is the most familiar. Square matrices are where eigenvalues, inverses, and least squares optimization problems make sense. Where processes do not change their state space. Rectangular are where singular values, and pseudoinverses make sense. This is the difference of taking a Cartesian Category vs a Monoidal one of the Kronecker product







### Relations and Categories: Allegories







Categorical thinking in functional programming brings to mind a certain set of combinators and typeclasses.







pointfree programming brings functional programming into the closest alignment with the ethos of category theory.






    
    <code>id x = x
    f . g = \x -> f (g x)
    fst (a,b) = a
    snd (a,b) = b
    fan f g = \x -> (f x, g x)
    left = Left
    right = Right
    either f g (Left x) = f x
    either f g (Right x) = g x
    curry f = \x y -> f (x,y)
    uncurry f = \(x,y) -> f x y
    dump = const ()
    
    -- absurd, assoc, absorb
    
    -- some useful derive notions
    par f g = \(x,y) -> (f x, g y) -- par f g = fan (f . fst) (g . snd)
    dup x = (x,x) -- dup = fan id id
     -- sometimes you want to take par as more primitive. A discussion for another day</code>







After having defined these, from henceforth we use no more binding forms. No more lambdas.







From this set of combinators, we can describe a significant chunk of all the possiblities of a lambda calculus.







Instead of a pointful lambda calculus DSL with all of the problems of scope and alpha renaming, we can use a point free dsl. There are many options for dsls with binding forms. The simplest may be something like this






    
    <code>data Expr = Lam String Expr | App Expr Expr | Var String
    
    type Name = String
    
    data Exp 
      = Var Name 
      | App Exp Exp
      | Lam Name Exp
      deriving (Eq,Show,Read)</code>







Or you may choose to use HOAS PHOAS or other techniques, or GADTs to track things or go Finally Tagless. https://www.schoolofhaskell.com/user/edwardk/bound







Categorical DSLs have a long history. The Arrow library is the place to find many of the above combinators. 







Conal Elliott has made some waves with his compiling to categoires project, which can be thought of perhaps as a finally tagless interpreter of a categorical DSL, with a GHC plugin compilation stage automatically converting from the pointful lambda calculus to this form.







We can make the initial form of the categorical dsl. The typeclass instances and the interpPF witness the isomorphism between the two representations.







A a [Finally tagless encoding](http://okmij.org/ftp/tagless-final/index.html), there is a function in the typeclass for every constructor of the dsl data type. The dsl becomes very easily extensible. Transformations and programming become mind bending. Pattern matching in the initial form is awesomely powerful and clean. Non fold-like uses of the DSL become awkward (again maybe you get good at it eventually?)






    
    <code>data PF a b where
        Id :: PF a a
        Comp :: PF b c -> PF a b -> PF a c
        Fst :: PF (a,b) a
        Snd :: PF (a,b) b
        Fan :: PF a b -> PF a c -> PF a (b,c)
        Lit :: (a -> b) -> PF a b
        Dump :: PF a ()
        Split :: PF a b -> PF c b -> PF (a :+: c) b
        Lft :: PF a (a :+: b)
        Rgt :: PF b (a :+: b)
    
    interpPF :: (Category k, Cartesian k, Closed k, CoCartesian k ) => PF a b -> k a b
    interp Id = id
    interp (Comp f g) = (interp f) . (interp g)
    interp Fst = fst
    
    instance Category PF where
       id = Id
       f . g = Comp f g
    instance Cartesian PF where
       fst = Fst
       snd = Snd
       fan f g = Fan f g
    instance Closed
    instance CoCartesian PF where
    instance Terminal PF where ?
    
    </code>







One problematic thing about typelevel programming is the lack of first class typelevel functions.  The above point-free dsl lifted to the typelevel is one possible way of getting out of this condundrum







The singletons library deals with this via defunctionalization. There is very exciting work of matchability polymorphism that will greatly enhance how typelevel programming can be done in Haskell. 







Pointfree DSLs lifted to the typelevel via data kinds is another possiblity. It is definitely burdensome in it's own way.






    
    <code>type T1 = 'Comp 'Fst 'Snd
    
    newtype SFun s a b = SFun forall k Catgeory k => k a b 
    data SFun s where
       SFst :: 
    
    
     </code>













Point free programming and finally tagless programming are considered to be somewhat mind bending and difficult. I am unclear if this discomfort will go away with time for everyone. Humans can be trained to familiarity with many things. I have great faith in us. Functional programming itself is often considered in the programming community at large to be difficult and unnatural compared to a trusty for loop. 






    
    <code>liftSet :: [a] -> Rel a a
    liftSet = map dup
    
    leftSet :: Eq a => Rel a b -> [a]
    leftSet = nub . (map fst)
    
    rightSet :: Eq b => Rel a b -> [b]
    rightSet = nub . (map snd)
    
    rtop :: (Enum a, Bounded a, Enum b, Bounded b) => [(a,b)]
    rtop = [(x,y) | x <- enumAll, y <- enumAll]
    
    rbottom = []
    
    rcompose :: Eq b => Rel a b -> Rel b c -> Rel a c
    rcompose xs ys = [ (a,c)  | (a, b) <- xs, (b', c) <- ys, b' == b]
    
    rid :: (Enum a, Bounded a) => Rel a a
    rid = liftSet enumAll
    
    rconverse :: Rel a b -> Rel b a
    rconverse = fmap swap
    
    rmeet :: (Eq a, Eq b) => Rel a b -> Rel a b -> Rel a b
    rmeet xs ys = [x | x <- xs, x `elem` ys]
    
    rjoin :: Rel a b -> Rel a b -> Rel a b
    rjoin = (++)
    
    untrans :: Rel a (b,c) -> Rel (a,b) c
    untrans = map assoc where assoc (x,(y,z)) = ((x,y),z)
    
    
    </code>






    
    <code>rcompose :: Eq b => Rel a b -> Rel b c -> Rel a c
    rcompose xs ys = [ (a,c)  | (a, b) <- xs, (b', c) <- ys, b' == b]
    
    rid :: (Enum a, Bounded a) => Rel a a
    rid = liftSet enumAll
    
    rfan :: Eq a => Rel a b -> Rel a c -> Rel a (b,c) 
    rfan f g = [ (a, (b,c)) | (a,b) <- f, (a',c) <- g, a == a']
    
    rfst :: (Enum a, Bounded a, Enum b, Bounded b) => Rel (a,b) a 
    rfst = rmap fst top
    
    rsnd :: (Enum a, Bounded a, Enum b, Bounded b) => Rel (a,b) b 
    rsnd = rmap snd top
    
    
    rleft = (Enum a, Bounded a) => Rel a (Either a b) 
    rleft = rmap Left top
    
    rright = (Enum a, Bounded a) => Rel a (Either a b) 
    rright = rmap Right top
    
    reither :: Eq a => Rel a c -> Rel b c -> Rel (Either a b) c 
    reither f g = (lmap Left f) ++ (lmap Right g)</code>







### Typeclasses 







Typeclasses are predicates on types. They can also be thought of as roughly sets of types. (Eq a) is the set of all types that support equality operations.







Multiparameter typeclasses allow you to make typeclasses that take more than one parameter. This is the foundation of one style of typelevel hackery, whiere you can use typeclasses as a kind of "typelevel prolog".







### Singletonized Relations







We can take a dependently typed approach to relations. This is very similar to what can be found in the Agda Algebra of Programming library [https://github.com/scmu/aopa](https://github.com/scmu/aopa). The methodology also has a very Profunctor feel. Some of the operations and data types that occur can already be found in the [profunctor package](http://hackage.haskell.org/package/profunctors-5.4). Profunctors are described as a categorical generalization of relations [https://bartoszmilewski.com/2016/07/25/profunctors-as-relations/](https://bartoszmilewski.com/2016/07/25/profunctors-as-relations/) To be honest, I kind of don't get it.







One interesting trick for embedding Set style thinking into relational algebra is the idea to replace any set with a relation that is just two copies of the set. $latex R = {(a,a) | a \in S}$. This is a kind of projection or guard relation. When you compose it with another relation, only those components that are within the guard relation will remain in the result. I think the identity relation specialized to a data type can be called a "doubleton". It is a singletonized data type with two copies of the type parameter.







We can mix and match the relational reasoning and the singleton style reasoning. The relational reasoning operates at a higher level













### Other Interesting Relation Domains







Above I used finite sets as our relations, but there are other interesting relational domains to speak of, and where the lattice character of relations becomes important. Lattices are also important in the subject of abstract interpretation.







For countable infinite sets, lists become plausible but questionable. You will have to ensure that you search through them fairly.







For uncountably infinite sets, a list is a completely unacceptable representation.







LinearRel = Subspaces of (Dsum a b). Can bee specified as the nullspace of a matrix or as the span of a set of vectors.







QuadFun. Composition = minimization. min_x pointful is the binding form. Similar to linearel. 







ConvexRel - ConvexRel are relations that are convex sets when you look at the set valued version of the relation. The Convex Hull of the union is the least upper bound of the union. The intersection is available. Some questions can be phrased as convex programming problems. If so, excellent.







PolyRel is a sub relation of ConvexRel. Now we have the ability to describe polyhedral subsets of the cartesian space. While polyhedra contain an uncountably infinite set, they are basically entirely discrete and combinatorial objects. You can determine many properties of the entire polyhedra by examining only it's finite faces or finite vertices. Two representations of note. The V-Rep and H-Rep. V-Rep gives the vertices of the polytope. All positions in the polytope can be written as a weighted average of the vertices. The H-Rep gives the linear (or affine) inequalities describing the faces. The polytope is understood to be the intersection of the half planes described by these linear inequalities. Some questions are easy, some are hard. high dimensional polytopes can be ridiculously huge if you need to examine the whole thing. Linear Programming is the nice big juicy hammer here is you can use it. Polyhedral computation (cddlib) is the nuclear bomb.







Relations and Dynamical Systems. Relations and Hoare style logic.







OctagonRel and ilk.







IntervalRel is a sub relation of PolyRel. We are only able to describe cartesian products of intervals. Almost has no relational flavor left, because projecting out variables tells us very little about the others. Very amenable to analysis. The finite domains also have a notion of IntervalRel that can be useful. In the context of binary 







SignRel?







LinRel. Linear (or affine which is roughly the same thing) relations. These describe linear subspaces / affine subspaces. Less powerful than PolyRel, distinct from IntervalRel. Can be analyzed via linear algebra techniques (null spaces, svd, gaussian elimination, orthogonalization that sort of thing). Basically is very amenable to analysis. 







All of these can be enhanced by considering finite discrete sets of them.  kD trees for example







Categories are very minimal objects. Galois Connections. Integers and rationals/reals. The floor. Division and subtraction. Integer programming. An abstract thing to talk about is an ordering relations. If this ordering relation has binary operations meet and join that have some of the flavor of intersection/union or AND/OR, then you have enough structure to call it a lattice. Galois Connections are a special kind of relationship between lattices that preserve certain structure. The connection has to play nice with the ordering (monotone). They also have to be nearly an isomorphism in certain ways. The two maps kind of have to be pseudo inverse of each other.  In categorical terms, they are a pair of functors in an adjoint relationship. These gaslis connections are a way of formalizing what you mean by saying one model is an abstraction of the other. For example, Boxes are an abstraction of arbitrary sets. You can abstract a set by giving a bounding box. There is a tightest bounding box. If you can guarantee the bounding box doesn't contain an element with some property, you can actually guarantee the set itself doesn't. It is hopefully much easier to prove things about boxes rather than arbitrary sets, so this can be a huge computational win. $latex \alpha$ Abstraction function takes sets to best bounding box. $latex \gamma$ concretization takes bounding box to largest possible set inside it. In this case, this does very little.  The two directions very often have very different ocmpiutational character. One is "free" and the other "forgets".







Abstraction. Relaxations. Abstract interpetation. Reachability. Abstraction refinement (CEGAR). Nested Quantitifers. Robust control. Hybrid systems. Model Checking.







Loop Unrolling. Bounded Model Checking. Widening? Finite Horizon problems.







Optimization Problems. Dynamic programming. The abstract definition gets you almost nowhere. However sometimes the definition of how you construct possible solutions lies the seeds of finding the actual solution.













Projection. Polyhedral computation. V and H representations







Equality reasoning and inequality reasoning. Inequality reasoning is more complicated, but more powerful. You may not need to examine every case to determine. Indirect equality






    
    <code>newtype FinNat n = FinNat Int deriving Show, Enum, Eq, Ord
    instance KnownNat n => Bounded (FinInt n) where
      minBound = FinNat 0
      maxBound = FinNat (getNum Proxy whatever)
    
    cap :: FinNat n -> FinNat n
    cap z@(FinNat x) | x < 0 = 0
                     | x < n = z
                     | otherwise = n
    instance KnownNat n => Num (FinNat n) where
      (FinNat x) + (FinNat y) = cap (x + y)
      
    type Fifty = FinNat 50
    plus :: Fifty -> Rel Fifty Fifty
    plus x = [(y, x + y) | y <- enumAll ] -- map liftFun (+)
    plusrel :: Rel (Fifty, Fifty) Fifty
    plusrel = liftFun2 (+)
    
    
    data Galois a b c d = Galois {f :: Rel a b -> Rel c d, g :: Rel c d -> Rel a b} -- f X <= Y <-> X <= g Y 
    
    gcompose :: {}
    Galois (compose (plus x)) (rdiv (plus x))
    -- the galois connection from relational composition and division
    gengalois :: Rel a b -> Galois
    gengalois r = Galois (compose r) (rdiv r)
    </code>







Consider a relation case of $latex x y \lte z$ where all the variables are now numbers. We know that we can just divide both sides by y if $y \gte 0$ to get an equivalent statement. But what is x actually? x is sort of the least upper bound. 







One thing that really throws me is that it makes sense to make a distinction between the input and the output of a function. Hence it makes sense to have two distinct spots in a categorical arrow. However, relations have very much a softer qualitative difference between their two sides. Because of trans and untrans, you can flip things between these two positions. The main purpose of the distinction appears to be organizing composition and for eventual lowering to a more constructive functional form.







The concept of least upper bound and greatest lower bound are useful. In Set, it is reasonable to talk about Union and Intersection, but we may want to talk about data structures / relation spaces that are not flexible enough to describe the "exact union". We want an approximation of these operations that is as good as it can be in some sense.







#### Galois Connections







Some other useful things. Division by `X \ rid = X`.  `X \ bottom = top`. `X \ top = bottom`. 



