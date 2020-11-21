---
author: philzook58
comments: true
date: 2019-05-12 14:39:42+00:00
layout: post
link: https://www.philipzucker.com/?p=1765
published: false
slug: Initial  Final Free Monad Coroutines
title: Initial  Final Free Monad Coroutines
wordpress_id: 1765
---




Freer monads seem closer to my idea of directly reflecting Bind and Pure.








https://markkarpov.com/post/free-monad-considered-harmful.html













    
    <code>data Command = PrintLn String | ReadLine
    type Prog = [Command]
    -- Fine. But what if I wanted to read the line and then print it? Well I'll need variables
    type Var = String
    data Command = PrintVar Var | ReadLine Var | PrintLit String
    type Prog = [Command]
    
    -- ok but what if I wanted to trasnform the string using an embded haskell function?
    data Command = PrintVar Var | ReadLine Var | Transform Var (String -> String) Var | 
    
    Instead of having a seperarte Prog and Command data type, we can merge the two
    data Prog = ReadLine Var Prog | Done | 
    --HOAS style, which kind of sucks. we can embed any transfrom statements inside of the readline.
    data Prog = ReadLine (String -> Prog) | PrintLn String Prog | Done</code>







I was blown away by what I saw in Oleg Kiselyov's tutorial book about MetaOcaml.







I had some confusion on the relation of finally tagless and template Haskell from a cursory reading of Oleg Kiselyov's pages.







It was not entirely clear to me that typed template haskell actually was impelmented and available from the GHC wiki https://ghc.haskell.org/trac/ghc/wiki/TemplateHaskell/Typed







It is however available since GHC 7.8 according to SPJ's slides.







I think the basic claim is that the full unrestricted power of the Q monad (which allows for full IO and GHC introsepction) makes typed template haskell unsound. You get get variables out of their scope. Now this probably won't compile ultimately, but still.







I think for playing around you are unlikely to find those holes.







[http://okmij.org/ftp/tagless-final/index.html](http://okmij.org/ftp/tagless-final/index.html)







[http://mpickering.github.io/posts/2019-02-14-stage-3.html](http://mpickering.github.io/posts/2019-02-14-stage-3.html)







[https://www.google.com/url?sa=t&rct=j&q=&esrc=s&source=web&cd=11&cad=rja&uact=8&ved=2ahUKEwibm_uA2b7gAhWknOAKHdHZBZs4ChAWMAB6BAgGEAI&url=http%3A%2F%2Fweb.cecs.pdx.edu%2F~sheard%2Fcourse%2FAdvancedFP%2Fnotes%2FStagingInHaskell.pdf&usg=AOvVaw3hZogQBrTkRrGmt0bDZ5Ae](https://www.google.com/url?sa=t&rct=j&q=&esrc=s&source=web&cd=11&cad=rja&uact=8&ved=2ahUKEwibm_uA2b7gAhWknOAKHdHZBZs4ChAWMAB6BAgGEAI&url=http%3A%2F%2Fweb.cecs.pdx.edu%2F~sheard%2Fcourse%2FAdvancedFP%2Fnotes%2FStagingInHaskell.pdf&usg=AOvVaw3hZogQBrTkRrGmt0bDZ5Ae)







template Haskell







[https://www.youtube.com/watch?v=AzJVFkm42zM](https://www.youtube.com/watch?v=AzJVFkm42zM)







allows adding gadts type constraints without gadts  

tempate haskell is not type indexed.







template haskell inital encoding  

 = Exp  

AppE  

LamE  

VarE







template haskell final encoding  

lam  

app  

var







interpeter ~ quoting  

stopping interpeter ~ antiquoting







quote ::   

quote ::







unquote







suggestion: try using sum / argmin / others as binding forms in tagless dsl







What makes finally tagless different from just using typeclasses. Maybe just feel?







Num is already a DSL for numbers.







Typeclasses are remarkably powerful. For some reason they are capable of simulating or modelling other powers in haskell.







[https://gist.github.com/danidiaz/36f5647c0968361eedd677ad3870715f#file-dsl-reading-list-md](https://gist.github.com/danidiaz/36f5647c0968361eedd677ad3870715f#file-dsl-reading-list-md)







GADT construction can be simulated by special type specialized smart constructors.







GADT pattern matching can be simulated (is equivalent to) by an eliminator form.







Strings - Butt nasty. getting scope right seems nearly impossible. But is the obvious first approach







De Bruijn - refer to variables by the number of lambdas you have to cross to get to the lambda you want to refer to. Scope basically takes care of itself.







HOAS.  If your main purpose is substitution, you can use the host language syntax as a substitution mechanism. You can always reflect into a first order form







(Expr a -> Expr b) -> Expr (a -> b)







data Expr = Lam (Expr -> Expr) | App Expr Expr







Checkout Phil Freeman's talk https://www.youtube.com/watch?v=8DdyWgRYEeI







PHOAS. 







PHOAS is connected with wanting to keep the recursive  types in the covaraint position of the tyep signatures. This allows you to write the data type as a Fix for recursion schemes,  This is important in Coq so that the thing is inherently terminating.







Kind of a mix. If you keep the type that you'll use to label variables polymorphic, then you can't do anything too goofy. Polymorphism forces functions to be copies, drops, and permutations. a -> a has to be identiy. 







(a,a) -> a has to either be fst or snd







(a,a) -> (a,a) is either id, swap, doubfst, or doubsnd







and so on.







unbound? 







If the type of the variable is polymorphic, it HAS to come from one of your binders.







data Expr var = |Lam var -> (Expr var) | App 







The lam dsl keyword is kind of inconvenient. It would be nice to be able to just compile into it.







Sharing. let expressions have slightly different meaning, implying sharing. We often think of desugaring a let expression to a lambda application. In HOAS the lambda really does have the feel of copying though.













power example













for any ADT you'd write, you can write a typeclas for it.







The typeclass completely reflects the data type definition.







I've seen this before.







In particular with resepct to "Free" instances.







FreeNum. Sometimes I refelct a typeclasses expression into a FreeNum type just so i can manipulate it in a style i'm more used to, or FreeCat.







(2*y) +(2*x) -> 2 * (y + x)







easy enough to see how we might do this in freenum. But how to do it wtuhout that reflection? we need a search procedure.







pow x n is already in the stndard library







http://hackage.haskell.org/package/base-4.12.0.0/docs/src/GHC.Real.html#%5E







It already has some interesting things. pow has been written out explciitly with rewrite rukles for the first couple.







Can we write a Num instance for template haskell to get a staged pow?







An alternaitve that I might attempt is to use a TypeLevel index number







typeclass Pow n where







   pow :: Num a => a -> a  







This would then unroll the pow. How is this different? It is finite recursion. It is not clear that GHC will unroll the regular pow, but this one will unroll. Will the typeclass indreciton go away? 







It would be interesting to actually dump the core for this.







Inlineable. Rewrite rules. specialization.













Rust finally tagless. Mix in with the macros?







Rust doesn't have hkt. type functions must be fully applied. But can we not then apply the same techniques as Haskell's type families, which also must be fully applied? Defunctionalization.







Wait you can't do finally tagless because you need a context? HKT. So maybe a final rep doesn't really help you.  








______













Free Monad like construction







turn functions into data constructors is how you make free things.







Pure :: a -> MyDSL a







Bind :: MyDSL a -> (a -> MyDSL b) -> MyDSL b







Read :: MyDSL String







Print :: String -> MyDSL ()







it's a monad.







Is it a functor? Is it applicative?







We can intepret the program into IO







interp :: MyDSL a -> IO a







interp (Pure a) = return a







interp (Bind x f) = fmap interp ((interp x) >>= (return . f))







interp Read = readLine







interp (Print x) = print x







factor out the common Pure Bind pattern. That becomes the Free monad.







Coroutines are methods are can yield a value but then be resumed (possibly with a new value).







They are generalizations of functions which only return once and generators because they can accept further arguments.







Haskell by default due to the weirdness of lazy evaluation already has what feels like coroutines.







It was a big help to me back at the start of my journey to realize I could replicate Haskell's impossible seeming constructions with python generators. You can build infinite objects in Haskell because they never actually get built until you need them.







A Thunk is a function that you can call with no arguments and it will return a value. It is a way of stalling computation.







Thunks are kind of not a thing in Haskell in the sense that kind of everything is thunk. That is a very confusing sentence. Let me explain.







In other languages there is a distinction between a function that takes no arguments and a value. You still have to call that function getval() in order to transform it into a value. In Haskell there is no function with no arguments. It can ignore the argument but that's not quite exactly the same. So it is subtle and confusing.







fun1 = \_ -> 2







kind of feels like a thunk and it looks like one if you call it with () which makes a programming pun.







fun1()







But still you do have to give it an argument. It is not a no argument function







Trampolining is a sensible thing and mechanism for thunking in languages that have a distinction between no argument function and values. It makes sense that maybe you need to keep evaluating a sequence of no argument functions until you actually get a value.







data Trampoline a = Bounce (Trampoline a) | Pure a







run Bounce x = run x







run Pure x = x







Trampoline is kind of like a Nat where Zero holds a value.







data Nat = Succ Nat | Zero







In fact, Trampoline a is isomorphic to (Nat, a) where the Nat holds the number of Bounces.







Trampoline is kind of silly as is. Values are lazily evaluated anyway so it doesn't really do that.







TrampolineT however still has a purpose in Haskell. You can interleave effects, like writing to the console while trampolining down the thing.







Free Monads and Monad Transformers are talked about as competing approaches to combining different Monads. Maybe you want to do a State-ful computation that Maybe will fail. Or have multiple composable States.







The type Free f a = a + f a + f f a + f f f a + ...







similar to [a]=1+a + aa +aaa+aaaa...







obviously if you apply f f f f to the Free f you still have an element of Free f. That's how the monadic join works.







Codensity - Not clear to me







The Free Monad takes a Functor that looks like the commands you'd want, with a spot for any future commands. It looks like Fix with an extra constructor. It is kind of like an abstract syntax tree of a monadic language that you can write an interpreter for. It is a construction that lifts any functor into a monad structure that loses the least it can. It kind of looks like the data type of List if you squint, and List is a Free Monoid.







data Ignore a = Nothing







isomorphic means that we can go from and to. In Functor terms that means there is a natural isomorphism.







Maybe ~iso~ Free Ignore







Leafy Trees are the Free monad of Pair







It's curious that the Just constructor corresponds to Return







Another interesting example from Stephen Diehl's article is Partiality, = Free Maybe







you give your computation fuel, aka a stack depth







Conal Elliott has a nice lead up on how you can come at Free just from thinking about Trees in his Generic Parallel Algorithms paper.







Monad Transformers are partially applied monad composition for those monads for which it makes sense. Unlike Functor or Applicative, monads do not compose. A monad wrapped in another monad may not still be a monad.







FreeT is the Free Monad Transformer







a consumer is very similar to the trampoline except now during the pause you need to give it a new parameter.







data Consumer m a b= Await (a -> m Consumer a b) | Pure b







Without the monad effect it looks like a multi argument function that takes a possible large number of arguments







data ManyArg a b = AnotherArg a -> (ManyArg a b) | Pure b







ManyArg a b = Free (a ->)







data Free f a = Free f (Free f a) | Pure a







A Producer is just going to be mostly a list







data ManyItems a b = Another a (ManyItems a b) | Pure b







It is tempting to plug a ManyItem right into a ManyArg and so you can.







plug (Another a x) (AnotherArg f) = plug x (f x)







plug _ (Pure y) = y







finally there is the transformer which is a list of functions







data Transformer a c b = Transform (a->c) (Transformer a c b) | Pure b







?data CoTransformer a c b = Transform (a->(c, (Transformer a c b)) | Pure b







?







This list of functions let's us transform a producer term by term







transformManyItem (Another x xs) (Transform f fs) = Another (f x) (transformManyItem xs fs)







But we can unify all of these things into a special case of one big boy.







[https://stackoverflow.com/questions/13352205/what-are-free-monads](https://stackoverflow.com/questions/13352205/what-are-free-monads)







foldMap ~ foldFree







foldMap collapses a structure using a mapping into some monoid object







The inverse of foldMap







invfoldMap :: Monoid m => ([a] -> m) -> a -> m







invfoldMap f = \x -> f [x]







foldFree collapses a structure using a natural transformation from f to a monad m







A list of functors







Question: Is Kmett's Algebra construction an alternative statement of Codensity Monad? The [a]->[a] mentioned is probably Hughes List.







You can fmap then function given then fmap with phi an arbitary number of times.







Refs:







[http://www.edofic.com/posts/2014-04-14-free-coroutines.html](http://www.edofic.com/posts/2014-04-14-free-coroutines.html)







[https://github.com/purescript-contrib/purescript-coroutines](https://github.com/purescript-contrib/purescript-coroutines)







[https://www.schoolofhaskell.com/school/to-infinity-and-beyond/pick-of-the-week/coroutines-for-streaming/part-1-pause-and-resume](https://www.schoolofhaskell.com/school/to-infinity-and-beyond/pick-of-the-week/coroutines-for-streaming/part-1-pause-and-resume)















