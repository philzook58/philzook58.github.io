---
author: philzook58
comments: true
date: 2019-08-11 17:54:33+00:00
layout: post
link: https://www.philipzucker.com/cav-2019-notes-probably-nothin-interestin-for-you/
slug: cav-2019-notes-probably-nothin-interestin-for-you
title: 'CAV 2019 Notes: Probably Nothin Interestin'' for You. A bit of noodling with
  Liquid Haskell'
wordpress_id: 2177
categories:
- Formal Methods
- Haskell
---




I went to the opening workshops of CAV 2019 in New York this year (on my own dime mind you!) after getting back from joining Ben on the long trail for a bit. The tutorials on Rosette and Liquid Haskell were really fun. Very interesting technology. Also got some good ramen and mochi pudding, so it's all good. Big Gay Ice Cream was dece.













## Day 1 workshops







Calin Belta [http://sites.bu.edu/hyness/calin/](http://sites.bu.edu/hyness/calin/).Has a new book. Control of Temporal logic systems. Automata. Optimized. Partition space into abstraction. Bisimulation [https://www.springer.com/gp/book/9783319507620](https://www.springer.com/gp/book/9783319507620)







Control Lyapunov Function (CLF) - guarantees you are going where you want to go







Control Barrier Function - Somehow controls regions you don't want to go to.







Lyapunov function based trajectory optimization. You somehow have (Ames 2014) [http://ames.gatech.edu/CLF_QP_ACC_final.pdf](http://ames.gatech.edu/CLF_QP_ACC_final.pdf) Is this it?







Differential flatness , input output linearization







Sadradiini worked there.







Temproal logic with 







#### Rise of Temporal Logic







Linear Temporal Logic vs CTL







Fixpoint logic,







Buchi automata - visit accepting state infinite times







equivalency to first order logic







monadic logic, propositions only take 1 agrument. Decidable. Lowenheim. Quantifier elimination. Bounded Mondel property







Languages: ForSpec, SVA, LDL, PSL, Sugar







Monadic second order logic (MSO).







method of tableau







#### Sadraddini







Polytopic regions. Can push forward the dynmaics around a trajectory and the polytope that you lie in. RRT/LQR polytopic tree. pick random poitn. Run.







Evauating branching heuristics







branch and prune icp. dreal. 







branch and prune. Take set. Propagate constraints until none fire.







branching heuristics on variables







largest first, smearing, lookahead. Try different options see who has the most pruning. Non clear that helped that muhc







QF_NRA. dreal benchmarks.  flyspeck, control, robotics, SMT-lib







[http://capd.sourceforge.net/capdDynSys/docs/html/index.html](http://capd.sourceforge.net/capdDynSys/docs/html/index.html)







#### Rosette







commands: saolver adied programming 







verify - find an input on which the assertions fail. exists x. not safe







debug - Minimal unsat core if you give an unsat query. x=42/\ safe(s,P(x))$ we know thia is unsat because of previous step







solve - exists v si.t safe(v)







synthesis - exists e forall x safe(x,P(x))













define-symbolic, assert, verify, debug, solve, sythesis







Rosette. Alloy is also connected to her. Z Method. Is related to relational logic?







[https://homes.cs.washington.edu/~emina/media/cav19-tutorial/index.html](https://homes.cs.washington.edu/~emina/media/cav19-tutorial/index.html)







[http://emina.github.io/rosette/](http://emina.github.io/rosette/)







Building solver aided programming tool.







symbolic compiler. reduce program all possible paths to a constraint







Cling - symbolic execution engine for llvm







implement intepreter in rosette







Symbolic virtual machine







layering of languages. DSL. library (shallow) embedding. interpreter (deep) embedding.







deep embedding for sythesis. 







I can extract coq to rosette?







how does it work?







reverse and filter keeping only positive queries.







symbolic execution vs bounded model checking







symbolic checks every possible branch of the program. Cost is expoentntial 







CBMC. 







type driven state merging. Merge instances of primitiv types. (like BMC), value types structurally ()







instance Merge Int, Bool, Real -- collect up SMT context







vs. Traversable f => Merge (f c) - do using Traversable







symbolic union a set of guarded values with diskoint guard.







merging union. at most one of any shape. bounded by number of possible shapes.







puts some branching in rosette and some branch (on primitives) in SMT.







symbolic propfiling. Repair the encdoing.







tools people have built.







veify radiation







strategy generation. That's interesting. builds good rewrite rules.







serval. 







certikso komodo keystone. fintie programss







IS rosette going to be useful for my work? coooooould be













### Liquid Haskell







[https://ranjitjhala.github.io/](https://ranjitjhala.github.io/)






    
    
```

{-# LANGUAGE GADTs, DataKinds, PolyKinds #-}
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--ple" @-}

{-@ type TRUE = {v: Bool | v = True }@-}
{-@  type NonEmpty a = {v : [a] | len v > 0}  @-}
{-@ head :: NonEmpty a -> a @-}
head (x : _) = x

{-@ measure f :: Int -> Int @-}
f x = 2 * x

{-@ true :: TRUE @-}
true = True


-- impl x y = x ==> y
-- {-@ congruence :: Int -> Int -> TRUE @-}
-- congruence x y = (x == y) ==> (f x == f y)
-- {-@ (==>) :: {x : Bool |} -> {y : Bool |} -> {z : Bool | z = x ==> y} @-}
-- x ==> y = (not x) || y

-- aws automated reaosning group
{-
nullaway uber. 
sadowski google static anaylis
infer faecobook

give programmer early 


refinement types

why and how to use
how to implement refinement types

mostly like floyd hoare logic

types + predicates = refinement type

t := {x:b | p} erefinemed b
      x : t -> t -- refined function type
linear arithemtic

congruence axioms


emit a bunch of verification conditions (VC)
p1 => p2 => p3 ... 

SMT can tell if VC is alwasy true


-}

{-@ type Zero = {v : Int | v == 0} @-}
{-@ zero :: Zero @-}
zero = (0 :: Int) -- why?


{-@ type NAT = {v: Int | v >= 0} @-}
{-@ nats :: [Nat]  @-}
nats = [0,1,1,1] :: [Int]

{-

subtype

in an environemnt Gamma, t1 is a subtype of t2
x are vairables are in scope.
/\x |- {v | q} <= {v | r}

True  => 


-}


{-@ plus :: x : Int -> y : Int -> {v : Int | v = x + y} @-}
plus :: Int -> Int -> Int
plus x y = x + y

-- measure. uninterpeteyd function called measure.
-- {-@ measure vlen :: Vector a -> Int @-}

-- {-@ at :: vec :Vector a -> {i : Nat | i < vlen vec} ->  @-}

-- {-@  size :: vec : Vector a -> {n : Nat | n == vlen vec} @-}

{-
horn contrints infer 

Collections and Higher and order fucntions

reduce :: (a -> b -> a) -> a -> [b] -> a
type a is an invaraint that holds on initial acc and indictively on f
Huh. That is true.


-- Huh. I could prove sum formulas this way.

sum'' = vec = let is = range 0 (size vec)
              add = \tot i -> ot + at vec i


              properties of data structures


size of of a list
allow uninterpetyed functions inside refinements

{ measre length}

LISTNE a = {v : [a] | 0 < length v}


measure yields refined constructions

[] :: {v : [a] | legnth v = 0}


              --}


              {-

              Q: measure?
              Q : environment?
              Q : where is standard libraru?

              no foralls anywhere? All in decidable fragment


              p : ([a],[a]) | (fst p) + (snd p) == lenght xs
              measures fst and snd


              interpeter

              impossible :: {v : String | false} -> a

imperative language

interpolation


/inlcude folder has prelude

basic values
{v : Int | lo <= v && v < hi }


invaraint properties of structures

encoe invraints in constructor

data OrdPair = OP {opX :: Int, opY :: Int}

{-@ data OrdPair = OP {opX :: Int, opY :: {v : Int | opX < v}@-}


class Liquid Int
class Liquid Bool
class Liquid ... Real?

{-@   @-}

Liquid Relations?
{  }

data OList 
{-@data OList a LB = Empt | :< {oHd :: {v : a | LB = v}   oTl :: OList a oHd }   @-}


{-@   {oHd :: a, oTl :: OList {v : a | oHd < v}   }@-}

GADTs?
-}
data MyList a where
    Nil :: MyList a
    {-@ Cons :: v : a -> MyList {x : a | x < v} ->  MyList a @-}
    Cons :: a -> MyList a -> MyList a

test :: MyList Int
test = Cons 2 (Cons 1 Nil)

{-

abstracting the invaraint from the data structure
parametrzie by relations

data [a]<rel :: a -> a -> Bool> where
    = []
    | (:) {hd :: }

    rel != is unique list

{\x y -> x >= y}
type level lambdas!? .... uh.... maybe.

reflecting singletons into liquid?

termination metrics

/ [length xs + len ys] -- merge sort

{-@ Half a s = }@-}

Oncey ou have temrination proofs you have proofs of correctness

Propositions as Types

Plus commutes is trivial
{n = n + n}

-}


{-@ easyProof :: {True} @-}
easyProof = ()

-- hot damn. I mean this is in it's legerdomain. But prettttty sweet.
{-@ commute :: x : Int -> y : Int -> {x + y = y + x} @-}
commute :: Int -> Int -> ()
commute x y = ()

{-@ reflect mysum @-}
{-@ mysum :: Nat -> Nat @-}
mysum :: Int -> Int
mysum 0 = 0 -- if n <= 0 then 0 else  2 * n + (mysum (n - 1))
mysum n = 2 * n + (mysum (n - 1))

-- what is going on here? why do I need _?
{-@ mysumpf :: _ -> {mysum 0 = 0 } @-}
-- mysumpf :: Proof
mysumpf _ = let x = mysum 0 in x

{-@ mysumpf' :: {mysum 3 = 12 } @-}
-- mysumpf :: Proof
mysumpf' = ()

{-@ reflect fastsum @-}
{-@ fastsum :: Nat -> Nat @-}
fastsum :: Int -> Int
fastsum n = n * (n + 1)

type Proof = ()
{-
{-@ pfsum :: x : Nat -> {fastsum x = mysum x} @-}
pfsum :: Int -> Proof
pfsum 0 = () -- let _ = fastsum 0 in let _ = mysum 0 in ()
pfsum n = pfsum (n-1)  
-}

{-@ pfsum :: x : Nat -> {fastsum x = mysum x} @-}
pfsum :: Int -> Proof
pfsum 0 = () -- let _ = fastsum 0 in let _ = mysum 0 in ()
pfsum n = pfsum (n-1)  

{-

reflection

reflect takes the prcondition of sum and dumps it as the poscondition

sum3 _ = let s0 =sum 0
             s1  = sum 1
             s2  = sum 3 -- all are going to be in scope.
z3 will connect the dots.



using proof combinatos from Proof Combinators
long chains of claculations

reflection of singletons

data SS s where
    {-@ SZero :: {v : Int | v = 0} -> SS 'Zero @-} 
    SZero :: Int -> SS 'Zero 
    {-@ SZero :: {v : Int | v = 0} -> SS 'S a @-} 
    SZero :: Int -> SS 'Zero 





    proof by induction
    sum n = n * (n + 1)/2

    2 * sum n  = n * (n + 1)


point free liquid types

(.) :: (a -> b) -> (a -> )
? Can I abstract over predicates like this?
({v:a | p} -> {s:}) -> 



Vectors

cauchy schwartz



-}

data V2 a = V2 a a 

{-@ reflect dot @-} 
dot (V2 x y) (V2 x' y') = x * x' + y * y'

{-@ reflect vplus @-}
vplus (V2 x y) (V2 x' y') = V2 (x + x') (y + y')

{-@ reflect smul @-}
smul s (V2 x' y') = V2 (s * x') (s * y')
{-
{-@ cauchy :: x : V2 Int -> y : V2 Int -> {(dot x y) * (dot x y) <= (dot x x) * (dot y y) } @-}
cauchy :: V2 Int -> V2 Int -> Proof
cauchy x y = let q = dotpos (vplus x y) in let r = dotpos (vplus x (smul (-1 :: Int) y)) in (\_ _ -> ()) q r
-}

-- {-@ square :: Int -> Nat @-} -- basiclly the same thing
{-@ reflect square @-}
square :: Int -> Int
square x = x * x



{-@ sqpos :: x: Int -> {square x >= 0} @-}
sqpos :: Int -> ()
sqpos x = ()

{-@ dotpos :: x: V2 Int -> {dot x x >= 0} @-}
dotpos :: V2 Int -> ()
dotpos x = ()

{-@ dotsym :: x: V2 Int -> y : V2 Int -> {dot x y = dot y x} @-}
dotsym :: V2 Int -> V2 Int ->  ()
dotsym x y = ()

{-@ vpluscomm :: x: V2 Int -> y : V2 Int -> {vplus x y = vplus y x} @-}
vpluscomm :: V2 Int -> V2 Int ->  ()
vpluscomm x y = ()

{-@ dotlin :: x: V2 Int -> y : V2 Int -> z : V2 Int -> {dot (vplus x y) z = dot x z + dot y z} @-}
dotlin :: V2 Int -> V2 Int ->  V2 Int ->  ()
dotlin x y z = ()





{-

What else is interesting to prove?

verify stuff about ODEs?

fold [1 .. t] where t = 10

could give little spiel about how dynamical systems are like imperative programming



get some rationals.

profunctor
p a b
a -> b are refined functions


I should learn how to abstract over typeclasses. Verified typeclasses?

SMT has built in rationals prob?
-}

data Rat = Rat Int Int 

{-@ reflect rplus @-}
rplus :: Rat -> Rat -> Rat
rplus (Rat x y) (Rat x' y') = Rat (x*y' + x'*y) (y * y')



{-@ reflect rmul @-}
rmul :: Rat -> Rat -> Rat
rmul (Rat x y) (Rat x' y') = Rat (x*x') (y * y')





data Nat' = S Nat' | Z

{-@ measure nlen @-}
{-@ nlen :: Nat' -> Nat @-}
nlen :: Nat' -> Int
nlen Z = 0
nlen (S x) = 1 + (nlen x) 
{-
-- failing?
-- crash: SMTLIB2 respSat = Error "line 31 column 169: unknown sort 'Main.SNat'"
data SNat a where
    SZ :: SNat 'Z
    SS :: SNat x -> SNat ('S x)
-}

{-@ reflect conv @-}
{-@ conv :: x : Nat -> {v : Nat' | nlen v = x} @-}
conv :: Int -> Nat'
conv 0 = Z
conv x = S (conv (x-1))

-- It's an isomorphism

{-@ pfconv :: x : Nat -> {nlen (conv x) = x} @-}
pfconv :: Int -> Proof
pfconv 0 = ()
pfconv x = pfconv (x - 1)

{-@ pfconv' :: x : Nat' -> {conv (nlen x) = x} @-}
pfconv' :: Nat' -> Proof
pfconv' Z = ()
pfconv' (S x) = pfconv' x

{-@ reflect plus' @-}
plus' :: Nat' -> Nat' -> Nat'
plus' Z x = x
plus' (S x) y = S (plus' x y)

{-@ plusz' :: x : Nat' -> {plus' x Z = plus' Z x}  @-}
plusz' :: Nat' -> Proof
plusz' Z = ()
plusz' (S x) = plusz' x


{-@ pluscomm' :: x : Nat' -> y : Nat' -> {plus' x y = plus' y x} / [nlen x, nlen y] @-}
pluscomm' :: Nat' -> Nat' -> Proof
pluscomm' Z y = plusz' y
pluscomm' (S x) (S y) = const (pluscomm' (S x) y) $ const (pluscomm' x (S y)) $  pluscomm' x y
    -- const () $ const (plus' (S x) (S y)) $ const (plus' x (S y)) (plus' x y)

    -- const (pluscomm' (S x) y) $ const (pluscomm' x (S y)) $  pluscomm' x y
 -- flip const is proof combinator .==   
    {-let q = pluscomm' x (S y) in
                        let w = pluscomm' (S x) y in 
                        let r = pluscomm' x y in (\b n m -> ()) q w r -- ? Was this necessary? -}
pluscomm' x Z = plusz' x




-- {-@ data Iso = @-}
data Iso a b = Iso { to :: a -> b, from :: b -> a, p1 :: Proof, p2 :: Proof}


{-

We also have type level lambdas.
refinement polymorphism

LH is somewhat like singletons in the sense there is a manual reflection step.
In singletons the manual reflection is in the Sing type
in LH it is kind of all over the place. (+) has a type. Where is it defined?


How does it know that the Haskell function + is the same as the SMT solver function?

Coq and Agda and Idris type checking is powered quite a bit by an internal unification engine
explicit annotation may lessen the burden somewhat

SMT solvers as a unification engine
structure unification vs uninterpeted functions.
f a ~ Int is not a valid Haskell constraint. Maybe with the unmatchable arrow it is?
In a funny sense, there is a difference between  Just and (+ 1). 
One being a constructor means we can match out of it
Just :: a ->> b
(+ 1) :: Int -> Int

-}

-- test' :: (f a ~ Int) => ()
-- test' = ()
```








Liquid Haskell - What is?







another thing we could do is galois connections between refinements. Pos, Zero, Neg <-> Int







Liquid Haskell uses SMT solvers to resolve it's type checking requirements.







Agda et al also work very much via unification. Unification is a broad term but it's true.







It also has a horn clause solver for inference. Every language needs some kind of inference or you'd go insane. Also it is piggybacking on haskell







It's not as magical as I thought? Like seeing the magicians trick. It really does understand haskell code. Like it isn't interpretting it. When it knows facts about how (+) works, that is because the refined type was put in by hand in the prelude connecting it to SMT facts. What is imported by liquid haskell?







The typing environment is clutch. You need to realize what variables are in scope and what their types are, because that is all the SMT can use to push through type checking requirements.







Installing the stack build worked for me. It takes a while . I couldn't get cabal install to work, because I am not l33t.







Uninterpeted functions. Unmatchability?







It wouldn't be haskell without a bunch of compiler directives. It is somewhat difficult to find in a single cohesive place what all the syntax, and directives are from liquid haskell. Poking around it best. 







  * ple
  * reflection
  * no-termination
  * higherorder - what is this?












[https://github.com/ucsd-progsys/230-wi19-web](https://github.com/ucsd-progsys/230-wi19-web) course notes







[https://github.com/ucsd-progsys/liquid-sf](https://github.com/ucsd-progsys/liquid-sf) some of software foundations







[https://nikivazou.github.io/publications.html](https://nikivazou.github.io/publications.html) niki vazou's pubs. Check out refinement reflection







[https://nikivazou.github.io/static/Haskell17/law-abiding-instances.pdf](https://nikivazou.github.io/static/Haskell17/law-abiding-instances.pdf) draft work? Shows stuff about typeclasses. This is a haskell 2017 paper though







[https://arxiv.org/pdf/1701.03320](https://arxiv.org/pdf/1701.03320) intro to liquid haskell. Interesting to a see a different author's take







[http://goto.ucsd.edu/~nvazou/presentations/](http://goto.ucsd.edu/~nvazou/presentations/) presentations. They are fairly similar to one another.







Liquid haskell gives us the ability to put types on stuff that wasn't possible before.







Linearity :: f :: {a -> b | f (s ^* a) == s ^* (f a) }







Pullback. {(a,b) | f a == g b}







Equalizer







Many things in categoruy theory rely on the exists unique. Do we have functiona extensionality in Liquid haskell?







product : {(a,b) | f q = x, g q = y,  =>   }







Pushing the boundaries on what liquid haskell can do sounds fun. 







Equalizer. The eqaulizer seems prominents in sheaves. Pre-sheaves are basically functors. Sheaves require extra conditions. Restriction maps have to work? Open covers seem important







type Equalizer f g a b = {(e :: a , eq :: a -> b) | f (eq e) = g (eq e) }







I think both the type a and eq are special. e is like an explcit parametrization.  







type Eq f g a = {e :: a | f e = g e} I think this is more in the spirit. Use f and g both as measures.







presheaf is functor. But then sheaf is functor that 







(a, Eq (F a) (G a)). typelevel equalizer? All types a that F and G agree on. 







https://ncatlab.org/nlab/show/equalizer







https://blog.functorial.com/posts/2012-02-19-What-If-Haskell-Had-Equalizers.html







Records are sheaves - Jon Sterling. Records have subtyping. This gives you a toplogy feeling thing.







https://www.slideshare.net/jonsterling/galois-tech-talk-vinyl-records-in-haskell-and-type-theory  








What about purescript records?







{foo | a} {bar | a} -> intersection = {foo bar | b} can inhabit either







union is   
or do you want closed records? union is union of fields. intersection is intersection of fields.







In this case a cover would be a set of records with possibly overlapping fields whose combined labels cover the whle space we want to talk about. consistency condition of sheaf/equalizer is that overlapping records fields have to match. I guess { q.foo = r.foo  } ?There is a way to combine all the stuff up. This is exactly what Ghrist was getting at with tables. Tables with shared columns.







data R1 = R1 {foo :: Int, bar :: Int}







{ (r1 :: R1, r2 :: R2) | (foo r1) = (foo r2) } -- we manitain duplicates across records.







{. }







if you have a "cover" {foo bar |} {bar fred} {gary larry} whose in













[https://www.sciencedirect.com/science/article/pii/S1571066108005264](https://www.sciencedirect.com/science/article/pii/S1571066108005264)







Sheaves. As a model of concurrency? Gaguen paper.







sheaves as constraint satisfcation? sheafifcation. Constraint solving as a way of fusing the local constraints to be globally consistent.







sheaves as records







sheaves as data fusion







[http://www.cs.bham.ac.uk/~mhe/papers/barbados.pdf](http://www.cs.bham.ac.uk/~mhe/papers/barbados.pdf)







Escardo. Compact data types are those finitely searchable







Continuous funcitons are ~computable? Productive?







[http://www.paultaylor.eu/](http://www.paultaylor.eu/)







[http://www.paultaylor.eu/ASD/foufct/](http://www.paultaylor.eu/ASD/foufct/)







[http://www.paultaylor.eu/~pt/prafm/](http://www.paultaylor.eu/~pt/prafm/)







typed recursion theory toplogy







typed computatabiltity theory







Topological notions in computation. Dictionary of terms realted decidable, searchable, semi decidablee







[cs.ioc.ee/ewscs/2012/escardo/slides.pdf](http://cs.ioc.ee/ewscs/2012/escardo/slides.pdf)







[https://en.wikipedia.org/wiki/Computable_topology](https://en.wikipedia.org/wiki/Computable_topology)



















Through NDArray overloading, a significant fragment of numpy code is probably verifiable.







Start with functional arithmetic programs.







Need to inspect function annotations to know how to build input type.  








@verify() tag







Use (Writer a) style monad.  








If statements are branching. We are again approaching inspecting functions via probing. But what if we lazily probe. At every __bool__ point, we run a z3 program to determine if there is an avaiable bool left possible (we don't need to inspect dead code regions. Also would be cool to mention it is a dead region). Curious. We're reflecting via Z3.







Loops present a problem. Fixed loops are fine. but what about loops that depend on the execution? for i in range(n). I guess again we can hack it...? Maybe. range only takes an integer. we don't have overload access.







Maybe we need to go into a full eval loop. utterly deconstructing the function and evaluating it statelemnt by statement.  







(compare :: a -> a -> Comparison). We could select a choice based on if there is a new one avaialable. Requires access to external store. We lose the thread. How can we know a choice was made? How can we know what the choice was? Did it ask var1 or var2? We can probably do it in python via access to a global store. But in haskell?







while loops take invariant annotations. 







It would be cool to have a program that takes 







pre conditions. Post ocnditions, but then also a Parameter keyword to declare const variables as deriveable.  exists parameter. forall x precondition x => post condition.







Parameter could be of a type to take a dsl of reasonable computations. Perhaps with complexity predicates. and then interpretting the parameter defines the computation.







Or simpler case is parameter is an integer. a magic number.












    
    
```



@pre(lambda x: None)
@post(lambda r: r >= 0)
def square(x):
	return x**2

@verify(pre, post) # Easier. because now we can also verify the individual function. Call Z3 at function definition time.
def pre(f,cond):
   if(VERIFCAIOTN_ON)
   return fnew
   def fnew(x):
        if(VERIFICATION_ON):
	   		if(x == VerificationEnv):
	   			newenv = x.copy
	            new.add_pre(cond(x.var))
	            newVar = Z3.variable()
	            newenv.add(newVar == f(x.var))



	        else:
	        	return f(x)



def post(f, cond):
   def fnew(x):
    if x == VerifcationEnv:
        Z3.findmodel(not cond(x.var), x.env)
        if can't find one:
           we're good.
           x.env.append(cond(x.var))
           return x
        else:
           assert(False, model, function name, function postcondition code.)


#overloading assignment. isn't a problem.
class VerifyArray():
   #numpy Z3 shim.

#termination requires measure decreasing at every recursive call.
#arbaitrary loops? How to deal with those?
#maybe a hierarchy of envs to make it easier on z3. Like it doesn't need to give the whole program history if the local use is good enough.



class VerificationEnv():
    self.var = []
    self.pre = []
    self.post = []
```




