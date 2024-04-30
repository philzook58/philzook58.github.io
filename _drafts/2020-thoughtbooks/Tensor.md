### Tensors and Functional Functional Differentiation

## Binding Forms
There is a notational pattern that appears over math and physics. It is convenient to introduce new bound variable names, or dummy indices attached to a kind of operator. These names do not intrinsically mean anything and they can be freely changed to anything, so long as you change them anywhere. This process is called alpha renaming, or dummy index renaming.

Examples:
    - \lambda i - The lambda binder. Introduces a new variable for the purposes of substitution
    - `let i = _ in` - The let binder. Related but slightly different from the lambda.
    - \forall i - Forall quantifier for logical formula
    - \exists i - Exists quantifier for logical formula
    - \sigma_i - Summation symbol
    - \int di  - integration symbol
    - \prod_i - Product symbol
    - \max_i  - maximization operator
    - \union_i
    - \meet

Similarly but slightly less commonly are search operators.
    - argmax_i - 
    - \mu - 
    - \epsilon - Hilbert's choose operator

Read more about this in this Jules Hedges paper, which is referencing earlier work by Escardo and Oliva, 

Summation is a binding form that is interesting from many angles.
 - Useful. Automatic differentiation. Numerical computing
 - Simpler in many sense that lambda calulus
 - More familiar (to me). Summation is an old friend.

History: Is summation the first binding form. Binding has it's analogs in pure liguisitcs and has been with us since prehistory. The greek logicians ,but to my knowledge probably did not use symbolism.

Why :
 1. Functions are the most syntactically lightweight thing in haskell
 2. We can make a dsl that looks pretty close to natural notation
 3. Functions are the most primitive construct or a functional programming language. The type level language is also mostlye functional and we're going up there.

Random though. The derivative operation is kind of dual to some of the operations above like sum. deriv :: b -> (i -> b) is at least type-wise a flip to sum :: (i -> b) -> b. And operationally it is also, not an inverse, but something not unlike an inverse.

There is an interesting way to look at these, as higher order functions.
To me and my background, I consider the \sum symbol to be the simplest and most intuitive of these forms.

In the haskell prelude 
sum :: [a] -> a

But I would like to instead work with
sum :: BEnum i => (i -> a) -> a
sum f = sum $ [f i | i <- enumAll ]

This is a form of HOAS.

Some of the techniques used to descibe lambda calculus are useful for general purpose binding forms, and not dependent on the substitution mechanism implied by the lambda binder.
A lot of the pain of implementing the lambda calculus is maintaining the correctness of your dummy variables under the substitution mechanism. It is possible to get accidental clashes of the dummy names

There to my knowledge are 4 main classes of techniques
 - Do the dumbest thing you can do. Just write the shit out. Use strings or ids as your dummy variables. For the record, DTDYCD is actually a positive in my book. It means it is simple to explain, and probably the first thing you should try.
 - HOAS/PHOAS - Higher Order Abstract Syntax (HOAS) abuses the fact that your functional programming language already has lambda binders, so the compiler authors already wrote perfectly good alpha renaming and substition code. PHOAS (Phantom HOAS) carries around . See Freeman's talk.
 - de Bruijn Indices - de Bruijn indices count how many binding forms to back jump over to get to the one you care about. By using this mechanism, you give a name that actually has meaning to the sites where dummy variables are used.
 - Pointfree / Indexfree - Combinator Calculi, Categorical abstractions, and algerba of programming style are styles of programming / compilation targets that express lambda calculus. It is generally considered more elegant to perform tensor calculation in an index-free style. Index-free structure can be constrained more easily to only forms that make sense. Some algebraic manipulations are easier and some are harder in indexfree style. I personally get the sense that if I don't know how to express the problem index free, I may have no idea what I'm talking about.

In Haskell, there are a couple different options
locally nameless - http://www.strictlypositive.org/notanum.ps.gz
unbound
bound - <a href="https://www.schoolofhaskell.com/user/edwardk/bound">https://www.schoolofhaskell.com/user/edwardk/bound</a>
https://www.schoolofhaskell.com/user/edwardk/phoas
http://dev.stephendiehl.com/fun/evaluation.html

https://www.youtube.com/watch?v=8DdyWgRYEeI
https://github.com/paf31/haskell-slides/tree/master/hoas

http://okmij.org/ftp/tagless-final/


## Summation

Let's walk before we run. I think it is fairly intuitive that you might have a function,
 say `f n = n * n` that we want to sum from n = 1 to n = 10. \sum_{n=1}^{10} f(n)

sum :: Int -> Int -> (Int -> Int) -> Int
sum lower upper f = sum [f n | <- [lower .. upper]]

1. It sucks to have everything be an Int
2. It is annoying (although sometimes important) to have to pass the lower and upper bounded parameters. Let's make them implciit

sum :: (BEnum i, Num a) => (i -> a) -> a

-- or we can make a bounded instance for Int, just for this post.
instance (Bounded Int) where
   maxBound = 100 -- sry not sry.
   minBound = 0

sum @(Fin 10) (\(Fin x) -> x * x)

newtype Fin n = Fin Int
instance Enum (Range n) where
instance Bounded

The simplest 

We can easily write nested summations

curried form
sum (\i -> sum \j -> i * j) ==
sum (\i -> i) * sum (\j -> j)

instance Bounded a, Enum b => Enum (a,b)
instance Bounded a, Bounded b => Bounded (a,b)
instance Bounded a, Bounded b => Bounded (a,b,c)
instance Bounded a, Bounded b => Bounded (a,b,c) -- and so on

uncurried form
sum (\(i,j) -> i * j)

quickcheck 
-- geometric series
-- a couple bernoulli series
-- maybe a binomial expansion?
-- look in knuth
sum id == n * (n - 1) / 2
sum (\x -> x ^ i) = (x^n - 1) / (1 - x)
sum \i -> (choose n i) x ^ i = (1 + x)^n


The implcit form becomes more useful when we turn our focus to tensor expressions.

Kronecker delta tensor

delta :: (Eq i, Num a) => i -> i -> a
delta i j | i == j    = 1
          | otherwise = 0

data I3 = X | Y | Z
levi-civitia symbol in 3d
eps3 i j k |i == j || j == k || i == k = 0
           | i < j `xor` j < k         = 1
           | otherwise =                -1 

cross :: (I3 -> a) -> (I3 -> a) -> (I3 -> a)
cross v w = \k -> sum \(i,j) -> (eps3 i j k) * (v i) * (w j)

quickcheck (some identites on levi civita)
\(i,j,k) -> sum \k -> (eps3 i j k) * (eps) 
== \(i, j) -> sum \ delta delta


eps2 :: Num b => Bool -> Bool -> b
eps2 i j | i < k = 1
         | i > k = -1
         | otherwise = 0           


sym :: (a -> a -> b) -> (a -> a -> b)
sym t = \i j -> (t i j + t j i) / 2

asym :: (a -> a -> b) -> (a -> a -> b)
asym t = \i j -> (t i j - t j i) / 2

The form above I think it fairly natural. However if we want to differentiate the expressions, it just doesn't work?
We want a DSL to express the expressions.


## Final form. DSLs for numbers.

For every data type, we can express it in final form as a typeclass.
For every typeclass, we can freeze it out as a "free" data type.

I think this correspondence is made more clear by tranferring to GADT notation for deifning data types. This syntax makes the type signatures of the data constructors more clear. It also brings the data defintiion into a `where` block which looks syntactically very similar to a `instance` typeclass declaration

```haskell
data FNum where
  Plus :: FNum -> FNum -> FNum
  Times :: FNum -> FNum -> FNum
  Negate :: FNum -> FNum
  FromInteger :: Int -> FNum

-- one direction of the isomorphism
instance Num FNum where
  (+) = Plus
  (*) = Times
  negate = Negate

-- the other direction
interp :: Num a => FNum -> a
interp (Plus x y) = (interp x) + (interp y)
interp (Times x y) = (interp x) * (interp y)
interp (Negate x) = negate (interp x)
```


## Simple differentiation

In order to perform differention, we need to be talking about numerical functions, not numbers. In order to do that, the simplest thing is to add another constructor x

The simplest data type that can express a numerical concaluation is.

```haskell 
data E = X | Sum E E | Prod E E | Lit Double

-- final form
class HasVar a where
  var :: a
```

This data type basically corresponds to polynomials over a single variable x.


instance Num E where
   x + y = Sum x y
   x * y = Prod x y
   fromInteger n = Lit (fromInteger n)
   abs = error "nah"
   signum = error "nah"
   negate x = (Lit -1) * x

diff :: E -> E
diff X = Lit 1
diff (Sum x y) = (diff x) + (diff y)
diff (Prod x y) = (diff x) * y + x * (diff y) 
diff (Lit _) = Lit 0

interp :: E -> (Double -> Double)
interp X x = x
interp (Lit l) _ = l
interp (Sum x y) = (interp x) + (interp y)
interp (Prod x y) = (interp x) * (interp y)  



## Automatic Differenation
Symbolic and Numerical computation
One is slow, the other fast.
Symbolic operates on ASTs.
Why do symbolic differentiation when we can do automatic differentiation for symbolic data types? 
The compiler is a powerful symbolic manipulation engine. Ausotmatic differentiation uses your compiler.
The line between automatic and symbolic differentiation is blurry.
Automatic differenation is a numerical process and symbolic is a cymbolic one.
However, numerics are basically don in terms of doubles, which is a bizarre standard of bits besigned into your cpu with fast hardware acceleration.


Automatic differentation is to symbolic diff as final is to initial

## Feynamn diagrams

Overloading the dsl can output graphviz files.
Feynman diagrams vs Penrose notation vs Goldstone diagrams. Topological only.
The T ordering trick.

## Multiple Variables




## Introducting

## To Curry or not to Curry. 
Me dunno



## Further Thoughts

- Hash Consing - Recollection of common terms is an important operations. This takes place both in noticing symmettries of Feynman graphs, and in recollecting subparts of graphs for the vague purposes of partial summation and "renormalization". In particular, any subparts that can be thought of as a geometric series are resummable. The closed form of the geometric series involes onlys summation, multiplication and inversion, all of which are efficient matrix operations.
- Chebfun - There is a delightful set of packages called Chebfun. It turns out that Chebyshev interpolation (where you use chebyshev polynomials to interpolate samples) is absolutely phenomenoal. A function (a -> b) is a value that has only 1 thing you can do with it: sample/apply it. Most ordinary functions can be approximated to machine accuracy with a fairly small number of sample (~100). When you call `sin` on your machine, it is not the platonic mathematical `sin`. It is being calculated htrough some procedure, and Chebyshev interpolation isn't the craziest method in the world, specially if you had to pick 1 method rather than specialzied ones.
- Optimizations. Fusing deltas, etc. Staged Interpreter for optimizations. Rewrite rules. 

### TRASH

To use Kemtt's ad, we need to give it (i -> a) -> (i -> a) an explicit functional form

Overloading function application - McBride's idiom brackets are the Haskelly way. C++ and Rust closures are a defunctionalization trasnformation to objects.


Vice versa, we can make a typeclass for something normally thought of as a data type
Maybe this is out of scope
```haskell

class List f where
   nil :: f a
   cons :: a -> f a -> f a
instance List [] where
  nil = []
  cons = (:)
interp :: List f => [a] -> f a
interp (x : xs) = cons x (interp xs)
interp [] = nil


-- Hughes list
instance List ([a] -> [a]) where
  nil = const []
  cons x xs = \ys -> x : (xs ys)

```


----

simple tensor expressions
sum' :: (BEnum a, Num b) => a -> b
sum' f = sum $ map f [minBound .. maxBound]

instance Num a => Num (b -> a) where

data I3 = X | Y | Z

delta i j | i == j    = 1
          | otherwise = 0

eps3 i j k |i == j || j == k || i == k = 0
           | i < j `xor` j < k         = 1
           | otherwise =                -1 
           
eps2 :: Num b => Bool -> Bool -> b
eps2 i j | i < k = 1
         | i > k = -1
         | otherwise = 0           


sym :: (a -> a -> b) -> (a -> a -> b)
sym t = \i j -> (t i j + t j i) / 2

asym :: (a -> a -> b) -> (a -> a -> b)
asym t = \i j -> (t i j - t j i) / 2

wedge

-- SR metric
g i j | i == 0 && j == 0 = -1
      | i == j = 1
      | otherwise = 0

dual :: BEnum b => b -> b -> b 
dual 

cross v w = sum [i,j] ((eps3 i j k) * (v i) * (w j))
cross (cross v w) u == 

dot v u = sum [i] ((v i) * (u i))

pathintegral j = exp $ integrrate \k -> integrate \i -> (j i) * (G i k) * (j k) 


https://stackoverflow.com/questions/26515102/making-numeric-functions-an-instance-of-num
https://wiki.haskell.org/Num_instance_for_functions
Pshah. Whatever, LOSERS.

data TExpr = Sum \ind -> 

interp :: TExpr ind -> (ind -> a) -> a
interp (V i) v = v i
interp (Sum f) v = sum (map (interp v . f)  [minBound .. maxBound]
interp (Prod x y) v = (interp v x)


a ~ DualNum Double ===> 


Traversable (ind ->)


diff j (Sum f) = Sum (j -> diff (f j)) 
diff j (J i)   = J i
diff j (prod   =

diff :: TExpr -> (ind -> TExpr)
diff (Sum f) j = diff (f j) j + (Sum \i -> (diff (f i) j)
diff (J i) j | i == j = 1
             | otherwise = 0

diff (Exp x) j = (diff x j) * (Exp x)

diff . diff . diff . diff

de bruijn indices

data TExpr = J Int | Sum TExpr | Prod | Plus | Let TExpr TExpr | LVar Int

Let allows sharing.


-----
I really like the algebra example, but I should just pump out a post on the point free lambda GADT. That is simple and interesting

The simplest lambda calculus syntax DSL looks like this


Running this lambda calculus requires somehow dealing with the variables.

In addition, named variable style DSLs require you to buy in whole hog . They aren't very naturally correct. When you interpret or manipulate them you need to think a bit about scoping, alpha renaming, and other issues. You can't refer to variables outside it's scope. Perhaps you are interested in making a fancy lambda calculus with like linear lambda calculus where you have to use a variable exactly once. In order to ,make these things happen, you have to check them. You need to get the cat back in the bag.


Categorical/Point Free DSLs let you more easily buy into power when you want it, piecemeal. They don't have any binding forms and are more easily manipulated.


Conal Elliott has been pushing categorical DSLs in his Compiling to Categories work. He has been focused on final encodings of these DSLs using .a standard set of categorical typeclasses. Final encodings have phenomenal properties, but are not the easiest to use or understand for some reason. It is more familiar to use a data type to represent a DSL.

I think point-free programming is not always that much worse than pointful programming from an ergonomics perspective. But I do think it is less readable and very foreign for some. And the pipework required is painfully explicit, when a named variable let's you implicilty teleport variables around. Perhaps a good approach would be to give a pointful surface syntax for users and immediately transform it into an internal point-free form. Performing manipulations on point-free representations is SO much better.

It is well known that Simply Typed Lambda Calculus is roughly or exactly a Cartesian Closed Category. 

I give hesitation on adding the Closed property to the DSL. This adds closures to your language, which are useful but again you've perhaps added too much power.


Recursion schemes to my knowledge are basically a necessity for point-free programming.

Many DSLs require named variables, for example a DSL with a summation form.


<!-- wp:code -->
<pre class="wp-block-code"><code>-- The most basic expression
data Expr = Add Expr Expr | Mul Expr Expr | Lit Int

runExpr (Add a b) = (runExpr a) + (runExpr b)

-- rewrite rules
dist (Mul (Add x y) z) = rule $ (Mul x z) `Add` (Mul y z)

-- either let the rule match or return same result?
-- convert io exception to EitherT?
rule f x = unsafePerformIO $ catches (Just $ f x) [Handle \PatternMatchFail _ -> Nothing]
-- or use a template haskell quasiquoter section
[$rule
dist
yada yada
]
 


data ExprF a = Add a a | Mul a a | Lit Int
type Expr = Fix ExprF
alg (Add x y) = x + y
interp = cata alg

--  The simplest boy
data Expr  = Add Expr Expr | Var String | Mull Expr Expr | Lit Int
interp env (Var x) = lookup x env 
data ExprHOAS = Add Expr Expr | Lam (Expr -> Expr) | Mul Expr Expr | Lit Int
data ExprPHOAS v = Add (Expr v) (Expr v) | Lam (v -> Expr v) | Var v | Lit Int -- Why lam? It's not particularly right to add functions together

data ExprHOAS = Add Expr Expr | Sum (Expr -> Expr) | Mul Expr Expr | Lit Int
data ExprPHOAS v = Add (Expr v) (Expr v) | Sum (v -> Expr v) | Var v | Lit Int
data ExprBruijn = 

-- uncurry all contrusctors. Suppose you had to build data types in a point free style. replace (->) with CatExpr. Make type correct wtih GADT.
-- free variables appear in the input. We pick them by position via Fst/Snd. 
data Expr
data ExprCat where
  Add :: ExprCat (Expr,Expr) Expr -- make each constructor a gadt of same type --
  Lit :: ExprCat Int Expr 
  LitInt :: Int -> ExprCat a Int -- inject any literals that may appear (anywhere)
  Compose :: ExprCat b c -> ExprCat a b -> ExprCat a c
  Id :: 

  Fan ::
  Fst ::
  Snd ::
  Sum :: CatExpr (a,b) (a,b) -> CatExpr b (Expr, b)
  Sum :: CatExpr (a,b) c -> CatExpr b c 
  Var? -- no var. we're point free
-- a refacotring kind of like Fix. But not in the sense that we're allow recursive data scruture
FreeCat f a b where
  Compose
  Id 
  Lift :: f a b -> FreeCat f a b
Add (Lit 1) (Lit 2) -> Compose Add (Fan (Lit 1) (Lit 2)) :: ExprCat a Expr
Add (Var "a") (Var "b") ~~ Add :: (Expr,Expr) Expr
Add (Var "a") (Var "a") ~~ Add . dup -- dup = Fan Id Id
Sum \x -> x ~ Fst . Sum Id
add ~ Compose Add Dup
What does an expression with no free variables look like?
ExprCat a Expr   

Hadamard -- Meet
Add -- Join
MatMul -- Compose
Div -- Inverse.
Id -- identity matrix
KRProd -- partial kron, partial  == Fan
Kron -- Par = Fst Snd KRProd . What are Fst Snd? A partial trace? While these may be identities in the bool version, they aren't linearly. Maybe if considered homogenously? Or if working with probability, trace = 1.
Transpose -- Converse
Trans --
UnTrans -- moving things between input and output
Trace -- ? == Compose (Trans Id)
Scalar Double -> Tensor () ()
vec :: Tensor a b -> Tensor () (a,b)</code></pre>
<!-- /wp:code -->


<a href="https://www.schoolofhaskell.com/user/edwardk/bound">https://www.schoolofhaskell.com/user/edwardk/bound</a>



Ed Kmett on bound, his library



First Order Syntax.



HOAS



de Bruijn



PHOAS



Whatever locally nameless is

"Tutorials " on writing depdnetly typed languages

Simply Easy by McBride and co

Mini-TT

Andrej Bauer - http://math.andrej.com/2012/11/08/how-to-implement-dependent-type-theory-i/

<a href="https://github.com/sweirich/pi-forall">https://github.com/sweirich/pi-forall</a>

Point-Free Languages<br>