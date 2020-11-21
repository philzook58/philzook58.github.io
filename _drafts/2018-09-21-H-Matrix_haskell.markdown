---
author: philzook58
comments: true
date: 2018-09-21 21:05:14+00:00
layout: post
link: https://www.philipzucker.com/?p=1300
published: false
slug: H-Matrix haskell
title: H-Matrix haskell
wordpress_id: 1300
---

data HMatrix =  Dense Matrix | Block HMatrix LowRank LowRank HMatrix
    
    -- implicit contract is that these matrices are skinny and fat
    data LowRank = LowRank Matrix Matrix Matrix -- Hmatrix HMatrix?
    
    
    lrdot :: LowRank LowRank -> 
    lrdot (LowRank a m b) (LowRank c n d) = LowRank a (m*(b * c)*n) d 
    -- multiplication is pretty fast O(Nk^2 (ln N))
    mdot :: HMatrix -> HMatrix -> HMatrix
    mdot (Dense x) (Dense y) = x * y
    mdot (Block a b c d) (Block x y z w) = Block a' b' c' d' 
        where
         a' = (a * b + densify lrdot b ) 
         b' =  dldot a y + 
         c' = 
         d = (  + d * w)
    mdot _ _ = error "H Matrix structure does not match"
    
    
    lrplus :: LowRank -> LowRank -> LowRank 
    lrplus (LowRank a m b) (LowRank c n d) = LowRank (hstack a c) (dsum m n) (vstack b d)
    
    
    lrcompress eps (LowRank a m b) = where
             qa, ra = qr a
             qb, rb = qr (transpose b)
             
    
    
    
    
    
    
    
    -- It is nice to have all these specialized forms that will be type errors if i use the wrong one
    
    lddot :: LowRank -> Matrix -> Matrix
    lddot (LowRank a m b) d = (a * (m  * (b * d)
    
    dldot :: Matrix -> LowRank -> LowRank
    lddot d (LowRank a m b) = LowRank (d * a)  m  b
    
    
    
    densify :: Hmatrix -> Matrix
    densify :: LowRank -> Matrix
    densify (Lowrank a m b) = a * m * b
     
    
    
    






Dead simplest non parametrized HMatrix format.

WHat is H only on one side (the input I guess?

OneSided LowRank = OneSide HMatrix Matrix Matrix

TensorLR = Matrix HTensor Matrix

The goal is kind of a recdution to a small space tensor, i.e. there are small number of kron product summed together. (maybe still expoentially many in dimension)

We'll need to make cuts in index space.

data HMatrix = HMatrix IndexCut HMatrix LowRank LowRank HMatrix



index cut may look like (i > 10 and j < 5)  giving sufficient seperation. (a predicate. Independent boxing of indices is nice.)

Index cut is true or not true to bisect space.

IndexCut, and IndexSeperation. Index seperation is a kron product structure

IndexSplitting = (Set indices, Set indices)

IndexCut = LT String a | GT String a -- Wait. Don't need GT since we do ture and False negation

IndexSet = [Index]

IndexRange = String Int Int -- name upper and lower

data HMatrix = IndexGrouping [HMatrix] [HMatrix]

Things are low rank when they are somewhat independent. remove dimensionality.

Once we have a lone Index we can let one factor be



could we discharge our proof obligations for dimensions with liquid haskell?

Yeah it really feels like HMatrix and BDD are related beasts

Tensor vs Matrix persepctive. In Matrix the is 1 in and one out index



hadamard multiplication - once a splitting contains no shared variables, that side of the splitting stays as is

Alternate taking index restrictions, merge them.

base case of single index split, do dense hadamard on factor and take union of k variables (k variables are implcit summation so we need to foil them)

hadamardmul' | sharedindeces =

| else = Index Split





sum terms

sum indices





type DSum a=  [ a]

data HMatrix = HMatrix (DSum HMatrix) [LowRank]





Compose f f a becomes a different

LowRank f f a = [(f a, f a )]

newtype Matrix ff gg a = Matrix ff (gg a) -- it is just compose

type Matrix = Compose

Compose vs FreeKron

Can we have an automatic differentation that abstracts over k parameter k :: (* -> *) -> (* -> *) -> * -> *

k f g a





Split [Indices] Vector Htensor Vector HTensor

The two vectors are the low rank k index . Indices are the indeices getting clustered into the first HTensor

Split [Indices] HTensor [Indices] HTensor | Cut Index Val HTensor HTensor

Cut is a driect sum of one of the index spaces. It is equivlanet to stack. Split is a kronecker decompositon. We leave the inner k variable unsummed

fuse index index tens =

sum index tens =

swap index index tens =

We can hadamard by Split them independently, then do all fuses.

fuse 3 fuse 1 fuse 0 GGGGG

g xrange yrange = Split g x/2 y/2

HTensorM in out -- in and out are balanced

Two different kinds of kron prod.  kron prod of vector space and kron prod low rankfiying matrix (has to be square matrix.). They can be interleaved

Split [a b] [a b]

LowRank [] []

LowRank |

(A o B) x (A o B)

--  LowRank ::  HTensor -> HTensor -> HTensorM -- no you will never want this

data LowRank = LR (Vec Htensor a) (Vec  Htennor a)

SplitM :: HtensorM [a] - > HTensorM [b] -> HtensorM [a b] -- implicitly balanced

HTensorM has an inverse

inverse SplitM  a b = splitM (inverse a) (inverse b) -- (A x B)^-1 = (A ^-1 x B^-1)

CutM :: HtensorM -> LowRank -> LowRank -> HtensorM   -- implicitly cuts both sides. Hence this is a block matrix. The B and C matrix have to be low rank to maintain invertiblity. No.

-- HStack VStack

Matrices requires Block if you want to invert them.

HTensor N, N is number of indices.

HTensor '[a, b , c] -> HTensor (xs ++ ys)

Split :: [HTensor m] -> [HTesnor n] -> HTensor (n + m)

Cut :: HTensor n -> HTensor n ->



Range

Cube = [Range]

vol :: Cube -> Double

vol xs = foldmap size xs

size :: Range -> Double

size (Range l r) = r - l

distR :: Range -> Range -> Double

distR (Range l1 r1) (Range l2 r2) = | l2 > r1 = l2 -r1

| l1 > r2 = l1 - r2

| otherwise = 0



mindistC2 :: Cube -> Cube -> Double

mindistC2 c1 c2 =  sum $ sq <$>  distR <$>  c1 <*> c2

split :: Range -> Range, Range

split (Range l r) = Range l (l + (r-l)/2), Range (l + (r-l)/2) r



g c1@(x1::x1s) c2@(x2::x2s) = | min vol c1 vol c2 < eps =

| otherwise = Cut r1   (g  x1s ++ r1   )  r2








