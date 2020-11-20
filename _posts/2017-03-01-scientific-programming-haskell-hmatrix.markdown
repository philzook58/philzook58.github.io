---
author: philzook58
comments: true
date: 2017-03-01 21:59:04+00:00
layout: post
link: https://www.philipzucker.com/scientific-programming-haskell-hmatrix/
slug: scientific-programming-haskell-hmatrix
title: Scientific Programming in Haskell with hmatrix
wordpress_id: 671
---

I've been puttering around with some ideas about how linear algebra could work in Haskell.

So I decided to check out what has been done. hmatrix binds to the gnu scientific libraries and lapack.

There is also htensor and repa which I need to check out.

This is the hello word of scientific programs. I could write this is numpy, scipy, matplotlib FAST. But I'm super used to those. Maybe not a fair comparison.

I build a circulant function for the 1d periodic Laplace equation matrix. I did not find good constructors that would elegantly construct the thing so I make a circulant routine using the fft. That's ok I guess.

I got the eigenvalues and eigenvectors with eigSH.

Then I plot it out to an external svg file using Cairo. I do not like the mental overhead of a monad.But I guess you can just copy and paste and ignore all that.

The Plt.line function takes a label and a list of (x,y) tuples

    
    runghc hello_laplace.hs




    
    -- runghc Laplace.hs
    
    import Numeric.GSL.Fourier
    import Numeric.LinearAlgebra
    import Data.Complex
    
    -- Some of the namespace crashes with the algebra stuff.
    import qualified Graphics.Rendering.Chart.Easy as Plt
    import Graphics.Rendering.Chart.Backend.Diagrams(toFile)
    
    fftRow m = fromRows $ (map fft) $ toRows m
    fftCol m = fromColumns $ (map fft) $ toColumns m
    
    
    ifftRow :: Matrix (Complex Double) -> Matrix (Complex Double)
    ifftRow m = fromRows $ (map ifft) $ toRows m
    ifftCol m = fromColumns $ (map ifft) $ toColumns m
    
    
    circulant :: Vector (Complex Double) -> Matrix (Complex Double)
    circulant v = ifftCol $ fftRow $ diag $ fft v
    
    {-
    -- nevermind
    rotate :: Int -> [a] -> [a]
    rotate _ [] = []
    rotate n xs = zipWith const (drop n (cycle xs)) xs
    -}
    
    
    
    
    num = 20
    
    c = assoc num 0 [(0,-2),(1,1),(num-1,1)] :: Vector C
    kmat = circulant c
    
    sol = eigSH (trustSym kmat)
    -- doesn't check hermiticty
    --sol = eigSH' kmat
    eigvals = fst sol
    
    -- a plotting function
    signal :: [Int] -> [(Double,Double)]
    signal xs = [ (fromIntegral x, realPart $ (c ! x)  )| x <- xs ]
    
    
    pltVec label v = (Plt.line label [zip [0..] (toList v)])
    
    main = toFile Plt.def "example1_big.svg" $ do
          Plt.plot (Plt.line "Matrix Row" [signal [0..(num-1)]])
          Plt.plot (pltVec "eigenvalues" eigvals)


Ok. Actually on reflection it's not bad. Scratching my head around the circulant matrix constructor took some time. And so did installing stuff. I did also keep slamming into type mismatches. and it didn't like eigSH' which I don't get.

Maybe Haskell for Mac would work well here? I did buy a copy.

Maybe Julia would be better? I think Julia has lots of functional and pythony things.

I should refactor the fftRow stuff into a higher order combinator that maps into rows and columns



    
    mapRow f m = fromRows $ (map f) $ toRows m







