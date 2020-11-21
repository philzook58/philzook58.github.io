---
author: philzook58
comments: true
date: 2019-08-11 18:28:34+00:00
layout: post
link: https://www.philipzucker.com/doing-basic-ass-stuff-in-haskell/
slug: doing-basic-ass-stuff-in-haskell
title: Doing Basic Ass Shit in Haskell
wordpress_id: 2111
categories:
- Haskell
tags:
- haskell
---




Haskell has lots of fancy weird corners, but you want to get rippin' and runnin'







The Haskell phrase book is a new useful thingy. Nice and terse.







[https://typeclasses.com/phrasebook](https://typeclasses.com/phrasebook)







This one is also quite good [https://lotz84.github.io/haskellbyexample/](https://lotz84.github.io/haskellbyexample/)







I also like what FP complete is up to. Solid set of useful stuff, although a bit more emphasis towards their solutions than is common [https://haskell.fpcomplete.com/learn](https://haskell.fpcomplete.com/learn)







I was fiddling with making some examples for my friends a while ago, but I think the above do a similar better job.







[https://github.com/philzook58/basic-ass-shit](https://github.com/philzook58/basic-ass-shit)







Highlights include:







Makin a json request






    
    
```haskell

-# LANGUAGE OverloadedStrings, DeriveGeneric #-}
module JsonRequest where

import Data.Aeson
import Network.Wreq
import GHC.Generics
import Control.Lens

data ToDo  = ToDo {
    userId :: Int,
    id :: Int,
    title :: String,
    completed :: Bool
  } deriving (Generic, Show)
instance ToJSON ToDo


instance FromJSON ToDo

my_url = "https://jsonplaceholder.typicode.com/todos/1"

main = do r <- get my_url
          print $ ((decode $ r ^. responseBody) :: Maybe ToDo) -- ((decode $ r ^. responseBody) :: Maybe ToDo)
```








Showing a plot of a sine function






    
    
```haskell

module Plot where

import Graphics.Rendering.Chart.Easy
import Graphics.Rendering.Chart.Backend.Cairo -- Chart-cairo
import Graphics.Image as I -- hip

-- https://github.com/timbod7/haskell-chart/wiki/example-1
filename = "example1_big.png"

main = do 
        toFile def filename $ plot (line "a sine" [[ (x :: Double, sin x) | x <- [0, 0.1 .. 2 * pi]]])
        plotimg <- readImageRGB VU filename -- yeah,I want the plot to pop up
        displayImage plotimg
        print "Press Enter to Quit"
        getLine
```








Doing a least squares fit of some randomly created data






    
    
```haskell

module LeastSquares where

import Numeric.LinearAlgebra

n = 20
x = linspace n (-3,7::Double)
y0 = 3 * x

main = do
        noise <- randn 1 n
        let y = (flatten noise) + y0
        let sampleMatrix = (asColumn x) ||| (konst 1 (n,1))
        let sol = (sampleMatrix <\> y) 
        print $ "Best fit is y = " ++ show (sol ! 0) ++ " * x + " ++ (show (sol ! 1))
```








#### Not too complicated stuff to get you excited about Haskell:







I love Power Serious. [https://www.cs.dartmouth.edu/~doug/powser.html](https://www.cs.dartmouth.edu/~doug/powser.html) Infinite power series using the power of laziness in something like 20 lines







[https://blog.plover.com/prog/haskell/monad-search.html](https://blog.plover.com/prog/haskell/monad-search.html) Using the list monad to solve SEND+MORE=MONEY puzzle.







[http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.42.8903&rep=rep1&type=pdf](http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.42.8903&rep=rep1&type=pdf) Jerzy Karczmarczuk doing automatic differentiation in Haskell before it was cool. Check out Conal Elliott's stuff after.







Very simple symbolic differentiation example. When I saw this in SICP for the first time, I crapped my pants.






    
    
```haskell

data Expr = X | Plus Expr Expr | Times Expr Expr | Const Double
deriv :: Expr -> Expr
deriv X = Const 1
deriv (Const _) = Const 0
deriv (Plus x y) = Plus (deriv x) (deriv y)
deriv (Times x y) = (Times (deriv x) y) `Plus` (Times x (deriv y))
```








[https://www.cs.kent.ac.uk/people/staff/dat/miranda/whyfp90.pdf](https://www.cs.kent.ac.uk/people/staff/dat/miranda/whyfp90.pdf) Why functional Programming Matters by John Hughes







[https://www.cs.cmu.edu/~crary/819-f09/Backus78.pdf](https://www.cs.cmu.edu/~crary/819-f09/Backus78.pdf) John Backus emphasizing escaping the imperative mindset in his 1978 Turing Award speech. A call to arms of functional programming







[https://www.cs.tufts.edu/~nr/cs257/archive/richard-bird/sudoku.pdf](https://www.cs.tufts.edu/~nr/cs257/archive/richard-bird/sudoku.pdf) Richard Bird defining sudoku solutions and then using equation reasoning to build a more efficient solver







[https://wiki.haskell.org/Research_papers/Functional_pearls](https://wiki.haskell.org/Research_papers/Functional_pearls) - Functional Pearls







#### Here's how I find useful Haskell packages:







I google. I go to hackage (if I'm in a subpage, click on "contents" in the upper right hand corner). Click on a category that seems reasonable (like "web" or something) and then sort by Downloads (DL). This at least tells me what is popular-ish. I look for tutorials if I can find them. Sometimes there is a very useful getting started snippet in the main subfile itself. Some packages are overwhelming, others aren't.







The Real World Haskell book is kind of intimidating although a lovely resource.







The wiki has a pretty rockin set of tutorials. Has some kind soul been improving it?







[https://wiki.haskell.org/Category:Tutorials](https://wiki.haskell.org/Category:Tutorials)







I forgot learn you a Haskell has a chapter on basic io







[http://learnyouahaskell.com/input-and-output](http://learnyouahaskell.com/input-and-output)







#### Learn more







When you're ready to sit down with Haskell more, the best intro is currently the [Haskell Book](http://haskellbook.com/)







You may also be interested in [https://www.edx.org/course/introduction-functional-programming-delftx-fp101x-0](https://www.edx.org/course/introduction-functional-programming-delftx-fp101x-0) this MOOC







[https://github.com/data61/fp-course](https://github.com/data61/fp-course) or this Data61 course







Then there is a _fun_ infinitude of things to learn after that.







______







More ideas for simple examples?







This post is intentionally terse.







IO is total infective poison.







standard output io






    
    
```haskell

main = do
      x <- getStrLn
      putStrLn "Hello"
      print [1,2,3]
      print (Just 19022.32)
      print x


```








mutation & loops. You probably don't want these. They are not idiomatic Haskell, and you may be losing out on some of the best lessons Haskell has to offer.













file IO







web requests







[http://www.serpentine.com/wreq/tutorial.html](http://www.serpentine.com/wreq/tutorial.html)







web serving - scotty







image processing







basic data structures







command line arguments







plotting







Parallelism and Concurrency







[https://nokomprendo.frama.io/tuto_fonctionnel/posts/tuto_fonctionnel_25/2018-08-25-en-README.html](https://nokomprendo.frama.io/tuto_fonctionnel/posts/tuto_fonctionnel_25/2018-08-25-en-README.html)



