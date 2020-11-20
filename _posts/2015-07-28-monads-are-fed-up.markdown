---
author: philzook58
comments: true
date: 2015-07-28 18:36:43+00:00
layout: post
link: https://www.philipzucker.com/monads-are-fed-up/
slug: monads-are-fed-up
title: Monads are f'ed up
wordpress_id: 77
---

Coming back from a couple weeks off of not reading about them, I find myself mystified once again.

I think they are a way to chain extra data through functions.

And you need them to make basic ghc programs? That sucks.

getArgs gets the command line arguments in a list of strings

getLine takes a string from the program

read converts strings into integers that can be added

foldr1 is a variant on foldr that takes the first element as the first accumulator value

putStrLn

putting stuff on seperate lines in a do block implies >>

>>= is implied by <- notation

Both are bind operations but a little different?

It all kind of does what you think it should from looking at it, but the monadic backend is deeply puzzling (look at the type definitions). I watched a youtube video of Brian something explaining how monads are a natural way of achieving function composition for functions that don't take in and output the same type, but I can't really recall how that made so much sense. Monads are slippery

`save this is a file hello.hs and run`

`ghc hello.hs`

`./hello`

`
module Main where
import System.Environment
main :: IO ()
main = do
args <- getArgs
num <- getLine
putStrLn ("Hello, " ++ show (foldr1 (+) (map read args)))
putStrLn num
`
