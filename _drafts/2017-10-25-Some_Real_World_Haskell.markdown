---
author: philzook58
comments: true
date: 2017-10-25 20:19:27+00:00
layout: post
link: https://www.philipzucker.com/?p=905
published: false
slug: Some Real World Haskell
title: Some Real World Haskell
wordpress_id: 905
---

HSpec - For unit testing haskell code. Used in conjunction with quickcheck

Hlint - checks for style in haskell code

stack - haskell installation manager. A different use case than cabal. Tends to make local ghc and local packages to more tightly control stuff.

stack ghc

stack ghci

stack install

stack exec

stack setup

Servant - A Haskell API builder. Uses funky type level technology, but that doesn't matter that much in that you almost certainly don't need to deeply understand that stuff to use it.

https://www.youtube.com/watch?v=19HTfXFmwvA

So you make api endpoints in an api datatype

:> happy bird is basically like slashes

:<|> yell bird combines different endpoints into a single api

Last thing is usually a request type, a type level list of possible requests, and the data type

Get '[Json] User

you can usually automatically generate toJSON and fromJSON for datatypes. This uses generics machinery I think? I have never really touched generics

the server function is built using

server :: Server ItemApi

with a yell bird between each handler in the same order as in the api type.

The individual handler functions

ReqBody '[JSON] User

describes the request type

Raw endpoint for serving static files?

servant-client generates haskell functions for api

Authentication is its own can of worms

some aspect of swagger autgenerates the nice api playground page

This has a number of useful articles

https://mmhaskell.com/blog/2017/10/9/serve-it-up-with-servant



checking out the example servant projects is also good.





generics - implement to and from. Uses functional dependencies

https://www.stackbuilders.com/tutorials/haskell/generics/



ST monad, The extra parameter can be interpeted as a heap

existential types. Let's you put a typeclass restraint on incoming guy.

https://www.youtube.com/watch?v=SPpIbiZFPRY
