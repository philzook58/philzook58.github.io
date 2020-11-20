---
author: philzook58
comments: true
date: 2018-02-16 21:58:45+00:00
layout: post
link: https://www.philipzucker.com/haskell-gloss-awesome/
slug: haskell-gloss-awesome
title: Haskell Gloss is awesome
wordpress_id: 987
tags:
- haskell
---

Edit: Check this out [https://mmhaskell.com/blog/2019/7/1/gloss-review](https://mmhaskell.com/blog/2019/7/1/gloss-review) !

Gloss is a super simple binding to drawing 2d stuff in a window for haskell

[https://hackage.haskell.org/package/gloss](https://hackage.haskell.org/package/gloss)

Given how relatively bewildering Hello World feels in Haskell, it's surprising how easy it is to get an animated window going. I think that may be because of expectations. You expect Hello world to be really easy and have no confusion and yet there is an inexplicable IO monad-what? , whereas you expect drawing to involve a bunch of inexplicable boiler plate bullshit.

    
    module Main where
    
    import Graphics.Gloss
    
    main :: IO ()
    main = simulate (InWindow "Nice Window" (200, 200) (10, 10)) 
           white 30 
           (0,0) 
           (\(theta,dtheta) -> Line [(0,0), (40 * cos theta, 40 * sin theta)]) 
           (\_ dt (theta, dtheta) -> (theta + dt * dtheta,dtheta - dt * (cos theta)))


This simulates a pendulum. Drawing it as a line.

simulate takes a pile of arguments

first thing describes a window, with title text, size and screen position I think?

then background color

frames per second

initial state (0 angle 0 angular velocity)

a drawing function from state to a picture, which is a gloss type of lines and crap

and a state update function taking a time step dt and current state.

I feel like there is room for a completely introductory tutorial to Haskell using gloss. It's so rewarding to see stuff splash up on the screen.

MAYBE I'LL DO IT. or maybe not.
