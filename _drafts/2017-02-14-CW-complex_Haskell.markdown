---
author: philzook58
comments: true
date: 2017-02-14 18:18:44+00:00
layout: post
link: https://www.philipzucker.com/?p=649
published: false
slug: CW-complex Haskell
title: CW-complex Haskell
wordpress_id: 649
---

Just a quick thought. A CW complex takes lower dimensional objects and uses attaching maps.

This gives a definition of a circle using functions as the subset relationship. The Hasse diagram is the function between types diagram.

    
    -- makes a circle
    
    type V1 = ()
    type V2 = ()
    
    type E1 = Float
    type E2 = Float
    
    v1e1 :: V1 -> E1
    v1e1 _ = 0
    
    v1e2 :: V1 -> E2
    v1e2 _ = 0
    
    v2e1 :: V1 -> E1
    v2e1 _ = 1
    
    v2e2 :: V1 -> E2
    v2e2 _ = 1


No. This is not what I want.

Somehow, I want inductive attachment to the skeleton.
