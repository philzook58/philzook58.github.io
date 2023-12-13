---
author: philzook58
comments: true
date: 2017-11-20 15:53:40+00:00
layout: post
link: https://www.philipzucker.com/?p=922
published: false
slug: Aff Monad in Purescript
title: Aff Monad in Purescript
wordpress_id: 922
---

Aff  is short for Asynchronous Effects. It is a monad for asynchronous computation in comparison to Eff which is for sequential computation

https://qiita.com/kimagure/items/2ebce1399bac00c79656

https://github.com/slamdata/purescript-aff



makeAff converts a callback in Eff to value in Aff

launchAff does a set of asynchrnous actions. It returns a canceller

forkAff let's you run code in a seperate thread

AVars are like MVars. They block on read if empty, they block on write if full



https://gist.github.com/anonymous/9585f309db7bc64478c5a8585ad0065a




