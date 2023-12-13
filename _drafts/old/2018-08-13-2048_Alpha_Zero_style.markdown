---
author: philzook58
comments: true
date: 2018-08-13 04:23:41+00:00
layout: post
link: https://www.philipzucker.com/?p=1196
published: false
slug: 2048 Alpha Zero style
title: 2048 Alpha Zero style
wordpress_id: 1196
---



We took an coursera AI course a while back that used 2048 as a problem which we approached with a more standard minimax approach.

https://github.com/ishmandoo/AI_2048

That gives us the structure of the code for selecting moves and the game mechanics

https://web.stanford.edu/~surag/posts/alphazero.html

To get started we'll just implement raw monte carlo tree search

http://mcts.ai/about/index.html

There are some questions about what should be expanded and how

I think what we narrowed down on has a lot of repetition

I mean, since we aren't really gonna have a deep  network, is this really alpha zero?
