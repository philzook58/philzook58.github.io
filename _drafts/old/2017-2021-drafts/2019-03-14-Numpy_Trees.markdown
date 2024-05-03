---
author: philzook58
comments: true
date: 2019-03-14 17:52:44+00:00
layout: post
link: https://www.philipzucker.com/?p=1869
published: false
slug: Numpy Trees
title: Numpy Trees
wordpress_id: 1869
---




APL is very interesting and cool, although perhaps the most off-putting programing language I've ever seen at first glance.







[https://tryapl.org/](https://tryapl.org/)







I think numpy clearly takes inspiration from it (or Matlab does, whatever the chain of inheritance is)







Some of the corner stone operations of numpy have similar analogs in APL. reshaping is $latex \rho$, arange is $latex \iota$ and some others.







Numpy broadcasting and fancy indexing also have analogs.







I suspect APL is somewhat richer than Numpy although I do not know it well enough to know how.







Aaron Hsu has been making the rounds as a APL proselytizer. When I saw him at a conf, I had no goddamn idea what he was talking about. But here is a fairly straightforward discussion of trees 







[https://www.youtube.com/watch?v=hzPd3umu78g](https://www.youtube.com/watch?v=hzPd3umu78g)







[http://dfns.dyalog.com/index.htm](http://dfns.dyalog.com/index.htm)







[https://github.com/Co-dfns/Co-dfns](https://github.com/Co-dfns/Co-dfns)







So, one way to store trees is to store them leaf up. Store an array with index of parent and and array with index of neighbor







Using a self-index to show no parent or no sibling







We can also seperate the tree out by depth.







depth = [d1,d2,d3]







The most basic interesting tree computation I can think of is a multiply add tree.







If the fold of the tree is associate, then it doesn't make that much sense to worry about stuff this way. Not clear that the tree structure is even relevant at all.













APLpy







We could start trying to build an APL interpeter in terms of numpy expressions. Combined with some of the JIT technology (numba and that fortran one)







Side note: If you do these trees in numpy style, it transfers pretty readily over to tensorflow or pytorch. One-hot encoding for node type. maybe this doesn't make that much sense. Would you be able to differentiate the structure of the tree?



