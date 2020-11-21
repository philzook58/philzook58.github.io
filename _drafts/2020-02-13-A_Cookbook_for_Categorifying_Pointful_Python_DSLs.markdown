---
author: philzook58
comments: true
date: 2020-02-13 19:21:40+00:00
layout: post
link: https://www.philipzucker.com/?p=2658
published: false
slug: A Cookbook for Categorifying Pointful Python DSLs
title: A Cookbook for Categorifying Pointful Python DSLs
wordpress_id: 2658
---




Haskell has a long tradition of drawing inspiration from category theory. Julia also has the Catlab.jl development. While I love and respect these languages, I do know in my heart that they are somewhat difficult and require being kind of a niche weirdo to get past the pain to get to the beauty. 







However, today python is the lingua franca of scientific computing. The syntax is fairly readable and unoffensive to beginners as far as these things go.  Many people end up learning a bit of python even if computing isn't really what they do. Biologists, physicists, economists, engineers, even pure mathematicians.







There is nothing to stop us from using python as a vehicle for categorical modeling.







Python isn't quite the perfect fit, because we have concepts that are painful to express in python.







To me, as a fairly unsophisticated user of category theory, when I say category theory, I basically mean a point-free / combinatory DSL. Variables are unpleasant to manipulate. Compact high level notation with algebraic (manipulable) is extremely useful for many purposes. The canonical examples is matrix notation. One can work with indexful matrices and be very expressive. It is fairly easy to write a tensor expression. However, these terms are verbose and rather difficult to manipulate correctly or recognize patterns. Your eye has to work modulo the names of variables to see things.







A lot of very good work has already gone into solvers. While one could try to reinvent the wheel, and maybe sometimes should, the shortest road is to build a platform atop that wheel. 







There are a class of embedded dsls that have Variable objects you can instantiate.







  * Sympy
  * Cvxpy, Pyomo
  * Z3Py






The cornerstones of the scientific python stack







  * scipy
  * numpy
  * pandas








