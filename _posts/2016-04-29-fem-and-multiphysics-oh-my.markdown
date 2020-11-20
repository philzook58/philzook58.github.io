---
author: philzook58
comments: true
date: 2016-04-29 14:09:35+00:00
layout: post
link: https://www.philipzucker.com/fem-and-multiphysics-oh-my/
slug: fem-and-multiphysics-oh-my
title: FEM and multiphysics oh my
wordpress_id: 346
---

So I've been poking around trying to find all the simulation packages. I've got a virtual machine burning a hole in my pocket. Should've sprung for more ram. Let's fill it with garbage.

How is a compilation ever successful. It seems beyond belief.

gmsh

code_aster - solid mechanics solving

moose - Sandia National Lab

Cubic

elmer

salome

openfoam- fluid mechanics stuff



A very interesting alternative is simscale, which now integrates with onshape. Simscale is sort of a web based wrapper for some opensource (I think code_aster, openfoam, and salome at least) stuff, but I am a big fan of convenience. Writing up the files and compiling this code is not entirely trivial.

So you pick your model from onshape or from an external file, mesh it with some mesh generator. AutomaticTetrahedral is from salome. SnappyHexMesh is from openfoam.

Then you need to set the simulation type and boundary conditions for faces. You need to hold some fixed, place loads on others.

Then you run. To visualize the solution you place filters. The Warp filter is a good one for bending. It warps the model in the direction of the displacement. It might be recommended while this part is in beta to download the paraview file and use paraview.
