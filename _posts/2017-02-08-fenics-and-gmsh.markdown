---
author: philzook58
comments: true
date: 2017-02-08 22:37:01+00:00
layout: post
link: https://www.philipzucker.com/fenics-and-gmsh/
slug: fenics-and-gmsh
title: Fenics and gmsh
wordpress_id: 626
---

I downloaded docker and set it up using their script.

fenicsproject notebook testbook

creates a notebook

Then

fenicsproject start testbook.

Starts a jupyter server.

You need to use python 2. Fenics is not installed for python 3 as far as I can tell.

I took the first example out of the tutorial book

You need

%matplotlib inline

in order to see the plots.

I installed solidpython which is a pythony version of openscad.

https://github.com/SolidCode/SolidPython

So you can output a scad file, but then you need to run openscad to convert it further.


brew install Caskroom/cask/openscad




puts it into an app folder and not in the path of the terminal




    
    import os
    
    os.system('/Applications/OpenSCAD.app/Contents/MacOS/OpenSCAD -o test.stl test.scad')


pip install numpy-stl

https://pypi.python.org/pypi/numpy-stl

ooh

%matplotlib notebook

makes an interactive plot. nice.

gmsh is necessary. Perhaps a better tool chain would just use gmsh and ignore the scad stuff.

http://femwiki.wikidot.com/fenics-intro:generating-meshes-and-fenics

https://github.com/FluidityProject/fluidity/wiki/Gmsh-tutorial

you can take a mesh from gmsh

gmsh

first click add points. add them in in by pressing e.

thenadd line

the add plane surface.

add physical group to start labelling boundaries.

click 2d under mesh.

refine it a couple times maybe then save the .msh

dolfin-convert untitled.msh test.xml

This is an answer as to how to grab these xml files

https://answers.launchpad.net/dolfin/+question/224015

So here's a start

[https://github.com/philzook58/python/blob/master/python/fenics/dolfin-convert.ipynb](https://github.com/philzook58/python/blob/master/python/fenics/dolfin-convert.ipynb)

This is not the cleanest workflow.
