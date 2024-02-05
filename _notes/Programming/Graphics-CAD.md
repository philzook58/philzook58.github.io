---
layout: post
title: CAD
---

- [CAD](#cad)
  - [Modelling](#modelling)
  - [Games](#games)
  - [VR / XR / AR](#vr--xr--ar)
  - [Background](#background)
- [Photogrammetry](#photogrammetry)
- [Computer Vision](#computer-vision)
- [Graphics](#graphics)
- [Inkscape](#inkscape)
- [FEM](#fem)

# CAD

opencascade <https://dev.opencascade.org/> - open source brep engine
<https://www.doscienceto.it/blog/posts/2024-01-23-ffi.html> <https://dev.opencascade.org/doc/overview/html/occt__tutorial.html> bottle tutorial
OCCT
<https://github.com/trelau/pyOCCT> <https://github.com/tpaviot/pythonocc-core>

CGL

<https://twitter.com/TLAlexander/status/1727571928905597091>

fornjot <https://github.com/hannobraun/Fornjot>
solvespace
<https://github.com/tlalexander/open-cad-foundation/discussions> open cad foundatin

truck <https://github.com/ricosjp/truck> rust cad kernel <https://news.ycombinator.com/item?id=35071317>
<https://github.com/MattFerraro/CADmium> Looks nice. Does it do anything?

MarshallB used for CAD [Sound and Robust Solid Modeling via Exact Real Arithmetic
and Continuity](https://dl.acm.org/doi/pdf/10.1145/3341703) <https://www.youtube.com/watch?v=h7g4SxKIE7U> - Ben Sherman giving a talk on this <https://www.ben-sherman.net/publications.html> some other related publications and thesis. <https://arxiv.org/pdf/2007.08017.pdf> differntiable

gmsh <http://gmsh.info/> meshing A three-dimensional finite element mesh generator with built-in pre- and post-processing facilities

OpenSCAD <https://nostarch.com/programmingopenscad>

Onshape

Freecad

solidworks

JoinABLe: Learning Bottom-up Assembly of Parametric CAD Joints  <https://arxiv.org/abs/2111.12772>

## Modelling

<https://johanpeitz.itch.io/picocad>

blockbench <https://www.blockbench.net/> simple block based minecrafty editor <https://github.com/JannisX11/blockbench> . web editor.

blender

[online viewer for cad](https://news.ycombinator.com/item?id=34936831) use open cascade and emscripten.

<https://news.ycombinator.com/item?id=38448653> meshgpt

## Games

Unity - The Big Dog

Unreal Engine 4. Kind of scares me

Godot - 3d and 2d. Kind of a Unity clone with

Love - Lua, supposed to be simple. 2D. All programmatic

PyGame - Old, and python. Lot's a support questions going to be avaiable. 2D

pico8

<https://www.gbstudio.dev/> drag and drop retro game creator

## VR / XR / AR

Space adventure zone

WebVR is deprecated
WebXR

aframe <https://aframe.io/docs/1.5.0/introduction/> ctrl-alt-i opens up isnpector. pretty cool.
<https://supermedium.com/>
<https://en.wikipedia.org/wiki/GlTF> web gl scene format can be exported

babylon

three.js

unity has a third party exporter

## Background

b-rep <https://en.wikipedia.org/wiki/Boundary_representation>
Step file <https://en.wikipedia.org/wiki/ISO_10303>
NURBS <https://en.wikipedia.org/wiki/Non-uniform_rational_B-spline>

constructive solid geometry

# Photogrammetry

point cloud
<https://en.wikipedia.org/wiki/MeshLab>
icp iterative

# Computer Vision

slam

# Graphics

<https://nostarch.com/computer-graphics-scratch> grahics from scratch

<https://www.cs.cmu.edu/~kmcrane/>> Keenan Crane. So good. <http://15462.courses.cs.cmu.edu/fall2021/>

<https://www.youtube.com/playlist?list=PLplnkTzzqsZTfYh4UbhLGpI5kGd5oW_Hh> Intro to graphics
<https://www.youtube.com/playlist?list=PLQ3UicqQtfNuBjzJ-KEWmG1yjiRMXYKhh> Justin Solomon

[Line art from images cvpr](https://twitter.com/ak92501/status/1507163038666919941?s=20&t=y2AWW1GNA8vyxsWqTXmKPQ)

[Shane's shadertoys. well documented](https://www.shadertoy.com/user/Shane/sort=popular)

[Shaders pt 1](https://www.youtube.com/watch?v=kfM-yu0iQBk&ab_channel=FreyaHolm%C3%A9r)

<https://github.com/ricktu288/ray-optics>

[Draw SVG rope using JavaScript](https://muffinman.io/blog/draw-svg-rope-using-javascript/)
[](https://muffinman.io/blog/js-libraries-for-generative-art/)

[crazy generative audio stuff](https://news.ycombinator.com/item?id=34163559)

attributes - sent to vertex shader
uniform - paramters sent to shaders
varying sent to fragment shader

Bloom effect

`mix` `mod`

Gamma correction and color mixing

green coordinates

Siggraph
[siggraph retrospective- Seminal Graphics Papers: Pushing the Boundaries, 50 year retro](https://dl.acm.org/doi/book/10.1145/3596711)

Ray tracng in one weekend

<https://github.com/vkoskiv/c-ray> ray tracgin in C. fancy looking with lots of features

# Inkscape

[Inkscape](https://inkscape.org/)
Logos by nick <https://www.youtube.com/playlist?list=PLynG8gQD-n8C-WYNovoPzWvxDMb1Ls_7S> seemspretty good

Ctrl is important key in inksapce. lock. spacebare for duplicate stamp
S for select
alignment can pick relative
shape union - shape differenc
Circle control nodes for arc and rounding corners. Convert to path.

<https://castel.dev/post/lecture-notes-2/> How I draw figures for my mathematical lecture notes using Inkscape

<https://michaelneuper.com/posts/efficient-latex-editing-with-emacs/>
<https://castel.dev/post/lecture-notes-1/> How I'm able to take notes in mathematics lectures using LaTeX and Vim

# FEM

See also: partial differential equations

code_aster - solid mechanics solving
moose - Sandia National Lab
Cubic
elmer
salome
openfoam- fluid mechanics stuff

- Sfepy
- Fenics, dolfin
- BEM++
- Gerris
- ASL
- meshpy
- SolidPython
- Skidl
