---
author: philzook58
comments: true
date: 2020-11-12 19:58:51+00:00
layout: post
link: https://www.philipzucker.com/?p=2928
published: false
slug: Kerbal Space Program
title: Kerbal Space Program
wordpress_id: 2928
---

  * [http://tomchaplin.xyz/portfolio/Control-Systems-in-Kerbal-Space-Program/](http://tomchaplin.xyz/portfolio/Control-Systems-in-Kerbal-Space-Program/)
  * https://www.coursera.org/specializations/spacecraft-dynamics-control#courses
  * https://krpc.github.io/krpc/python.html
  * [https://www.youtube.com/watch?v=D_X5k5lvx10&feature=youtu.be](https://www.youtube.com/watch?v=D_X5k5lvx10&feature=youtu.be)
  * [https://whiteaster.com/blog/kerbal-space-program%E2%80%8A-%E2%80%8Acomplex-environment-for-reinforcement-learning/](https://whiteaster.com/blog/kerbal-space-program%E2%80%8A-%E2%80%8Acomplex-environment-for-reinforcement-learning/)

CKan is a Kerbal package manager [https://github.com/KSP-CKAN/CKAN/releases](https://github.com/KSP-CKAN/CKAN/releases) [https://github.com/KSP-CKAN/CKAN/wiki/Installing-CKAN-on-Ubuntu](https://github.com/KSP-CKAN/CKAN/wiki/Installing-CKAN-on-Ubuntu) Opne up ckan from the command line.  

Alright I'm trying to build the source. God help me. I needed a downgraded version of bazel-1.0.0. [https://github.com/krpc/krpc/blob/master/tools/docker/Dockerfile](https://github.com/krpc/krpc/blob/master/tools/docker/Dockerfile)  [https://krpc.s3.amazonaws.com/](https://krpc.s3.amazonaws.com/)

Ben did not seem to have any problems

Copy the krpc folder in GameData into the GameData folder of kerbal

What would be interesting to do with rotating frames?

Rotations? Rotation inference? The MIP method from Russ?

[https://esa.github.io/pykep/examples/index.html#generic](https://esa.github.io/pykep/examples/index.html#generic) pykep

  * http://taha.eng.uci.edu/Geometric_Control_Course.html 
  * http://web.mit.edu/nsl/www/videos/lectures.html nonlinear control slotine
  * 



Getting to the moon. You want 

start when the moon is 90 degs from you
You want to burn such that eventually you'll intersect at 180 degrees across the planet.
This is because again burning prograde moves the opposite side of you orbit, which you want to slingshot over to the moon


3.4k = deltav to get into orbit



kerbal space program implements a "sphere of influence". Only one body affects another at a time
Nothing has a tiled orbit

wiki kerbal space program https://wiki.kerbalspaceprogram.com/wiki/Mun

- atmosphere as 70km
     low kerbin orbit (lko) 75 - 100 km altitude, 2200m/s orbital speed



delta v
 - most intuitive model is to consider burn to be instantaneous. Once in orbit
 - strange model of lift off or when fighting gravity
 - also you mostly prograde or retrograde, so "hovering" isn't a point
 - 


cheat menu - put me in orbit around kerbin
delta v - map

plane change


Delta v and phase maps. Tells you about how much fuel you need and relative position of planets when to do your fire.
![](/assets/kerbal_deltav.png)

![](/assets/kerbal_phase.png)