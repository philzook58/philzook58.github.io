---
author: philzook58
comments: true
date: 2017-02-11 17:34:28+00:00
layout: post
link: https://www.philipzucker.com/?p=629
published: false
slug: CGAL PyMesh
title: CGAL PyMesh
wordpress_id: 629
---

http://www.cgal.org/index.html

http://pymesh.readthedocs.io/en/latest/



sudo apt-get install libcgal-dev

Went to the tutorial and copied and pasted code to see if it works.

    
    g++ hello_world.cpp -lCGAL -frounding-math


will compile. Order matters for -l tags? Weird weird weird. I saw a thing that suggested using -lgmp as well. We'll see.



    
    pip install cgal-bindings


I need to install SWIG?

Hmm got an error about ASCII something. Need to use pip3

Ok.  fatal error: CGAL/Advancing_front_surface_reconstruction.h: No such file or directory

Can't find an answer. Not worth it. I'll just use C++.

https://www.youtube.com/watch?v=Mk-NH2-_hMo

https://www.youtube.com/watch?v=3DLfkWWw_Tg



On another note

https://www.youtube.com/watch?v=zWhMc3am7ao&t;=1189s



Ok. I had problems installing the bindings. It has been suggested that the apt-get cgal is way out of date on my rusty 14.04 ubuntu.

brew install cgal

sudo pip install cgal-bindings

Hey it appears to have worked! This is the first time ever I've had an easier time on my mac rather than ubuntu. Dang, I REALLY need to upgrade to 16.

Examples are useful

https://github.com/CGAL/cgal-swig-bindings/tree/master/examples/python


