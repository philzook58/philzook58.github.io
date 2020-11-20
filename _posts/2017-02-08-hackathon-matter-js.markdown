---
author: philzook58
comments: true
date: 2017-02-08 22:25:57+00:00
layout: post
link: https://www.philipzucker.com/hackathon-matter-js/
slug: hackathon-matter-js
title: 'Hackathon: Matter.js'
wordpress_id: 633
---

For the Brown hackathon, we made a multiplayer browser video game called Enceladus using node, raw javascript, socket.io, and matter.js as a physics engine.

https://github.com/ishmandoo/enceladus

I think we'll keep working on it, so I'll post more when it isn't a pile of Hackathon garbage.

Here are some scattered, totally worthless to anyone else notes as I started exploring the documentation of Matter.js:

Engine.update updates by dt



Bodies - factory methods for creating new bodies

Bounds - Axis aligned bounding box = min and max x and y values

Body. whatever lets you set almost anything about a body.

set to static can be useful

bodies hold velocity prev velocity other things. I bet you mostly should not update these values manually.



Common - useful random crap. Random picks random values. chaining seems useful? clone. topological sort. sign function.



Constraint - fix distance between two points. No rotation contraints?



SAT - seperating axis theorem - convex shapes -

http://www.dyn4j.org/2010/01/sat/



Engine - clear resets



Grid

broad phase collision detection?

http://buildnewgames.com/broad-phase-collision-detection/






