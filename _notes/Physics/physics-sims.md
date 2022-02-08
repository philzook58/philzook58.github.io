---
layout: post
title: Physics Sims
---

# Physics Engines

[pybullet](https://pybullet.org/Bullet/phpBB3/viewforum.php?f=19)
[ten minues physics](https://matthias-research.github.io/pages/tenMinutePhysics/index.html)
[Verlet Physics: Simple but effective method for physics simulations in games | IGDC 2021](https://www.youtube.com/watch?v=zfkaMWIo3XM&ab_channel=IndiaGDC)

[matter js](https://brm.io/matter-js/)
[game physics from scratch](https://brm.io/game-physics-for-beginners/)

[box2d](https://box2d.org/)
chipmunk


Position based dynamics
Impulse based

Collision detection

# Fluids

[Julia GMSH petsc fluid sim](https://twitter.com/francescverdugo/status/1487115027979063296?s=20&t=OSBR7Kcf7AOCicTAypA9yQ)

## 2021

erin catto
https://ubm-twvideo01.s3.amazonaws.com/o1/vault/gdc09/slides/04-GDC09_Catto_Erin_Solver.pdf

Discrete time and space?
Allow some overlap?
Collisions using force fields

Reduce everything to points
Reduce everything to AABB
Model paths as R -> R? But then how to 
FRP?
Hierarchy of scales?
Collisions as discrete events is tough

Organizational scheme
Use classes?
collide(A,B)? return point? true/false? region included in both? AABB? Maximal AABB?
inside(x,A) ? point query?

javascript AD. Forward mode prob. No overloading sucks.


## 2017

Good resources

https://www.toptal.com/game/video-game-physics-part-ii-collision-detection-for-solid-objects

http://buildnewgames.com/gamephysics/

Ericson book on collision detection

Ian Millington Game Physics Engine

Forum listing of resources

http://www.bulletphysics.org/Bullet/phpBB3/viewtopic.php?f=6&t=63

I've seen a couple phd theses mentioned

http://www.continuousphysics.com/ftp/pub/test/files/physics/papers/mirtichThesis.pdf

https://www.youtube.com/watch?v=wPKzwSxyhTI

