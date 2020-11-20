---
author: philzook58
comments: true
date: 2016-05-25 18:52:31+00:00
layout: post
link: https://www.philipzucker.com/visual-odometry-and-epipolar-stuff/
slug: visual-odometry-and-epipolar-stuff
title: Visual Odometry and Epipolar Stuff
wordpress_id: 452
---

I went on a huge projective geometry kick a few years back. I loved it when i found out about it.

Anyway, forgotten a great deal of it now. Looking into using cameras to determine displacement of a robot.

http://www.eng.auburn.edu/~troppel/courses/00sum13/7970%202013A%20ADvMobRob%20sp13/literature/vis%20odom%20tutor%20part1%20.pdf

https://en.wikipedia.org/wiki/Essential_matrix

Useful stuff

So if we translate and rotate 3d vectors we have

$latex x' = Rx+t$

If we take the cross product we have the equation

$latex t\times t=0$

$latex t \times x' = t \times R x$

Since whatever comes out of a cross product is perpendicular to what went in

$latex x' \cdot (t \times x') = 0 = x' \cdot t \times Rx$

Now we can just interpret these 3d vectors as 2d projective plane vectors from two different camera viewpoints (homogenous coordinates).

This last equation gives the epipolar constraint. It describes what the ray that projects to the object from camera 1 looks like in camera 2. And that ray is going to be a line. So the essential matrix converts from points in 1 camera to lines in the other camera.

Ok.

Then how do you get the R and t back from point correspondence? A cross product can be represented as a skew symmetric matrix (it's a linear process that takes a vector to another vector).

$latex t\times = [t]_x$

The cross product kills 1 vector, so this vector has eigenvalue 0 for this matrix.

And it flips two other vectors with some minus signs. In an orthogonal basis with t as one element, it would look something like

$latex \begin{matrix} 0 & -1 & 0 \\ 1 & 0 & 0 \\ 0 & 0 & 0 \end{matrix}$

So when we take the SVD of E, it will have 2 equal eigenvalues and 1 zero eigenvalue. $latex E = USV^T$

The matrix $latex V^T$ transforms from the x frame to the t frame.

The matrix U transforms from the t frame to the x' frame.

We can just unflip the two vectors switched up by the cross product in the t basis(The matrix that does this is called W) and compose U and V to reconstitute R.

Then we can find $latex [t]_x=ER^{-1}$

Note that the t you find is unknown up to scale. You can only find the direction of translation, not how far.

The problem comes from that you can't tell the difference between images of dollhouses and real houses. There is an unavoidable scale ambiguity. BUT, one would have estimates from all sorts of other places. Context maybe, other sensors, current estimates of velocity, estimates of the actual 3d position of the points you're using.

Makes sense, I think. Now I have to actually try it.


