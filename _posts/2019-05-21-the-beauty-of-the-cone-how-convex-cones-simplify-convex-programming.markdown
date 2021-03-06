---
author: philzook58
comments: true
date: 2019-05-21 16:46:24+00:00
layout: post
link: https://www.philipzucker.com/the-beauty-of-the-cone-how-convex-cones-simplify-convex-programming/
slug: the-beauty-of-the-cone-how-convex-cones-simplify-convex-programming
title: 'The Beauty of the Cone: How Convex Cones Simplify Convex Programming'
wordpress_id: 2022
categories:
- Optimization
tags:
- convex
- math
- optimization
---




I watched the [Stephen Boyd course](http://web.stanford.edu/class/ee364a/) to get me started in convex programming. At the beginning, he spends some time talking about convex sets rather than launching in convex optimization. I did not appreciate this sufficiently on the first pass. Convex sets are a very geometric topic and I think that for the most part, convex functions are best thought as a special case of them. The epigraph of a scalar valued convex function on $ R^d$ , the filled in area above a graph, is a d+1 dimensional convex set. Convex constraints on the domain can be thought of as further cutting this shape. Finding the minimum of the shape can be thought of as a geometrical problem of finding the furthest point in the -y direction.







There is another mathematical topic that I did not appreciate for how powerful and clean it is. If you check out this [textbook by Fenchel](http://www.convexoptimization.com/TOOLS/Fenchel1951.pdf), he starts with the topic of convex cones rather than sets, I now realize for good reason.







I was sketching out a programmatic representation of convex sets and was annoyed at how ugly things were turning out. First off, infinity is a huge problem. Many convex problems have infinite answers.  








The simplest problem is $ \max_x c^T x$ with no constraints. The answer plunges off to infinity vaguely in the direction of $ c$. The next simplest problem is $ \max_x c^T x , a^T x \geq 0$. This either goes off to infinity away from the constraint plane, hits the constraint plane and goes off to infinity, or if c and a are parallel, it is an arbitrary location on the constraint plane.







In short, the very most simple convex problems have infinite answers. You actually need to have a fairly complex problem with many conditions before you can guarantee a finite answer. Once we have a bounded LP, or a positive definite quadratic problem do we start to guarantee boundedness.  








In order to work with these problems, it is helpful (necessary?) to compactify your space. There are a couple options here. One is to arbitrarily make a box cutoff. If we limit ourselves to an arbitrary box of length 1e30, then every answer that came back as infinite before is now finite, albeit huge. This makes me queasy though. It is ad hoc, actually kind of annoying to program all the corner cases, and very likely to have numerical issues. Another possibility is to extend your space with rays. Rays are thought of as points at infinity. Now any optimization problem that has an infinite answer returns the ray in the direction the thing goes of to infinity at. It is also annoying to make every function work with either rays or points though. 







Another slightly less bothersome aesthetic problem is that the natural representation of half spaces is a normal ray and offset $ a^T x \geq b$ The principles of duality make one want to make this object as similar to our representation of points as possible, but it has 1-extra dimension and 1 arbitrary degree of freedom (scalar multiplying a and b by the same positive constant does not change the geometrical half space described). This is ugly.







In the field of projective geometry, there is a very beautiful thing that arises. In projective geometry, all scalar multiples of a ray are considered the same thing. This ray is considered a "point". The reason this makes sense is that projective geometry is a model of perspective and cameras. Two points are completely equivalent from the perspective of a pinhole camera if they lie on the same ray connecting to the pinhole. This ray continues inside the camera and hits the photographic screen. Hence points on the 2D screen correspond to rays in 3D space. It makes elegant sense to consider the pinhole to be the origin or your space, and hence you come to the previous abstract definition. Points at infinity in 3D (like stars effectively) are not a problem since they lie on finitely describable rays. Points at infinite edge of the 2D screen are not really a problem either. Perfectly reasonable points in 3D can map to the infinite edge of the screen in principle. Someone standing perfectly to the side of the pinhole in 3d space has a ray that goes perfectly horizontally into the camera, and in a sense would only hit a hypothetical infinite screen at infinity.







A great many wonderful (and practical!) things fall out of the projective[ homogenous coordinates](https://en.wikipedia.org/wiki/Homogeneous_coordinates). They are ubiquitous in computer graphics, computer vision, and robotics. The mathematical language describing translations and rotations is unified. Both can be described using a single matrix. This is not the intention, but it is a pleasant surprise. Other geometrical questions become simple questions of linear or vector algebra. It is very cool.







Can we use this method for describing the space we want to find convex sets in? I think not. Unfortunately, the topology of projective space is goofy. At the very least in 2D projective space, which can be thought of as a sphere with opposite points identified,  do not necessarily have an inside and outside (I'm questioning this idea now)? So convex sets and talking about maximal half planes and such seems questionable.







But I think we can fix it. Cones are good. In a slight twist on the projective geometry idea, what if you only non negative multiples of rays $ \lambda \geq 0$ as the same "point". You can take as a canonical plane $ x_0 =1$ similar to the pinhole camera. This plane can be thought of as your more ordinary affine space. Now half spaces touching the origin (cones) correspond to affine half spaces. We have a reasonable way of describing points at infinity on this plane, which correspond to rays. Arbitrary convex sets on this plane correspond to cones of rays.







Cones in this context are sets closed under arbitrary non-negative sums of points within them. Hence a cone always includes the origin. Cones are basically convex sets of rays. 







By adding in an arbtrary-ish degree of freedom to points, we bring points and half spaces much closer in alignment. Now evaluating whether a point in a half space looks like $ a^T x \geq 0$ with no ugly extra b.







So in closing, as convex sets are kind of a cleaner version of convex functions, so are convex cones a cleaner version of convex sets. This is actually useful, since when you're programming, you'll have to deal with way less corner infinite cases. The theory is also more symmetrical and beautiful









