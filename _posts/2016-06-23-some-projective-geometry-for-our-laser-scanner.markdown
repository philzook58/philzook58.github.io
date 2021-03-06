---
author: philzook58
comments: true
date: 2016-06-23 22:33:00+00:00
layout: post
link: https://www.philipzucker.com/some-projective-geometry-for-our-laser-scanner/
slug: some-projective-geometry-for-our-laser-scanner
title: Some Projective Geometry for our laser scanner
wordpress_id: 464
---

We're building a simple laser scanner. Camera attached to a board, with line laser hot glued to a servo on same board.

![](/assets/Thu-Jun-23-2016-182606-GMT-0400-EDT.png)

The line laser will scan. This laser line defines a plane. a pixel on the camera corresponds to a ray originating from the camera. Where the ray hits the plane is the 3d location of the scanned point.

Projective geometry is mighty useful here. To take a point to homogenous coordinates add a 1 as a fourth coordinate.

Points with 0 in the fourth coordinate are directions aka points on the plane at infinity (that's a funky projective geometry concept, but very cool).

Planes are also defined by 4 coordinates. The first 3 coordinates are the normal vector of the plane. $ a \cdot x = c $. The fourth coordinate is that value of c, the offset from the origin. We can also find the plane given 3 points that lie on it. This is what I do here. What we are using is the fact that a determinant of a matrix with two copies of the same row will be zero. Then we're using the expansion of a determinant in term of its minors, probably the formula they first teach you in school for determinants. Because of these facts, this minor vector will dot to zero for all the points on that plane.

Then finally we're finding the intersection of the ray with the plane. The line is described as a line sum of two homogenous points on the line. we just need to find the coefficients in the sum. You can see by dotting the result onto the plane vector that the result is zero.

Then we dehomogenize the coordinates by dividing by the fourth coordinate.





    
    import numpy as np
    
    #origin is camera position. z is direction camera is looking. x is to the right. y is up.
    #Waiiiiiit. That's a left handed cooridnate system? Huh. Whatever. May come out mirrore
    PCameraHomog = np.array([0.,0.,0.,1.])
    #Baseline distance of 
    #Let's use units of meters
    PLaser = np.array([ 0.3 ,0,0])
    
    #I have measured my angle from -x going clockwise. God that is dumb.
    laserAngle = 60.
    laserRadian = laserAngle *np.pi/180.
    
    PLaserHomog = np.append(PLaser, [1.])
    upDirHomog = np.array([0.,0.,1.,0.])
    laserDirHomog = np.array([-1.* np.cos(laserRadian), np.sin(laserRadian), 0., 0.])
    
    planeMat = np.stack((PLaserHomog, upDirHomog, laserDirHomog))
    
    def colminor(mat,j):
    	subMat = np.delete(mat, j, axis=1)
    	return (-1.)**j * np.linalg.det(subMat)
    
    #The homogenous vector describing the plane coming off of the line laser. p dot x = 0 if x is on plane
    laserPlaneHomog = np.array(map(lambda j: colminor(planeMat, j) , range(4)))
    
    #Should all be zero
    print np.dot(laserPlaneHomog, laserDirHomog)
    print np.dot(laserPlaneHomog, upDirHomog)
    print np.dot(laserPlaneHomog, PLaserHomog)
    
    def pixelDir(x,y):
    	# pix / f = objsize / objdist
    	# f = pix * objdist / objsize
    	f = 100. #camera Width of 1m object at 1m in pixels, or 8m object at 8m. 
    	return np.array([ x / f ,  y / f , 1., 0.])
    
    cameraRay = pixelDir(10,20)
    
    #pos is on line between camera pos and ray and lies on laserplane. Hence pos dot plane = 0, which you can see will happen
    posHomog = np.dot(cameraRay, laserPlaneHomog) * PCameraHomog - np.dot(PCameraHomog, laserPlaneHomog) * cameraRay
    print posHomog
    
    def removeHomog(x):
    	return x[:3]/x[3]
    
    pos3 = removeHomog(posHomog)
    
    print pos3
    
    
    







