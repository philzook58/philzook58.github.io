---
author: philzook58
comments: true
date: 2015-12-28 17:10:54+00:00
layout: post
link: https://www.philipzucker.com/more-opencv/
slug: more-opencv
title: More Opencv
wordpress_id: 348
---

Canny finds edges. Edges are basically places of very large derivative in the image. Then the canny algorithm cleans it up a little.

FindContours seems to be a clutch dude

[http://dsynflo.blogspot.com/2014/10/opencv-qr-code-detection-and-extraction.html](http://dsynflo.blogspot.com/2014/10/opencv-qr-code-detection-and-extraction.html)

This guy uses it to

    
    import cv2
    import numpy as np
    
    cap = cv2.VideoCapture(0)
    
    while(1):
    
        # Take each frame
        _, frame = cap.read()
    
        gray = cv2.cvtColor(frame, cv2.COLOR_BGR2GRAY)
        edges = cv2.Canny(gray,100,200)
        #ret,thresh = cv2.threshold(gray,50,255,cv2.THRESH_BINARY)
    
        kernel = np.ones((5,5),np.uint8)
        edges = cv2.dilate(edges,kernel,iterations = 5) # really chunks it up
    
        contours,hierarchy= cv2.findContours(edges,cv2.RETR_TREE,cv2.CHAIN_APPROX_SIMPLE)[-2:]
        cv2.drawContours(frame, contours, -1, (0,0,255), 3)
        cv2.imshow('res',cv2.pyrDown(frame))
        k = cv2.waitKey(5) & 0xFF
        if k == 27:
            break
    
    cv2.destroyAllWindows()


The dilation reduces the number of contours to something more reasonable

Each contour is of the format [[[x y]], [[x y]], [[x y]]]

I had a problem with draw contours until I found out I needed to write onto a color image with it.



The good features to track

    
    import cv2
    import numpy as np
    
    
    cap = cv2.VideoCapture(0)
    
    
    while(1):
    
        _, frame = cap.read()
    
        gray = cv2.cvtColor(frame, cv2.COLOR_BGR2GRAY)
        corners = cv2.goodFeaturesToTrack(gray,25,0.01,10)
        corners = np.int0(corners)
        for i in corners:
            x,y = i.ravel()
            cv2.circle(frame,(x,y),8,[0,0,255],-1) #image center radius color thickness
        cv2.imshow('image',cv2.pyrDown(frame))
    
        k = cv2.waitKey(5) & 0xFF
        if k == 27:
            break


The 25 is number of corners, 0.01 is a quality cutoff (1% of best corner quality found), 10 is minimum distance between corners


