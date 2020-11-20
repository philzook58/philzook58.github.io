---
author: philzook58
comments: true
date: 2015-12-30 05:08:25+00:00
layout: post
link: https://www.philipzucker.com/opencv-feature-detection-and-tracking/
slug: opencv-feature-detection-and-tracking
title: OpenCV feature detection and tracking
wordpress_id: 358
---

Wrote some utter shit code to get started with tracking via feature detection. Probably not the best way to go about the business.

Click on the screen to pick the green dot to follow

Uses the ORB feature finder. Each feature then has a descriptor and does brute force search to find best one.

Needs a lot more to be useful for anything. Suggestions: reject outliers, take best k matches and pick closest one to previous match, maintain a set of best current descriptors.

This is another approach to following something, but I'm not sure it is a great one.

    
    import cv2
    import numpy as np
    
    
    orb = cv2.ORB()
    bf = cv2.BFMatcher(cv2.NORM_HAMMING, crossCheck=True)
    
    minpoint = []
    mindes = []
    def findNearestKeyPoint(x,y,kp,des):
        global minpoint, mindes
        mindist = 100000000000
        minpoint = kp[0]
        mindes = des[0]
        index = 0
        for point in kp:
            dist = (point.pt[0]-x)**2+(point.pt[1]-y)**2
            if dist < mindist:
                mindist = dist
                minpoint = point
                mindes = des[index]
                #print des[index]
            index += 1
    
    
    def service_mouse(event,x,y,flags,param):
        global kp, des
        if event == cv2.EVENT_LBUTTONDOWN:
            findNearestKeyPoint(x,y,kp,des)
    
    
    cap = cv2.VideoCapture(0)
    
    cv2.namedWindow('image')
    cv2.setMouseCallback('image',service_mouse)
    
    while(1):
    
        _, frame = cap.read()
    
        gray = cv2.cvtColor(frame, cv2.COLOR_BGR2GRAY)
        kp = orb.detect(gray,None)
        kp, des = orb.compute(gray, kp)
        img2 = cv2.drawKeypoints(frame,kp,color=(0,255,0), flags=0)
        if minpoint:
            cv2.circle(img2, (int(minpoint.pt[0]),int(minpoint.pt[1])) , 4, [0,0,255],-1 )
    
            matches = bf.match(np.array([mindes]),des)
            # suggestions: get list of best, pick closest to knwon position, update descriptors
    
            matches = sorted(matches, key = lambda x:x.distance)
            newguy = kp[matches[0].trainIdx].pt
            cv2.circle(img2, (int(newguy[0]),int(newguy[1])) , 10, [0,0,255],-1 )
    
    
        cv2.imshow('image',cv2.pyrDown(img2))
    
        k = cv2.waitKey(5) & 0xFF
        if k == 27:
            break
    









