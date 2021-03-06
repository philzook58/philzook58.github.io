---
author: philzook58
comments: true
date: 2016-08-01 03:16:27+00:00
layout: post
link: https://www.philipzucker.com/aruco-in-opencv/
slug: aruco-in-opencv
title: Aruco in opencv
wordpress_id: 483
tags:
- aruco
- opencv
---

So there isn't great documentation on the python bindings as far as I can find. There are docs on the c++ bindings.  Trying to do this on a mac was a hellish uphill battle, and opencv in the virtual machine has been... hmm actually pretty okay? Well, I did this on my fresh new triple boot ubuntu flash drive.

Invaluable is to go into the python REPL and type

    
    import cv2
    help(cv2.aruco)


Then you can see what all the available functions are. They're more or less self explanatory, especially since they are described in the opencv c++ tutorials.

[http://docs.opencv.org/3.1.0/d9/d6d/tutorial_table_of_content_aruco.html](http://docs.opencv.org/3.1.0/d9/d6d/tutorial_table_of_content_aruco.html)

I believe the python bindings are generated programmatically, and they are fairly systematic, but always a touch different from the c++ function calls. A big difference is typically the python calls don't modify in place.

Anyway, to get you up, I cobbled together some really basic code. It can generate a tag and save it

    
    import numpy as np
    import cv2
    import cv2.aruco as aruco
    
    
    '''
        drawMarker(...)
            drawMarker(dictionary, id, sidePixels[, img[, borderBits]]) -> img
    '''
    
    aruco_dict = aruco.Dictionary_get(aruco.DICT_6X6_250)
    print(aruco_dict)
    # second parameter is id number
    # last parameter is total image size
    img = aruco.drawMarker(aruco_dict, 2, 700)
    cv2.imwrite("test_marker.jpg", img)
    
    cv2.imshow('frame',img)
    cv2.waitKey(0)
    cv2.destroyAllWindows()
    


And this is a basic program to detect the markers

    
    import numpy as np
    import cv2
    import cv2.aruco as aruco
    
    
    cap = cv2.VideoCapture(0)
    
    while(True):
        # Capture frame-by-frame
        ret, frame = cap.read()
        #print(frame.shape) #480x640
        # Our operations on the frame come here
        gray = cv2.cvtColor(frame, cv2.COLOR_BGR2GRAY)
        aruco_dict = aruco.Dictionary_get(aruco.DICT_6X6_250)
        parameters =  aruco.DetectorParameters_create()
    
        #print(parameters)
    
        '''    detectMarkers(...)
            detectMarkers(image, dictionary[, corners[, ids[, parameters[, rejectedI
            mgPoints]]]]) -> corners, ids, rejectedImgPoints
            '''
            #lists of ids and the corners beloning to each id
        corners, ids, rejectedImgPoints = aruco.detectMarkers(gray, aruco_dict, parameters=parameters)
        print(corners)
    
        #It's working.
        # my problem was that the cellphone put black all around it. The alrogithm
        # depends very much upon finding rectangular black blobs
    
        gray = aruco.drawDetectedMarkers(gray, corners)
    
        #print(rejectedImgPoints)
        # Display the resulting frame
        cv2.imshow('frame',gray)
        if cv2.waitKey(1) & 0xFF == ord('q'):
            break
    
    # When everything done, release the capture
    cap.release()
    cv2.destroyAllWindows()
    


They are sprinkled with the requisite garbage and cruft of me wiggling around with print statements to figure out what everything is.

It sounds like more of what I want is to use Aruco boards. They sound good. I'm looking into using this for maybe robot configuration sensing.


