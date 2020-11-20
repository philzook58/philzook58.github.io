---
author: philzook58
comments: true
date: 2017-09-01 14:04:50+00:00
layout: post
link: https://www.philipzucker.com/notes-ros-orb-slam-2/
slug: notes-ros-orb-slam-2
title: Notes on ROS and ORB SLAM 2
wordpress_id: 457
tags:
- ROS Visual Odometry
---

[https://github.com/raulmur/ORB_SLAM2](https://github.com/raulmur/ORB_SLAM2)

This seems like the most recent openly available slam package I could find. So let's try it out

whenever using ros always

    
    source /opt/ros/kinetic/setup.bash


run

    
    roscore




when using ros

rosnode info or rosnode list to inspect running nodes

rostopic gets the avaiable messages

Something like this. However, should edit the yaml config file

sudo apt-get install ros-kinetic-usb-cam

    
    rosrun usb_cam usb_cam_node


To inspect the image

    
    rosrun image_view image_view imag=/usb_cam/image_raw


rosrun usb_cam usb_cam_node __name:=camera

changes the topic name to camera



    
    rosrun ORB_SLAM2 Mono Vocabulary/ORBvoc.txt Examples/Monocular/TUM1.yaml
    


Dang. I'm pretty impressed. With a bad calibration file and no tuning, it works ok in short term. Blur clearly seems like an issue.

The contents of the example yaml config

    
    %YAML:1.0
    
    #--------------------------------------------------------------------------------------------
    # Camera Parameters. Adjust them!
    #--------------------------------------------------------------------------------------------
    
    # Camera calibration and distortion parameters (OpenCV) 
    Camera.fx: 517.306408
    Camera.fy: 516.469215
    Camera.cx: 318.643040
    Camera.cy: 255.313989
    
    Camera.k1: 0.262383
    Camera.k2: -0.953104
    Camera.p1: -0.005358
    Camera.p2: 0.002628
    Camera.k3: 1.163314
    
    # Camera frames per second 
    Camera.fps: 30.0
    
    # Color order of the images (0: BGR, 1: RGB. It is ignored if images are grayscale)
    Camera.RGB: 1
    
    #--------------------------------------------------------------------------------------------
    # ORB Parameters
    #--------------------------------------------------------------------------------------------
    
    # ORB Extractor: Number of features per image
    ORBextractor.nFeatures: 1000
    
    # ORB Extractor: Scale factor between levels in the scale pyramid 	
    ORBextractor.scaleFactor: 1.2
    
    # ORB Extractor: Number of levels in the scale pyramid	
    ORBextractor.nLevels: 8
    
    # ORB Extractor: Fast threshold
    # Image is divided in a grid. At each cell FAST are extracted imposing a minimum response.
    # Firstly we impose iniThFAST. If no corners are detected we impose a lower value minThFAST
    # You can lower these values if your images have low contrast			
    ORBextractor.iniThFAST: 20
    ORBextractor.minThFAST: 7
    
    #--------------------------------------------------------------------------------------------
    # Viewer Parameters
    #--------------------------------------------------------------------------------------------
    Viewer.KeyFrameSize: 0.05
    Viewer.KeyFrameLineWidth: 1
    Viewer.GraphLineWidth: 0.9
    Viewer.PointSize:2
    Viewer.CameraSize: 0.08
    Viewer.CameraLineWidth: 3
    Viewer.ViewpointX: 0
    Viewer.ViewpointY: -0.7
    Viewer.ViewpointZ: -1.8
    Viewer.ViewpointF: 500
    




Other things to consider LSD-SLAM

SVO

DSO

Actually, many people are recommending svo and dso saying orb_slam while the better behaving one, works poorly on the pi

https://github.com/uzh-rpg/rpg_open_remode

OpenSfm

http://theia-sfm.org/

https://arxiv.org/pdf/1701.08493.pdf

https://github.com/uoip/monoVO-python

http://avisingh599.github.io/vision/monocular-vo/

[https://gist.github.com/nickoala/8d7e0bc24be3cec459e63bc1eb8cc858](https://gist.github.com/nickoala/8d7e0bc24be3cec459e63bc1eb8cc858)

Also a perhaps useful ROS short course

https://www.youtube.com/watch?v=0BxVPCInS3M&t;=2745s

Old 6/16:

So I downloaded a cool looking package

[https://github.com/uzh-rpg/rpg_svo](https://github.com/uzh-rpg/rpg_svo)

roslaunch svo_ros live.launch

You need to have a camera running

sudo apt-get install ros-jade-usb-cam

run with

rosrun usb_cam usb_cam_node

You can see it using image_viewer

rosrun image_viewer image_viewer image:=/cam_usb/image_raw

Change the param file in svo_ros so that the camera has the same resolution and stuff
