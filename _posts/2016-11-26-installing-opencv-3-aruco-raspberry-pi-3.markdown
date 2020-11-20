---
author: philzook58
comments: true
date: 2016-11-26 22:26:47+00:00
layout: post
link: https://www.philipzucker.com/installing-opencv-3-aruco-raspberry-pi-3/
slug: installing-opencv-3-aruco-raspberry-pi-3
title: Installing OpenCV 3 for Aruco on a Raspberry Pi 3
wordpress_id: 576
tags:
- raspberry pi opencv
---

Basically followed these instructions

http://www.pyimagesearch.com/2016/04/18/install-guide-raspberry-pi-3-raspbian-jessie-opencv-3/

Except! Don't get his suggested zips. They did not work since they were to old to have aruco. I did this and there was only the dictionary of constants and none of the functions in cv2.aruco.

Here's a script that is basically compiled from the page, except git cloning the opencv directories.

Put this into a install_opencv.sh and run

    
    chmod +x install_opencv.sh


then run the script

    
    sudo apt-get update
    sudo apt-get upgrade
    sudo apt-get install -y build-essential cmake pkg-config
    sudo apt-get install -y libjpeg-dev libtiff5-dev libjasper-dev libpng12-dev
    sudo apt-get install -y libavcodec-dev libavformat-dev libswscale-dev libv4l-dev
    sudo apt-get install -y libxvidcore-dev libx264-dev
    sudo apt-get install -y libgtk2.0-dev
    sudo apt-get install -y libatlas-base-dev gfortran
    sudo apt-get install -y python2.7-dev python3-dev
    cd ~
    #wget -O opencv.zip https://github.com/Itseez/opencv/archive/3.1.0.zip
    #unzip opencv.zip
    #wget -O opencv_contrib.zip https://github.com/Itseez/opencv_contrib/archive/3.1.0.zip
    #unzip opencv_contrib.zip
    git clone https://github.com/opencv/opencv.git
    git clone https://github.com/opencv/opencv_contrib.git
    pip install numpy
    cd ~/opencv
    mkdir build
    cd build
    cmake -D CMAKE_BUILD_TYPE=RELEASE \
        -D CMAKE_INSTALL_PREFIX=/usr/local \
        -D INSTALL_PYTHON_EXAMPLES=ON \
        -D OPENCV_EXTRA_MODULES_PATH=~/opencv_contrib/modules \
        -D BUILD_EXAMPLES=ON ..
    
    make -j4
    sudo make install
    sudo ldconfig


This process takes a while. However the early stages might still ask you stuff so get into the cloning before you leave it be for a couple hours. OpenCV is pretty big. I think it's using 40% of a 8gb SD card, so plan accordingly. I think you can delete the clone directories once it's installed.
