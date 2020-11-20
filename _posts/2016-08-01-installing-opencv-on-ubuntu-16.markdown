---
author: philzook58
comments: true
date: 2016-08-01 03:06:47+00:00
layout: post
link: https://www.philipzucker.com/installing-opencv-on-ubuntu-16/
slug: installing-opencv-on-ubuntu-16
title: Installing opencv on ubuntu 16
wordpress_id: 480
---

I'm not finding the intructions hyper easy. I bet sudo apt-get install opencv would work pretty well, but i want some latest features (aruco support in the contrib?)

This is useful

[http://docs.opencv.org/trunk/d7/d9f/tutorial_linux_install.html#gsc.tab=0](http://docs.opencv.org/trunk/d7/d9f/tutorial_linux_install.html#gsc.tab=0)



okay git clone  both the contrib

https://github.com/opencv/opencv_contrib

and the main project directory

i have a fresh installation of ubuntu

First I had a error in the cmake process

sudo apt-get build-dep opencv

I had an error about no sources. Had to uncomment the dep-src lines in /etc/apt/sources.list file. The ran sudo apt-get update. Now it installs a ton

[http://askubuntu.com/questions/496549/error-you-must-put-some-source-uris-in-your-sources-list](http://askubuntu.com/questions/496549/error-you-must-put-some-source-uris-in-your-sources-list)

Running this in the created build directory. Have to adjust the path to modules to suit what you've done

    
    cmake -D CMAKE_BUILD_TYPE=Release -D CMAKE_INSTALL_PREFIX=/usr/local -DOPENCV_EXTRA_MODULES_PATH=../../opencv_contrib/modules ..



    
    make -j7


sudo make install



seems to have installed python bindings. Good.




