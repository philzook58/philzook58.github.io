---
author: philzook58
comments: true
date: 2017-02-09 22:46:43+00:00
layout: post
link: https://www.philipzucker.com/opencv-android/
slug: opencv-android
title: OpenCV Android
wordpress_id: 622
---

https://www.youtube.com/watch?v=nv4MEliij14

https://www.learn2crack.com/2016/03/setup-opencv-sdk-android-studio.html

A summary of the video

Get the SDK from opencv.org

Make new project with regular settings

new > import module

select java folder in sdk folder

got an erro

had to install android-sdk by clickign isntall missing platforms

copy all stuff from native > libs into a JNILibs folder by dragging and dropping

Changed the SDK version to after 21 to remove camera2 error

android.usedeprecatedNDK

I was having an NDK error

Go to tools > SDK manager and download cmake lldb and ndk

https://developer.android.com/ndk/guides/index.html

still have errors.

http://stackoverflow.com/questions/27453085/execution-failed-for-task-appcompiledebugndk-failed-to-run-this-command-ndk

Have to go into files as far as I can tell. This gradle isn't around
