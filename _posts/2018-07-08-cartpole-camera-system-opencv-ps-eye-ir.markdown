---
author: philzook58
comments: true
date: 2018-07-08 20:38:02+00:00
layout: post
link: https://www.philipzucker.com/cartpole-camera-system-opencv-ps-eye-ir/
slug: cartpole-camera-system-opencv-ps-eye-ir
title: Cartpole Camera System - OpenCV + PS EYE + IR
wordpress_id: 1149
tags:
- mocap
- opencv
- pseye
---

We tried using colored tape before. It was okay after manual tuning, but kind of sucked. Commerical motion tracking systems use IR cameras and retroreflectors.




We bought some retroreflective tape and put it on the pole. [http://a.co/0A9Otmr](http://a.co/0A9Otmr)




We removed our PS EYE IR filter. The PS EYE is really cheap (~7$) and has a high framerate mode (100+ fps). People have been using it for a while for computer vision projects.




[http://wiki.lofarolabs.com/index.php/Removing_the_IR_Filter_from_the_PS_Eye_Camera](http://wiki.lofarolabs.com/index.php/Removing_the_IR_Filter_from_the_PS_Eye_Camera)




We followed the instructions, but did not add the floppy disk and sanded down the base of the lens to bring the image back into focus.




We bought an IR LED ring light which fit over the camera with the plastic cover removed and rubber banded it in place.




[http://a.co/2sGUY08](http://a.co/2sGUY08)




If you snip the photoresistor it is always on, since the photoresistor is high resistance in the dark. We used a spare 12V power supply that we soldered a connector on for.




We had also bought an IR pass filter on amazon, but it does not appear to help.




Useful utilties: qv4l2, v4l2-ctl and v4l2-utils. You can change lots of stuff.




qv4l2 -d 1 is very useful for experiementation




Useful options to v4l2-ctl : -d selects camera, -p sets framerate -l gives a list of changeable options. You have to turn off the automatic stuff before it becomes changeable. Counterintuitively auto-exposure seems to have 1 as off.




There has been a recent update to opencv to let the v4l2 buffer size be changed. We're hoping this will really help with our latency issues




A useful blog. We use v4l2-ctl for controlling the exposure programmatically




[http://www.jayrambhia.com/blog/capture-v4l2](http://www.jayrambhia.com/blog/capture-v4l2)




Oooh. The contour method + rotated rectangle is working really well for matching the retroreflective tape.




[https://docs.opencv.org/3.3.1/dd/d49/tutorial_py_contour_features.html](https://docs.opencv.org/3.3.1/dd/d49/tutorial_py_contour_features.html)




You need to reduce the video size to 320x240 if you want to go to the highest framerate of 187fps







In regards to the frame delay problem from before, it's not clear that we're really seeing it? We are attempting both the screen timestamp technique and also comparing to our rotary encoder. In the screen timestamp technique, it is not so clear that what we measure there is latency, and if it is, it includes the latency of the monitor itself, which is irrelevant.




[![img_5311](http://philzucker2.nfshost.com/wp-content/uploads/2018/07/IMG_5311.jpg)](http://philzucker2.nfshost.com/wp-content/uploads/2018/07/IMG_5311.jpg) [![img_2511](http://philzucker2.nfshost.com/wp-content/uploads/2018/07/IMG_2511-e1531081718210.jpg)](http://philzucker2.nfshost.com/wp-content/uploads/2018/07/IMG_2511-e1531081718210.jpg)







![](http://philzucker2.nfshost.com/wp-content/uploads/2020/03/image-2.png)



![](http://philzucker2.nfshost.com/wp-content/uploads/2020/03/image-1.png)

