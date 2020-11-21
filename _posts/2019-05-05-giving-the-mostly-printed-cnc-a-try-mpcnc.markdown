---
author: philzook58
comments: true
date: 2019-05-05 17:48:58+00:00
layout: post
link: https://www.philipzucker.com/giving-the-mostly-printed-cnc-a-try-mpcnc/
slug: giving-the-mostly-printed-cnc-a-try-mpcnc
title: Giving the Mostly Printed CNC a try (MPCNC)
wordpress_id: 1766
categories:
- Robots
tags:
- 3d print
- cnc
- robots
---




[Declan](http://www.declanoller.com) had the good idea to make a CNC machine. There is a popular plan available here 







[https://www.v1engineering.com/specifications/](https://www.v1engineering.com/specifications/)





![](/assets/IMG_3675-e1557077476919-768x1024.jpg)A Doge





The really cute part of it is using electrical conduit as rails, which are shockingly inexpensive. Like a couple bucks for 4 feet! Holy shnikes!







We've been printing up a storm for the last couple weeks. A ton of parts!







We already had a lot of motors and stuff lying around. Declan bought a lot of stuff too just for this. Assorted bearings and bolts. The plans have a bill of materials.





![](/assets/IMG_0634-e1550460314632-768x1024.jpg)



![](/assets/IMG_2563-1-1024x768.jpg)



![](/assets/IMG_3169-e1550460089557-scaled.jpg)



![](/assets/IMG_8133-1024x768.jpg)



![](/assets/IMG_2022-e1550460294609-768x1024.jpg)

















[Repetier host](https://www.repetier.com/) seemed to work pretty well for controlling the board







Used the RAMPS branch of the mpcnc marlin repo







Edited the header files as described in this post so that we could use both extruders as extra x and y  motor drivers. It did not seem like driving two motors from the same driver board was acceptable. Our bearings are gripping the rails a little too tight. It is tough to move.








https://www.v1engineering.com/forum/topic/marlin-using-e-drivers-to-run-2nd-x-and-y-motors/


























Some useful links on the thingiverse version of the mpccnc [https://www.thingiverse.com/thing:724999](https://www.thingiverse.com/thing:724999)













He suggests using this program [http://www.estlcam.com/](http://www.estlcam.com/)  Seem like windows only? ugh.







The mpcnc plans don't contain actual tool mounts but here are some examples







A pen holder: [https://www.thingiverse.com/thing:1612207/comments](https://www.thingiverse.com/thing:1612207/comments)







A dewalt mount: [https://www.thingiverse.com/thing:944952](https://www.thingiverse.com/thing:944952)







This is an interesting web based g-code maker. Ultimately a little to janky though. It works good enough to get started [http://jscut.org/jscut.html](http://jscut.org/jscut.html) . Not entirely clear what pocket vs interior vs whatever is. engrave sort of seemed like what I wanted. Went into inkscape with a reasonable png and traced bitmapped it, then object to path. It's also nice to just find an svg on the internet







The following code was needed to zero repetier and the RAMPS at the touch off point. We added it as a macro. It is doing some confusing behavior though.






    
    
```

G92 X0 Y0 Z0
@isathome
```














pycam is the best I can find for 3d machining. Haven't actually tried it yet







[http://pycam.sourceforge.net/getting-started/](http://pycam.sourceforge.net/getting-started/)







We should probably upgrade the thing to have limit switches. It pains me every time we slam it into the edge.







All in all, a very satisfying project. Hope we build something cool with it. 




<video controls="controls">
  <source type="video/mp4" src="/assets/mpcnc.mp4"></source>
  <p>Your browser does not support the video element.</p>
</video>

![](/assets/mpcnc.mp4)


![](/assets/IMG_1694-e1557077512596-768x1024.jpg)



![](/assets/IMG_6235-e1557077498103-768x1024.jpg)A horsie







