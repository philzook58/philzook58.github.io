---
author: philzook58
comments: true
date: 2016-11-22 06:09:18+00:00
layout: post
link: https://www.philipzucker.com/pipe-raspberry-pi-video-ffmpeg-opencv/
slug: pipe-raspberry-pi-video-ffmpeg-opencv
title: 'Pipe Raspberry Pi Video into ffmpeg and opencv: A Failure So Far'
wordpress_id: 558
tags:
- raspberry pi
---







Trying to get video off of raspberry pi in a low latency way.

Edit:

As mentioned in the comments, we tried using uv4l. Installed as per the instructions, but the streaming tutorial is not working right. vlc complains about not being able to open /dev/video0

This helped a bit

We were able to get a pretty low latency link in the browser

http://blog.cudmore.io/post/2016/06/05/uv4l-on-Raspberry-Pi/

To Be continued



Piping raspivid through netcat as suggested in raspicam documentation

    
    raspivid -t 0 -w 640 -h 480 -hf -ih -fps 20 --rotation 180 -o - | nc -k -l 2222


Mplayer does a decent job. Maybe 0.1 second latency. Pretty dang good.

VLC did not do so good. Maybe 3 second latency. Perhaps some fiddling would fix?

Eventually, we want the stream in a program somewhere, hopefully python is acceptably fast. Here is a site that I heavily cribbed from

[http://zulko.github.io/blog/2013/09/27/read-and-write-video-frames-in-python-using-ffmpeg/](http://zulko.github.io/blog/2013/09/27/read-and-write-video-frames-in-python-using-ffmpeg/)

The colors are screwed up. This is not fast enough for our purposes. If you want, I believe you can fix it with cv2.cvtColor

You can see that I've tried a bunch of ffmpeg tags but none seem to help.

It does not appear that python is the speed hangup. I inspected with python -m cProfile

    
    import subprocess as sp
    
    FFMPEG_BIN = "ffmpeg" # on Linux ans Mac OS
    #-i tcp://192.168.0.15:2222
    command = [ FFMPEG_BIN,
    			'-i', 'tcp://192.168.0.15:2222',
    		#	'-f', 'image2pipe',
    			'-f', 'rawvideo',
    			'-tune', 'zerolatency',
    			'-fflags', 'nobuffer',
    			'-preset','ultrafast',
    			'-pix_fmt', 'rgb24',
    			'-vcodec', 'rawvideo', '-']
    pipe = sp.Popen(command, stdout = sp.PIPE, bufsize=10**8)
    
    import numpy
    # read 420*360*3 bytes (= 1 frame)
    width = 640
    height = 480
    
    
    import cv2
    
    
    while(True):
    	# Capture frame-by-frame
    	raw_image = pipe.stdout.read(width*height*3) #takes 0.15 secs per call.  
    	# transform the byte read into a numpy array
    	image =  numpy.fromstring(raw_image, dtype='uint8')
    	image = image.reshape((height,width,3))
    	# throw away the data in the pipe's buffer.
    	pipe.stdout.flush()
    
    	# Display the resulting frame
    	cv2.imshow('frame',image)
    	if cv2.waitKey(1) & 0xFF == ord('q'): #takes about 0.05 secs per call. Work out to 5 fps.
    		break
    
    cv2.destroyAllWindows()





