---
author: philzook58
comments: true
date: 2017-08-21 15:16:05+00:00
layout: post
link: https://www.philipzucker.com/gstreamer/
slug: gstreamer
title: Gstreamer
wordpress_id: 790
---

gstreamer is tinker toys for putting together media applications. Very reminiscent of gnuradio although it doesn't have a nice gui editor. You smash together a bunch of blocks

It keeps coming up so I am looking into it more.

https://gstreamer.freedesktop.org/documentation/installing/on-linux.html

sudo apt install libgstreamer1.0-dev

copy example

https://gstreamer.freedesktop.org/documentation/tutorials/basic/hello-world.html#

gcc hello_gstream.c `pkg-config --cflags --libs gstreamer-1.0`

v4l2src is the webcam source of the /dev/video0 device

<del>apt-get install gstreamer0.10-ffmpeg</del>

<del>gst-launch-1.0 -v \</del>
<del> v4l2src \</del>
<del> ! qtdemux \</del>
<del> ! h264parse \</del>
<del> ! ffdec_h264 \</del>
<del> ! ffmpegcolorspace \</del>
<del> ! x264enc \</del>
<del> ! rtph264pay \</del>
<del> ! udpsink host=127.0.0.1 port=5000</del>

helpful idiom

gst-inspect | grep "h264"

This let me view my webcam

gst-launch-1.0 -v v4l2src device=/dev/video0 ! video/x-raw,framerate=30/1,width=1280,height=720 ! xvimagesink

The video/x-raw is a "cap", a capability, kind of defining the type of video flowing through. It isn't a conversion step as I understand it. It is telling the graph which of the possible types of video available you've picked (your webcam can just be told to give you different stuff).

Ugh. The gstreamer elements are super useful, but where is an organized list of them. The manual just has a big dump. Most of these are probably not useful.

https://gstreamer.freedesktop.org/documentation/plugins.html

videoconvert sounds like a good one

There are some fun opencv and opengl ones. Like face detection or wacky effects. Handdetect is a curious one

fakesrc for testing

special sinks for os x -  [osxvideosink](https://gstreamer.freedesktop.org/data/doc/gstreamer/head/gst-plugins-good-plugins/html/gst-plugins-good-plugins-osxvideosink.html)

playbin for playing from a uri

[x264enc](https://gstreamer.freedesktop.org/data/doc/gstreamer/head/gst-plugins-ugly-plugins/html/gst-plugins-ugly-plugins-x264enc.html) - encodes into h264

uvch264 - gets a h264 stream right from the webcam

http://oz9aec.net/software/gstreamer/using-the-logitech-c920-webcam-with-gstreamer-12

Or you can just change the parameter to v4l2src to output h264. Ok this is not working on my webcam. I get

ERROR: from element /GstPipeline:pipeline0/GstV4l2Src:v4l2src0: Internal data flow error.

instead

gst-launch-1.0 -v v4l2src device=/dev/video0 ! video/x-raw,framerate=30/1,width=640,height=480 ! x264enc tune=zerolatency !  h264parse ! avdec_h264 ! xvimagesink

encodes h264 and then decodes it. May want to change that zerolatency to another setting option. Maybe?

    
    rc<span class="gtkdoc opt">-</span>lookahead<span class="gtkdoc opt">=</span><span class="number">5</span>


https://gstreamer.freedesktop.org/data/doc/gstreamer/head/gst-plugins-ugly-plugins/html/gst-plugins-ugly-plugins-x264enc.html

okay continuing ahead with the streaming. I can't get h264 to stream. It gives a ERROR: from element /GstPipeline:pipeline0/GstVideoTestSrc:videotestsrc0: Internal data flow error. when combined with the stock example code

GARBAGE. DO NOT USE.

    
    gst-launch-1.0 rtpbin name=rtpbin \
    v4l2src device=/dev/video0 ! video/x-raw,framerate=30/1,width=640,height=480 ! queue ! x264enc tune=zerolatency ! rtph264pay ! rtpbin.recv_rtp_sink_0 \
    rtpbin.send_rtp_src_0 ! udpsink port=5000                            \
    rtpbin.send_rtcp_src_0 ! udpsink port=5001 sync=false async=false    \
    udpsrc port=5005 ! rtpbin.recv_rtcp_sink_0


https://gstreamer.freedesktop.org/data/doc/gstreamer/head/gst-plugins-good-plugins/html/gst-plugins-good-plugins-rtpbin.html

However. using h263 it does work. Needed to change ffenc to avenc from their example and ffdec to avdec

Sending

    
    gst-launch-1.0 rtpbin name=rtpbin \
            v4l2src ! videoconvert ! avenc_h263 ! rtph263ppay ! rtpbin.send_rtp_sink_0 \
                      rtpbin.send_rtp_src_0 ! udpsink port=5000                            \
                      rtpbin.send_rtcp_src_0 ! udpsink port=5001 sync=false async=false    \
                      udpsrc port=5005 ! rtpbin.recv_rtcp_sink_0


receiving

    
    gst-launch-1.0 -v rtpbin name=rtpbin \
    udpsrc caps="application/x-rtp,media=(string)video,clock-rate=(int)90000,encoding-name=(string)H263-1998" \
    port=5000 ! rtpbin.recv_rtp_sink_0 \
    rtpbin. ! rtph263pdepay ! avdec_h263 ! xvimagesink \
    udpsrc port=5001 ! rtpbin.recv_rtcp_sink_0 \
    rtpbin.send_rtcp_src_0 ! udpsink port=5005 sync=false async=false


for receiving on my macbook


gst-launch-1.0 -v rtpbin name=rtpbin \




    
    udpsrc caps="application/x-rtp,media=(string)video,clock-rate=(int)90000,encoding-name=(string)H263-1998" \
    
    port=5000 ! rtpbin.recv_rtp_sink_0 \
    
    rtpbin. ! rtph263pdepay ! avdec_h263 ! videoconvert ! osxvideosink \
    
    udpsrc port=5001 ! rtpbin.recv_rtcp_sink_0 \
    
    rtpbin.send_rtcp_src_0 ! udpsink host=192.168.1.12 port=5005 sync=false async=false


you need to specify a host for the udpsinks to get the video on another computer.

I would estimate the latency at 1/4 second maybe. Much better than other things I've tried.

okay default latency on rtpbin is 200ms.

on receiving side set latency=0 as an option to rtpbin (not totally sure if transmitting side should have it too.)

I wonder how bad that will fail in the event of packet loss? It's probably not a good setting for some circumstances, but for a non-critical application on a LAN it seems pretty good.

I think the latency might have crept up a bit over a minute. Not too bad though.

https://github.com/GStreamer/gst-rtsp-server

Update 3/12/19:

Mark has some interesting notes on using gstreamer to streaming. He reported a better latency.

http://markmaz.com/mambo_notes/
