---
author: philzook58
comments: true
date: 2017-09-04 17:54:25+00:00
layout: post
link: https://www.philipzucker.com/limesdr-gettin-going/
slug: limesdr-gettin-going
title: LimeSDR, gettin going
wordpress_id: 694
---



I had trouble installing the ppa the first time I tried about a month ago. It seemed to go through the second time around

Install LimeSuite using the ppa instructions for ubuntu. I have 16.04

https://wiki.myriadrf.org/Lime_Suite

lsusb shows OpenMoko as the device. Odd.

https://wiki.myriadrf.org/LimeSDR_Quick_Start



Ok. A capitalized command LimeSuiteGUI is insane. No commands are capitalized.

It brings up some spaceship of cryptic options.

Some of the stuff in the top menu bar seems good. Connecting, Programming, FFT, etc.

The commands

LimeUtil --info

LimeUtil --find

Lists a device. So that's good. Also does updating?



Added a myriad RF ppa for gnuradio

https://wiki.myriadrf.org/Packaging

sudo apt-get install gnuradio gnuradio-dev

Also installed gqrx. This is very useful for determining if the goddamn thing is working at all

http://gqrx.dk/download/install-ubuntu





Ok. GQRX was crashing on boot.

So was gnuradio when I tried playing with the osmocom source

GNU C++ version 5.4.0 20160609; Boost_105800; UHD_003.010.001.001-release

ImportError: /usr/lib/python2.7/dist-packages/gnuradio/uhd/_uhd_swig.x86_64-linux-gnu.so: undefined symbol: _ZN3uhd4usrp10multi_usrp7ALL_LOSB5cxx11E

so did python

from gnuradio import uhd

Eventually I apt get installed libuhd-dev which makes gqrx run now with an rtl-sdr

gqrx with line

**soapy=0,driver=lime**

should work but didn't



Hmm another twist

Limesdr is power hungry

I may not have a usb3 port on my 2012 desktop insane as that sounds

so i need external power? I wonder if that is what the blinking led signifies



Trying to install in windows now. Maybe that will work better

Install PothosSDR

After running zadig can recognize an rtl-sdr in gqrx

https://wiki.myriadrf.org/Lime_Suite#USB_driver

Install the drivers as specified for limesdr.

I accidentally installed the x86 instead of the x64 drivers and needed to uninstall with deletion and then reinstall properly. Got error code 48

It appears to be working.

https://wiki.myriadrf.org/LimeSDR-USB_Quick_Test

GQRX opens.





It has been months since I tried in ubuntu 16.04. Maybe things have gotten better.

ok. At first gqrx wouldn't load but after fiddling with the sampling and bandwidth it does. I don't get any FM signals with nothing attached to the Lime. That is either good or bad. It does appear to be receiving data at least though.



So I have not gotten gqrx to actually receive signals with limesdr, but gnuradio appears to be working to some degree. This graph plays audio on 101.5 although very crappily. I hope it just needs filtering (I think I should be low passing those resamplers. Also I probably shouldn't be receiving on the middle of the band where the DC spike is). I doubled the resampler because a single resampler through an error for too much decimation. Is this standard procedure?

![simple_lime_fm-grc](http://www.philipzucker.com/wp-content/uploads/2017/09/simple_lime_fm.grc_.png)

Useful gnuradio tutorials

http://files.ettus.com/tutorials/labs/Lab_1-5.pdf

Possibly useful blog series

https://myriadrf.org/blog/limesdr-made-simple-part-4-pothos-beyond/



ok. Next step is simple transmit and receive






