---
author: philzook58
comments: true
date: 2015-09-26 22:14:34+00:00
layout: post
link: https://www.philipzucker.com/getting-going-with-rtl-sdr-a-computer-radio-thingy/
slug: getting-going-with-rtl-sdr-a-computer-radio-thingy
title: Getting Going with RTL-SDR (A computer radio thingy)
wordpress_id: 124
---

Using a Mac kind of adds a little bit of shit to every encounter I have with open-sourcy projects. The really mainstream ones fully support macs, but the sort of off road ones need tweaking and digging, even though by and large OS X is compatible with linux as far as I can tell.

Install macports. I tried using homebrew and failed

    
    port install gqrx


It'll install an explosion of stuff.

run gqrx

select the device.

192000 sample rate

leave the other stuff at 0. Do not yet know what that does

When I change the output device it crashes hard for some reason. Default works though

You can click and right click on numbers to change them

Around 100Mhz you'll see some fm stations

Pick a demodulation. WFM mono or stereo.

[http://www.smittix.co.uk/rtlsdr-up-and-running-in-mac-osx-yosemite-with-gqrx-gnuradio/](http://www.smittix.co.uk/rtlsdr-up-and-running-in-mac-osx-yosemite-with-gqrx-gnuradio/)

[http://gqrx.dk/doc/practical-tricks-and-tips](http://gqrx.dk/doc/practical-tricks-and-tips)



Here's a bunch of garbage that didn't work:

Followed these instructions:

[https://github.com/robotastic/homebrew-hackrf](https://github.com/robotastic/homebrew-hackrf)

build failed on gr-baz. Hmm. Error

    
    Gruel required to compile baz


Tried doing some stuff. Apparently not updated to gnuradio 3.7? Optional So maybe ok.



    
    rtl_test -t


Reported that it can see my stick (A NooElec R820T2 NESDR Mini 2)

Another useful link: [http://blog.opensecurityresearch.com/2012/06/getting-started-with-gnu-radio-and-rtl.html](http://blog.opensecurityresearch.com/2012/06/getting-started-with-gnu-radio-and-rtl.html)

Screw it. i don't know how to get this working. Let's try a different tact.

Fired up my ubuntu virtual machine. Go into settings and add a usb filter for the SDR dongle

    
    sudo apt-get install rtl-sdr
    


https://rwmj.wordpress.com/tag/gnu-radio/

http://www.instructables.com/id/RTL-SDR-FM-radio-receiver-with-GNU-Radio-Companion/step11/Final-remarks/



Alright After some significant hiccups, changing tacts

[https://github.com/roger-/pyrtlsdr](https://github.com/roger-/pyrtlsdr)

    
    pip install pyrtlsdr


I'd bet that one of the previous stages was necessary to get this going.

Checkout demo_waterfall.py. Pretty cool


