---
author: philzook58
comments: true
date: 2015-09-03 14:16:05+00:00
layout: post
link: https://www.philipzucker.com/havin-some-problems-with-beaglebone/
slug: havin-some-problems-with-beaglebone
title: Havin' Some Problems with Beaglebone
wordpress_id: 113
---

When I turned on the beaglebone black and saw that it served its own IDE, I was immensely pleased. Also Javascript! Language of the future (Not necessarily due to inherent qualities, but due to it's adoption as a langua fraca. There is no easier toolchain to get going)!

However things turned to shit and now I'm a little more hesitant to embrace dat bone.

The pin headers are too long and unmarked. It's a pain to count from the side to find the pin you need. Especially since the pins have different functionality. Not all pins are PWM for example.

A problem that took forever was getting the xbox controller to work really properly. Apparently some kind of EMI was occurring. `dmesg|grep usb` had some business about babble. Found a forum post that said to use a hub or usb extender and then you'll be find. Used an usb extender and it worked. Bizarre.

For some unknown reason I had difficulty getting more than 2 PWM to works. It spit mysterious messages about device trees (which apparently are important. A lot of things in this world are important.).

I went into uEnv.txt in the boot folder and started disabling stuff. My hypothesis was that the pins being configured for other purposes that was blocking their use.

First I uncommented the line to disable HDMI. Then, I accidentally bricked the beaglebone by uncommenting a line in uEnv.txt that enables eMMC which is where the beaglebone boots from. I am an idiot.

I unbricked it by loading the debian image onto a microSD. Not a big deal except for the scary factor. I do not like formatting things. Especially not with sudo. Also, I did not have a microSD card handy and had to wait for one.

I essentially followed the instructions here [https://www.raspberrypi.org/documentation/installation/installing-images/mac.md](https://www.raspberrypi.org/documentation/installation/installing-images/mac.md)

replacing the raspberry pi image with the beaglebone image. dd is an odd duck. I used /dev/disk3 rather than /dev/rdisk3 which might explain why it took so goddamn long. Apparently one is buffered and the other isn't.

So yeah. I love having the beef of a full linux on board stuff. Really I think control from an xbox controller would have been unfeasible natively on an arduino (don't quote me on that. Never actually looked. I've heard the Leonardo can do usb stuff maybe). But for simple purposes I think you're better off with an arduino controlled over serial. Could just then make some python program to accept the xbox controller on a host computer. Check out this clever snippet for a simple Serial protocol. Then you can type in numbers followed by a letter for various commands. The - '0' thing is because the numbers come in sequential order in ascii.

I could type into the serial console

123a

And then it would set servo a to 123 degrees.

    
    if ( Serial.available()) {
    char ch = Serial.read();
    
    switch(ch) {
    case '0'...'9':
    //Pretty goddamn clever right here. Not mine.
    v = v * 10 + ch - '0';
    break;
    case 'a':
    servoA.write(v);
    v = 0;
    break;
    case 'b':
    servoA.write(v);
    v = 0;
    break;
    }
    }






Also,  update on the h-bridge:

It caught on fire.






