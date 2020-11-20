---
author: philzook58
comments: true
date: 2015-08-31 03:50:13+00:00
layout: post
link: https://www.philipzucker.com/installing-icestorm-on-a-mac/
slug: installing-icestorm-on-a-mac
title: Installing icestorm on a mac
wordpress_id: 109
---

So I caught a hiccup

You need to install Xcode probably

Firstoff, you need to install libusb

brew install libusb1

make and install libftdi from source

http://www.intra2net.com/en/developer/libftdi/download.php

brew install python3



brew install gnu-sed

brew install gawk

brew install mercurial

brew install bison

go to icestorm website

Run all the the commands. like it says. Maybe you'll find more packages that you need installed that I had already. Look at the error and brew install some guesses.

Here's a kicker, go into the makefile for the iceprog and add a 1 to the end of -lftdi so it becomes -lftdi1

I changed the Makefile in iceprog to have the following stuff. I don't think my libftdi was installing where expected by default

LDLIBS = -L/usr/local/lib -L/usr/lib -lftdi1 -lm
CFLAGS = -MD -O0 -ggdb -Wall -std=c99 -I/usr/include/libftdi1
DESTDIR = /usr/local

I guess cc automatically peels lib off the front. Go fig.

Okay. Cool.

Then I git cloned the repository from the hackaday tutorial to see if I could get it to run

http://hackaday.com/2015/08/27/learning-verilog-for-fpgas-hardware-at-last/

./build.sh demo

I got the error

Can't find iCEstick USB device (vedor_id 0x0403, device_id 0x6010).

D'oh.

Well.

brew install lsusb

used lsusb. I can see it right there. The computer can see the thing.

Apparently i think the arduino drivers I have installed previously conflicted with libftdi or something, so I had to unload them


kextstat | grep FTD




Copy and paste the names you find to unload the ftdi devices




sudo kextunload -b com.FTDI.driver.FTDIUSBSerialDriver




sudo kextunload -b com.apple.driver.AppleUSBFTDI




finally I got blinking lights.




Jesus.
