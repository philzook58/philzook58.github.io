---
author: philzook58
comments: true
date: 2017-09-26 00:31:58+00:00
layout: post
link: https://www.philipzucker.com/?p=891
published: false
slug: BeagleBone PRU
title: BeagleBone PRU
wordpress_id: 891
---

The PRU (programmable real time unit) is something that has been on my to do list for a while. They are processors on the Beaglebone that can be independently programmed and talked to while the main processor is running linux. Supposedly you can toggle a pin at 200Mhz using these PRUs.



plug the beaglebone into your usb port

you can ssh in  with

ssh root@beaglebone.local

[http://www.righto.com/2016/08/pru-tips-understanding-beaglebones.html](http://www.righto.com/2016/08/pru-tips-understanding-beaglebones.html)

This is good. Just blindly follow it.

I had to comment out the load data section in the c coade to get it to compile. I have old version of prussdrv.h?









http://processors.wiki.ti.com/index.php/PRU_Training:_Hands-on_Labs

pasm is the pru assembler

https://github.com/beagleboard/am335x_pru_package

http://wiki.thing-printer.com/index.php?title=PyPRUSS_on_BeagleBone


