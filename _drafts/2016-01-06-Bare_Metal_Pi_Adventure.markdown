---
author: philzook58
comments: true
date: 2016-01-06 03:02:50+00:00
layout: post
link: https://www.philipzucker.com/?p=366
published: false
slug: Bare Metal Pi Adventure
title: Bare Metal Pi Adventure
wordpress_id: 366
---

[https://github.com/dwelch67/raspberrypi](https://github.com/dwelch67/raspberrypi)

[http://www.valvers.com/open-software/raspberry-pi/step01-bare-metal-programming-in-cpt1/](http://www.valvers.com/open-software/raspberry-pi/step01-bare-metal-programming-in-cpt1/)

[http://www.cl.cam.ac.uk/projects/raspberrypi/tutorials/os/](http://www.cl.cam.ac.uk/projects/raspberrypi/tutorials/os/)

Formatted an SD card as FAT32 (used ubuntu program disks. Click on little gear)

[https://github.com/raspberrypi/firmware/tree/master/boot](https://github.com/raspberrypi/firmware/tree/master/boot)

download start.elf and bootcode.bin from here and put on sd card

https://launchpad.net/gcc-arm-embedded

Install gcc toolchain on ubuntu with

    
    sudo add-apt-repository ppa:team-gcc-arm-embedded/ppa
    sudo apt-get update
    sudo apt-get install gcc-arm-embedded


Got an error about broken pipe trying to overwrite some crap Found workaround

    
    <code>sudo apt-get -o Dpkg::Options::="--force-overwrite" install gdb-arm-none-eabi`</code>


git cloned the bare metal examples directory

ran make in blinker01 and copied blinker01.bin to card as kernel.img

Seems to work. Coo.

Yeah. Changed the timing in blinker01.c to 0x700000 and now it is off longer than it is on.

Setting the pin turns the led off.

clearing turns it on.




