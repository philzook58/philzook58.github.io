---
author: philzook58
comments: true
date: 2015-11-29 02:48:24+00:00
layout: post
link: https://www.philipzucker.com/?p=272
published: false
slug: mbed on the FRDM-K64F
title: mbed on the FRDM-K64F
wordpress_id: 272
---

I've heard whispers (on hackaday. God I love hackaday) about mbed, that maybe its some kind of arduino for big boys. So I bought a Freescale FRDM-K64F board from digikey to check it out.

[https://docs.mbed.com/docs/getting-started-mbed-os/en/latest/](https://docs.mbed.com/docs/getting-started-mbed-os/en/latest/)

Well, I got to

yt build

and it failed. Proabbly because I ignored some of the package installation. I AM NOT A DIRECTION FOLLOWER.



[http://yottadocs.mbed.com/#installing](http://yottadocs.mbed.com/#installing)

Had some problems getting it to work.

Eventually I realized that the old version

    
    <code data-lang="sh" class="language-sh">sudo apt-get install gcc-arm-none-eabi<span class="o">=</span>4.9.3.2015q3-1trusty1</code>


d

needs to be replaced with

    
    <code data-lang="sh" class="language-sh">sudo apt-get install gcc-arm-none-eabi<span class="o">=4.9.3.2015q3-1trusty1</span></code>


I don't see the other version in the repository. Maybe it got replaced?

i guess you want to plugin to the usb port labelled opensda.

I wonder what the other port does?

Yeah, copying and pasting the blinky.bin does seem to make the thing blink. Sweet.

At least the sanity check seems to be up and running.


