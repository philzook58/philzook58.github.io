---
author: philzook58
comments: true
date: 2016-01-22 01:42:40+00:00
layout: post
link: https://www.philipzucker.com/?p=379
published: false
slug: Bus pirate and Jtag and Logic Analyzer
title: Bus pirate and Jtag and Logic Analyzer
wordpress_id: 379
---

I'm fascinated by hardware hacking. I want to understand.

Things to look into in the future: GoodFET, busblaster

I had a bus pirate from way back. I installed the new firmware 6.1 to get jtag support. It isn't always supported from the commandline as was suggested by this useful post

[http://cybermashup.com/2014/05/01/jtag-debugging-made-easy-with-bus-pirate-and-openocd/](http://cybermashup.com/2014/05/01/jtag-debugging-made-easy-with-bus-pirate-and-openocd/)

    
    screen /dev/ttyUSB0 115200 8N1


gets you into bus pirate

m lists protocols

i gives info





ctrl-a ? will give a list of screen commands.

ctrl-a is the general escape sequence

ctrl-a d gets you out. Not sure if this is always the best way. I believe that will leave anything running that was there

I've heard of two fellaa in the context of jtag,

openocd and urjtag

sudo apt-get install openocd




