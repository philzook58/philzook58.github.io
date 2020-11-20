---
author: philzook58
comments: true
date: 2018-03-02 04:43:37+00:00
layout: post
link: https://www.philipzucker.com/linksprite-cnc-machine/
slug: linksprite-cnc-machine
title: Linksprite CNC machine
wordpress_id: 614
---

I'm impressed with the package in the box. Well organanized.

Putting it together took maybe 4 hours, half watching The Wire.

The x-axis screw is not fitting. I'm hoping the end is just ground incorrectly.

Nope. This has been a huge pain. They sent me the wrong screw. There are 8mm 4mm and 2mm pitch T8 rods. They have 1 2 and 4 starts to their threading. I have bought the maximal number of incorrect rods. I now have in posession the 4mm pitch rod I need. Figuring this out has set me back a month and another 30$. I am annoyed.

There is a crack in the z-axis printed part. Epoxy should fix it.

open up arduino serial monitor

115200 baud both NL & CR

    
    $$ (view Grbl settings)
    $# (view # parameters)
    $G (view parser state)
    $I (view build info)
    $N (view startup blocks)
    $x=value (save Grbl setting)
    $Nx=line (save startup block)
    $C (check gcode mode)
    $X (kill alarm lock)
    $H (run homing cycle)
    ~ (cycle start)
    ! (feed hold)
    ? (current status)
    ctrl-x (reset Grbl)
    




Hmm. LinuxCNC is more complicated than I thought. It seems installing it on my regular ubuntu 14.04 is not an option without a lot of dangerous futzing. Uses a real-time special kernel.

http://linuxcnc.org/docs/devel/html/code/building-linuxcnc.html

whenever it didn't work i apt-get installed whatever was missing.

I also had to add a non redistributable when that error came up.

make







Two Control Guys. One in python one in java

https://github.com/vlachoudis/bCNC

https://github.com/winder/Universal-G-Code-Sender



Pycam and Blendercam do 3d models. Pycam appears to be defunct

http://pycam.sourceforge.net/

go to folder and make.

The website seems wrong. The links aren't.

Build error

https://sourceforge.net/p/pycam/mailman/pycam-devel/

    
    I added
    #include <stddef.h>
    to Edge.h.






http://blendercam.blogspot.com/



Pcb

https://github.com/pcb2gcode/pcb2gcode



Inkscape gcodetools.

https://github.com/cnc-club/gcodetools#gcodetools

https://www.norwegiancreations.com/2015/08/an-intro-to-g-code-and-how-to-generate-it-using-inkscape/



Openscam (now called camotics?) is a path simulator.



http://jscut.org/



S1000 sets the spindle speed

M3 turns spindle on

M5 turns off

even 0.2 depth is a little deep

home. reset

turn on the spindle


