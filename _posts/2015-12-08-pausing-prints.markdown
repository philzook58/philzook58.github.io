---
author: philzook58
comments: true
date: 2015-12-08 03:53:26+00:00
layout: post
link: https://www.philipzucker.com/pausing-prints/
slug: pausing-prints
title: Pausing Prints
wordpress_id: 288
---

So we want to be able to pause prints to put stuff in them.

The way to do it is to export gcode from slic3r. Go into repetier's gcode editor tab.

Then you can drag the layer slider until you're where you want a pause.

Show layer range is a nice setting

Click on the button that says last layer to bring yourself to the part of the code

    
    G1 X97.250 Y100.000 E108.68348
    G1 Z22.200 F7800.000


The Z instruction moves up to the next layer.

Insert this little hunk of code inside

    
    G1 X97.250 Y100.000 E108.68348
    
    M117 Do Yo Thang
    G1 X0 Y0&nbsp;
    M0
    G1 X97.251 Y99.986
    
    G1 Z22.200 F7800.000


G1 X0 Y0 sends the head to 0,0 to get it out of the way

M117 Sends a messsage

M0 waits for user response for our prusa i3 with marlin firmware (button press)

The last line returns it to its previous position. Make sure to replace those numbers with the actual numbers you see.

[http://reprap.org/wiki/G-code](http://reprap.org/wiki/G-code)

M226 did not seem to work. Nor did repetier style @pause


