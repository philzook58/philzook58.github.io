---
author: philzook58
comments: true
date: 2015-09-17 14:08:25+00:00
layout: post
link: https://www.philipzucker.com/ngspice-huh/
slug: ngspice-huh
title: ngspice, huh
wordpress_id: 166
---

Got tipped off to ngspice. Circuit simulation. Not bad. Can't get it to graph properly on my computer though. I vastly prefer specifying the circuit in a file to specifying it in a schematic. That sucked.

[http://www.ngspice.com](http://www.ngspice.com)

is a solid online doohickey

    
    **** Sweet LC Circuit ***
    
    *element type is designated by first letter
    *format is node node value
    L1 0 1 1mH
    C1 0 1 1uC
    R1 1 0 1000
    
    *vs 2 0 DC 1 sin(0 1 5.032e3)
    
    *set icitial conditions for v1
    .ic v(1)=1
    
    *Do transient analysis and plot from 1ms to 2ms
    .TRAN 10us 2mS 1mS
    .plot tran v(1)
    
    *Gotta end stuff
    
    .end


Hypothetically this is a copy of that code. Wonder how long that'll last

[http://www.ngspice.com/index.php?public_circuit=T6XqVE](http://www.ngspice.com/index.php?public_circuit=T6XqVE)

Axebot Lives.


