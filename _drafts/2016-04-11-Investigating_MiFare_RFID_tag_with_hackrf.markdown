---
author: philzook58
comments: true
date: 2016-04-11 03:21:17+00:00
layout: post
link: https://www.philipzucker.com/?p=426
published: false
slug: Investigating MiFare RFID tag with hackrf
title: Investigating MiFare RFID tag with hackrf
wordpress_id: 426
---

https://github.com/miguelbalboa/rfid

adding to the example sketch in the loop

    
    mfrc522.PCD_AntennaOn();
    delay(500);
    mfrc522.PCD_AntennaOff();
    delay(500);


This pulses the Tx antenna on and off.

I read in the datasheet 40 ohms? Maybe this is the impedance of the setup. If so, maybe cutting the traces and hooking striaght up





Check out this. We can read out some hackrf to a file and inspect it with inspectrum using the following commands.

https://greatscottgadgets.com/sdr/11/

    
    <a href="http://sox.sourceforge.net/">hackrf_transfer -r foo.s8 -f 13560000 -n 10000000
    sox</a> foo.s8 foo.f32
    inspectrum foo.32






Using a little loop antenna about 1cm in diameter with about 6 turns.

Right in top of the thing with no gain you can see the signal at -36db

There are 4 turns in a square coil of length about 4cm






