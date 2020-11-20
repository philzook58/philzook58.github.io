---
author: philzook58
comments: true
date: 2018-03-03 23:03:34+00:00
layout: post
link: https://www.philipzucker.com/trying-platform-io/
slug: trying-platform-io
title: Trying Platform.io
wordpress_id: 698
---

http://hackaday.com/2017/04/07/platformio-and-visual-studio-take-over-the-world/

http://platformio.org/

Somehow I was not aware of this thing. It is a build tool for microcontrollers

Seems like people basically like it. 1000+ stars on github

python -m pip install -U platformio



make a folder

platformio init --board icestick

Holy crap. Is this thing going to download and setup the tools? THAT. IS. AWESOME. If it works.

Better yet clone this bad boy

https://github.com/platformio/platformio-examples

https://github.com/platformio/platformio-examples/tree/develop/lattice_ice40/lattice_ice40-leds

go to the blink folder.

platformio run

platformio run --target upload

Holy. Hell. It worked. THAT IS NUTS.

The commands it ran to compile

    
    yosys -p "synth_ice40 -blif .pioenvs/icestick/hardware.blif" -q src/counter.v
    arachne-pnr -d 1k -P tq144 -p /home/philip/Documents/platformio-examples/lattice_ice40/lattice_ice40-counter/src/counter.pcf -o .pioenvs/icestick/hardware.asc .pioenvs/icestick/hardware.blif
    


Hmm. I'm puzzled. Where did this come from? How did it know counter.v?



Mecrisp has an icestick version. Intriguing (Mecrisp is a forth implementation)





https://github.com/platformio/platform-lattice_ice40/tree/develop/examples/leds

had to sudo apt install libreadline6 and gtkwave to run simulation

I had to follow these instructions to get the FTDI device to work

https://stackoverflow.com/questions/36633819/iceprog-cant-find-ice-ftdi-usb-device-linux-permission-issue

and change the platformio.ini file to say icestick instead of icezum. Actually i don't think that is necessary.






