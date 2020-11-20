---
author: philzook58
comments: true
date: 2016-12-29 20:23:47+00:00
layout: post
link: https://www.philipzucker.com/fpga-renaissance/
slug: fpga-renaissance
title: FPGA renaissance
wordpress_id: 598
---

FPGA are at the locus of converging interests.



 	
  1. OS, assembly and the roots

 	
  2. Software define radio

 	
  3. Camera stuff, opencv, computer vision

 	
  4. Haskell, Programming languages and Clash. Functional programming hardware. Forth.

 	
  5. Electronics (Sonar? etc?). Getting a CNC soon for circuit board cutting. Can a crytsal oscillator be used as an ultrasound transducer?

 	
  6. Some physics-y inspired questions about boolean logic looking frustrated fields. Kagome lattice of clocked not gates (or unclocked)? Topological excitations? Edge modes?


FPGA is on the periphery of all of these topics.

I've started going through Bruce land's Cornell Fpga videos. Really good. Seems like the guy knows his stuff.

I bought a super mega cheapo fpga in the past and spent days getting the legacy tool chain running. I think I've done this twice on two separate computers.

I did the same for the Lattice icestick on my macbook.

These may have been huge mistakes sapping my enthusiasm. Because at that point I just had no desire left to explore.

I've been stalled out, waiting a year for my snickerdoodle. Tempted to buy another zynq board.

I booted up my cheapo board again and got some blinking and did a NIOS tutorial. At the end though, the board doesn't have enough oomph to run a NIOS program. Maybe I can finesse it, or I've done something really stupid, but I've seen suggestions of 50 M4K blocks of memory and my board has only 26.

So, I just bought a couple of boards on aliexpress. They are closer to real dev boards with some actual peripheries like built in vga, ps2, some ram, buttons, displays, and with newer chipsets than the cyclone II.

I also bought a 200khz 8-channel ADC. 40khz Sonar?

I bought a fast ADC DAC on aliexpress and an ethernet PHY a while ago thinking I could rig it up. The same board is now in the example images attached the the Spartan 6 Fpga! That means that hopefully it will all just plug and play. That's awesome! I was pretty suspicious of my electrical jury rigging at those frequencies.


