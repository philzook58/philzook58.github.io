---
author: philzook58
comments: true
date: 2016-12-28 06:47:43+00:00
layout: post
link: https://www.philipzucker.com/?p=330
published: false
slug: Nios II on Cyclone II
title: Nios II on Cyclone II
wordpress_id: 330
---

Q-sys is the secret, mboy.

This reopened my curiousity about fpgas

[http://hackaday.com/2015/12/16/taking-the-pulse-width-modulation-of-an-fpga/](http://hackaday.com/2015/12/16/taking-the-pulse-width-modulation-of-an-fpga/)

I just have not yet found a use case for them. But one he claims is that you'd want a really custom cpu with peripherals for some reason.

I find opencores.org to be completely overwhelming and directionless. There must be some advantage to using the native altera Nios II though right? (Xilinx chips have some equivalent)

Quartus II 13.0sp1

On 64-bit linux, qsys did not open.

It's located

 **`<ACDS install directory>\quartus\sopc_builder\bin\`****`qsys-edit`**

http://stackoverflow.com/questions/17355863/cant-find-install-libxtst-so-6

libxtst.so.6 error

    
    <code><span class="pln">sudo apt</span><span class="pun">-</span><span class="pln">get install libxtst6</span><span class="pun">:</span><span class="pln">i386</span></code>


This fixed it. Funny world, huh. I have no idea what any of that was about or what that library is

[embed]https://www.youtube.com/watch?v=1a_cD6FBROA[/embed]

This seems useful and pertinent.

-------------------------------------------

I have now come back to this post probably a year later.

Blink is still working. Everything is still installed. Ahhhhhhh. Feels good man. The rush of blinking lights. Now I'm using a 12V power supply on my quartus instead of piggy backing an arduino. Of course the board has a regulator on it. What was I thinking? This is so much better.

https://www.altera.com/content/dam/altera-www/global/en_US/pdfs/literature/tt/tt_nios2_hardware_tutorial.pdf

And I couldn't find the examples they're talking about in my quartus distro

But I think these are them

https://www.altera.com/support/support-resources/design-examples/intellectual-property/embedded/nios-ii/exm-hardware-tutorial.html



Everything went pretty smooth

I'm not sure they ever explicitly that you need to attach the ex

Except my chip doesn't have enough M4K units to do that ram they want. Bumped it down to 12800Bytes of onboard ram.

Nope. Still too many. Bumped it down to 5120 Bytes. Somewhere in between these two numbers is the most i can get with what I'm doing.

Seems good so far.

Now to get into eclipse

OpenJDK 64-Bit Server VM warning: You have loaded library /home/philip/altera/13.0sp1/nios2eds/bin/eclipse_nios2/plugins/org.eclipse.equinox.launcher.gtk.linux.x86_1.1.100.v20110505/eclipse_1407.so which might have disabled stack guard. The VM will try to fix the stack guard now.

Ruh Roh. Error.

sudo apt-get install execstack

no fixy

[http://sandaruny.blogspot.com/2016/09/installing-nios-ii-eclipse-on-ubuntu.html](http://sandaruny.blogspot.com/2016/09/installing-nios-ii-eclipse-on-ubuntu.html)

Ok better.

Now it is all funky though. /com/altera errors whenever you try to do anything

I'm getting better results when you call eclipse-nios2 in the bin folder rather than the bare eclipse file.

also used this to change my default jvm. Make sure to change it back later

sudo update-alternatives --config java

Poo. After all that not enough memory. Maybe this is fixable. Or maybe there is a reason this is the bargain basement fpga.

I wish that snickerdoodle would get here.
