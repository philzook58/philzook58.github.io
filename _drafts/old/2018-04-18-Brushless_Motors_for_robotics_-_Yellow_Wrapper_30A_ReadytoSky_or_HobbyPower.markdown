---
author: philzook58
comments: true
date: 2018-04-18 18:16:24+00:00
layout: post
link: https://www.philipzucker.com/?p=1030
published: false
slug: Brushless Motors for robotics - Yellow Wrapper 30A ReadytoSky or HobbyPower
title: Brushless Motors for robotics - Yellow Wrapper 30A ReadytoSky or HobbyPower
wordpress_id: 1030
---

Holy shit. This Ben Katz guy's stuff is fucking sweet.

http://build-its-inprogress.blogspot.com/

https://www.youtube.com/watch?v=VSvipjiiGL8

Also the ODrive project.



Cheap-o motor driver.

Yellow Readytosky from amazon.

Looking at other board pictures, it appears to be equivalent to HobbyPower boards.

It is possible that the firmware can be reflashed.

This is the SimonK firmware repository.

[https://github.com/sim-/tgy](https://github.com/sim-/tgy)

There is a flag in the code that can turn on RC car like control with reverse. These ESC are just atmega's attached to big ole FETs. Be sure to check out the Makefile. With it you can read and flash. You need avrdude installed. Also possibly the avr-gcc toolchain.

It appears that mine does not already have SimonK installed? If it were, one can reprogram using the servo control line.

There are exposed pads on the board that to connect to the correct programming pins, MISO MOSI SCK RESET VCC GND.



In order to sequence the switching of the three power lines, my understanding is that the microcontroller turns off the power and reads the back EMF to determine where in the cycle. In principle, I feel like this information could be recorded and sent back as a position counter. However, I am frightened at messing up the timing of the code, which I suspect is highly tuned. Or perhaps one could tap into the lines with another microcontroller?

For feedback we can hopefully use the cheap motor encoder disks from aliexpress



[https://www.rcgroups.com/forums/showthread.php?2211634-Flashing-Atmel-based-SimonK-ESCs-to-BLHeli](https://www.rcgroups.com/forums/showthread.php?2211634-Flashing-Atmel-based-SimonK-ESCs-to-BLHeli)

https://github.com/c---/ArduinoUSBLinker

https://oscarliang.com/esc-1-wire-bootloader-signal-cable-blheli-simonk/



So If we can easily reflash these guys to have a reverse mode, that would be nice.



So the simonk site has some make commands that appear to use avrdude? Does it basically use avrdude to communicate?

Does it need to be externally powered too? Yes. You need to power the esc thrugh the powerlines for all of this

make read

We happen to have some AVR isp Mark II hanging around from a wild and errant youth.

make read_avrisp2

should work in theory?

https://www.youtube.com/watch?v=3wTYY_9w_8k



https://www.rcgroups.com/forums/showthread.php?1513678-RCTimer-Turnigy-Hobbywing-ESC-DIY-Firmware-Flashing



A very interesting post about using brushless in a battlebot, with some discussion of SimonK settings and tuning

http://www.etotheipiplusone.net/?p=3985

https://docs.google.com/document/d/1m5izv6gzFoWk-8pS96Rfv9UoiWpTZ8kr1d-6uXDNpU8/edit

This is very useful.

He mentions some regenerative modes

[https://geekshavefeelings.com/posts/sensorless-brushless-cant-even](https://geekshavefeelings.com/posts/sensorless-brushless-cant-even)

https://www.youtube.com/watch?v=MQQX7IIdAtI

The main code for the SimonK controller

Its a lot but not so much that you can't skim the nice commenting in 20 mins and have some thoughts

[https://github.com/sim-/tgy/blob/master/tgy.asm](https://github.com/sim-/tgy/blob/master/tgy.asm)

a 38400 baud is mentioned? Is that the right baud for the bootloader communication?

Low_Brake is an interesting option. Turn brake on when PWM is below lowest pwm.

Hmm Could Motor_Debug be turned on for possible position control?

AVR note on Brushless motor control

http://www.microchip.com//wwwAppNotes/AppNotes.aspx?appnote=en591508

Am I going to have extreme difficulty with slow movement? Maybe: Current sensing strategy fails so Not even sure mtor will know which coil to turn on.

https://hackaday.com/2015/04/20/driving-a-brushless-dc-motor-sloooooooowly/


