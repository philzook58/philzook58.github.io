---
author: philzook58
comments: true
date: 2015-11-30 01:29:30+00:00
layout: post
link: https://www.philipzucker.com/gettin-back-goin-on-fpga/
slug: gettin-back-goin-on-fpga
title: Gettin Back Goin on FPGA
wordpress_id: 222
---

I recently bought a high speed AD/DA unit which seems like it could probably only be serviced by an fpga, so I thought I'd give it another go.

I have this board

[http://www.amazon.com/RioRand-EP2C5T144-Altera-Cyclone-Development/dp/B00LEMKR92/ref=sr_1_2?ie=UTF8&qid=1446530204&sr=8-2&keywords=fpga](http://www.amazon.com/RioRand-EP2C5T144-Altera-Cyclone-Development/dp/B00LEMKR92/ref=sr_1_2?ie=UTF8&qid=1446530204&sr=8-2&keywords=fpga)

and a [http://www.amazon.com/Geeetech-Altera-Blaster-ALTERA-programmer/dp/B00E9JAC7O/ref=sr_1_8?ie=UTF8&qid=1446530247&sr=8-8&keywords=altera](http://www.amazon.com/Geeetech-Altera-Blaster-ALTERA-programmer/dp/B00E9JAC7O/ref=sr_1_8?ie=UTF8&qid=1446530247&sr=8-8&keywords=altera)

To program it

I power it by jumpering the labelled 3v3 to an arduino's 3v3 power. It's just the easiest way for me. A random power supply will porbably work too. Looks like it has an onboard regulator

Unfortunately my working Quartus II is on long gone computer

After a couple days I figured out that I downloaded the wrong version. Make sure to get the web edition

[http://dl.altera.com/13.0sp1/?edition=web&direct_download=1&version_number=13.0sp1&description=Quartus+II+Software+%28includes+Nios+II+EDS%29&platform=linux&filesize=1753569283&download_method=download&direct_file=QuartusSetupWeb-13.0.1.232.run#tabs-2](http://dl.altera.com/13.0sp1/?edition=web&direct_download=1&version_number=13.0sp1&description=Quartus+II+Software+%28includes+Nios+II+EDS%29&platform=linux&filesize=1753569283&download_method=download&direct_file=QuartusSetupWeb-13.0.1.232.run#tabs-2)

Get the main Quartus file and the cyclone II support

Quartus II kept crashing found this fix

[https://www.altera.com/support/support-resources/knowledge-base/solutions/rd12102013_780.html](https://www.altera.com/support/support-resources/knowledge-base/solutions/rd12102013_780.html)

quartus: error while loading shared libraries: libSM.so.6: cannot open shared object file: No such file or directory

sudo apt-get install libsm6:i386

In the new project wizard pick a new and for the device pick


Device Cyclone II




EP2C5T1448N




Couldn't find that exact part number in the list. Picked EP2C5T144C8




Seems close.




So we have to do pin assignment. The clock is a special pin, so that's how you pull it in. There are leds on board




Three LEDs are connected to pins 3, 7 and 9, and a push-button is connected to pin 144.




I took called the node clock and used PIN_17 which desribes itself as one of the clocks.




I picked counter_out[25] as PIN_9 since it gives a reasonable blink rate. (the clock pin should be 50Mhz)


[http://www.leonheller.com/FPGA/FPGA.html](http://www.leonheller.com/FPGA/FPGA.html)

Click new file vhdl. Made a simple counter.

    
    // This is an example of a simple 32 bit up-counter called simple_counter.v
    // It has a single clock input and a 32-bit output port
    module simple_counter (input clock , output reg [31:0] counter_out);
    always @ (posedge clock)// on positive clock edge
    begin
     counter_out <= #1 counter_out + 1;// increment counter
    end
    endmodule// end of module counter




Got an error about needing a Top Level Design entity

Went into Assignments > Settings to set the top level design entity. I guess this is like defining the entry point of the program. Used simple_counter as top level.

The "My First FPGA" tutorial has too much bullshit in it from the get go.

Compiled

Tools > Programmer

Hardware Setup - picked USB Blaster

JTAG.

Having porblems. Just says failed.

Picked .sof files in output_files

Error (209053): Unexpected error in JTAG server -- error code 89

Apparently some kind of permissions problem in linux for the usb blaster

[http://rocketboards.org/foswiki/view/Documentation/UsingUSBBlasterUnderLinux](http://rocketboards.org/foswiki/view/Documentation/UsingUSBBlasterUnderLinux)

Holy shit. It is working.

It assigned counter_out[0] to PIN_24. And I read a 25Mhz signal. That makes sense. Every cycle of the 50Mhz clock the pin is flopped and that divides the frequency by 2.
