---
author: philzook58
comments: true
date: 2017-02-02 15:59:35+00:00
layout: post
link: https://www.philipzucker.com/install-webpack-ise-14-7-ubuntu-spartan-ax309-fpga-board/
slug: install-webpack-ise-14-7-ubuntu-spartan-ax309-fpga-board
title: Install WebPack ISE 14.7 on Ubuntu & Spartan AX309 FPGA Board
wordpress_id: 600
---

Downloaded Webpack ISE, the free Xilinx guy that works with

Tried to install usb drivers. But it failed. I saw a board that said it should work if libusb is installed. We'll see.

It wasn't readily apparent to me how to run the thing. The Mojo site helped

[https://embeddedmicro.com/tutorials/mojo-software-and-updates/installing-ise](https://embeddedmicro.com/tutorials/mojo-software-and-updates/installing-ise)

You need to source a file.

You have to get a license from the license manager. It did not automatically navigate my browser. Select webpack license and load it in the license manager. It will be emailed to you.

A Series of errors upon trying to plan pins:

/opt/Xilinx/14.7/ISE_DS/ISE/bin/lin64/_pace_old: error while loading shared libraries: libXm.so.3: cannot open shared object file: No such file or directory

    
    sudo apt-get install libmotif3




/opt/Xilinx/14.7/ISE_DS/ISE//lib/lin64/libstdc++.so.6: version `GLIBCXX_3.4.15' not found (required by /usr/lib/firefox/libxul.so)

    
    sudo apt-get install libstdc++5




https://forums.xilinx.com/t5/General-Technical-Discussion/Xilinx-issues-on-Linux/td-p/194576/page/2

Wind/U Error (193): X-Resource: DefaultGUIFontSpec (-*-helvetica-medium-r-normal-*-14-*) does not fully specify a font set for this locale
Wind/U Error (248): Failed to connect to the registry on server philip-desktop

Warning!!: XKEYSYMDB environment variable is set to a wrong location

    
    sudo apt-get install xfonts-75dpi xfonts-100dpi




rebooted computer.

Hey! It works after a good 30 seconds. Oh my good this looks like garbage. What is going on here? Some weirdo windows port?



Ok. I have a Spartan 6 AX309 board now and a xilinx platform usb cable. Let's see if we can program it. I asked the seller for the link to their files. It's  got datasheets and example code. That's nice.

http://elinux.org/Install_Xilinx_USB_cable_drivers_for_Ubuntu

http://www.george-smart.co.uk/wiki/Xilinx_JTAG_Linux

The programming software is apparently called impact. That's helpful. SARCASM

Ok. I left this on my desk for a week and forgot what I did. As I recall the installation process did not appear to be working.

Ok. So I think it might be working.

I had concern about getting some kind of ESN error, but I think I was doing things in the wrong order.

First click boundary scan.

Then find Initialize chain.

Then my chip shows up. Then I added a .bit file configuration.

WHOO. The LED BLINK TEST WORKS.

Why do I do this to myself? My Altera toolchain was working just fine. Oh well. Onwards and upwards.




