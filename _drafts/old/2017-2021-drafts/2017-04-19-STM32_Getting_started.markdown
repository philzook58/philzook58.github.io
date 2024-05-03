---
author: philzook58
comments: true
date: 2017-04-19 19:23:20+00:00
layout: post
link: https://www.philipzucker.com/?p=653
published: false
slug: STM32 Getting started
title: STM32 Getting started
wordpress_id: 653
---

https://hackaday.com/2016/12/02/black-magic-probe-the-best-arm-jtag-debugger/https://www.aliexpress.com/item/ARM-Minisystem-Development-Board-STM32-Development-Board-Core-Board-ESP-Network-STM32F103C8T6/32725174720.html?spm=2114.13010608.0.0.PYSjFu

![](https://ae01.alicdn.com/kf/HTB1vulHNXXXXXXkXFXXq6xXFXXXH/224361831/HTB1vulHNXXXXXXkXFXXq6xXFXXXH.jpg)

I also bought an st-link programmer a while ago.

installing an stlink toolchain from this github. I needed to apt-get install libusb-1.0.0-dev

https://github.com/texane/stlink/blob/master/doc/compiling.md

make release

sudo make install

Having problems running some programs.  can't find shared libraries . https://github.com/texane/stlink/issues/478.

sudo ldconfig fixed problem

https://github.com/texane/stlink/blob/master/doc/tutorial.md

Installed programs:

st-util

st-flash

st-info

stlink-gui



This is the gcc toolchain for arm embedded. Follow the instructions

https://launchpad.net/~team-gcc-arm-embedded/+archive/ubuntu/ppa

I had to uninstall a previous version of gdb-arm-none-eabi



An impressive looking book.

https://www.cs.indiana.edu/~geobrown/book.pdf



Peripheral libraries. I assume these are what is needed to compile a program for the STM32

http://www.st.com/en/embedded-software/stm32-standard-peripheral-libraries.html?querycriteria=productId=LN1939

I registered with STM32

Installed the STM32CubeMX

Install. Make a new project. Select the right chipset. Then you can select the peripherals you want and generate some boiler plate and driver code.

The STM32 was clearly never meant to be used with raw gcc. It is meant to be programmed in an IDE.

OpenSTM, an Eclipse based IDE

http://www.openstm32.org/Downloading+the+System+Workbench+for+STM32+installer

You may need to make an account to get the installer

I used wget to grab the installer. Chrome failed to completely download a couple times

The is an Ac6 folder made

The file eclipse seems to be the executable

In the new c project wizard you can pick stm32 project

I defined a new board that matched the processor I have, the stm32F103C8T5

I'm going to pick to use the Hardware abstraction library?

Not sure what the standard peripheral library has in it.

Interesting extra options:

Lwip - lightweight ip

FreeRTOS

Usb drivers

FatFs filesystem.



examples can be found using the HAL

http://www.st.com/content/st_com/en/products/embedded-software/mcus-embedded-software/stm32-embedded-software/stm32cube-embedded-software/stm32cubef1.html

So you can build in OpenStm

and the run st-util to start a server

and gdb on the generated elf file in the project directory and the following commands

    
    <code>target extended localhost:4242</code>


load

continue



https://github.com/texane/stlink/blob/master/doc/tutorial.md



As for flashing I'm a little scared.

I generated a GPIO pin 13 output enabled project from STMCubeMX. The project type was SW4STM32, which is the software workbench

Adding this line in the User Code section in main.c

    
    HAL_GPIO_WritePin(GPIOC, GPIO_PIN_13, GPIO_PIN_SET);


I built (Ctrl+b)

I flashed with the command.

st-flash write blinker.bin 0x8000000

and the light turns off.

    
    HAL_GPIO_WritePin(GPIOC, GPIO_PIN_13, GPIO_PIN_RESET);


Turns the light on



Interesting: Forth on Stm32

http://hackaday.com/2017/04/19/moving-forth-with-mecrisp-stellaris-and-embello/

https://hackaday.com/2017/03/30/the-2-32-bit-arduino-with-debugging/

https://hackaday.com/2017/04/04/hackaday-io-user-reviews-six-stm32-ides/#more-251126

I was an idiot for not skimming hackaday earlier. Why didn't they come up in my googles?

https://hackaday.io/project/20879-notes-on-using-systemworkbench-with-stm32-bluepill



Does this thing have an ADC or not? I thought i read in the datasheet it does, but I saw a post saying it doesn't

https://hackaday.com/2016/07/11/stm32-and-fpgas-in-a-tiny-package/

https://hackaday.com/2017/01/23/ice-ice-radio-uses-fpga/#more-240835

https://hackaday.com/2016/12/02/black-magic-probe-the-best-arm-jtag-debugger/
