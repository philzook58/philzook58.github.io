---
author: philzook58
comments: true
date: 2018-03-08 17:53:12+00:00
layout: post
link: https://www.philipzucker.com/stm32f411-discovery-board-getting-started/
slug: stm32f411-discovery-board-getting-started
title: STM32F411 Discovery Board  Getting started
wordpress_id: 1007
---

Bought one of these discovery boards for 15$ from digikey. I like the built in stuff, like the 9axis mems device. I don't enjoy wiring up little boards particularly and it makes every project so ephemeral.

http://www.st.com/content/st_com/en/products/evaluation-tools/product-evaluation-tools/mcu-eval-tools/stm32-mcu-eval-tools/stm32-mcu-discovery-kits/32f411ediscovery.html

I am concerned that I should have gotten the older board.

User manual has pin connectors

http://www.st.com/content/ccc/resource/technical/document/user_manual/e9/d2/00/5e/15/46/44/0e/DM00148985.pdf/files/DM00148985.pdf/jcr:content/translations/en.DM00148985.pdf

It's in platform.io as

disco_f411ve

Huh it only supports STM32Cube? I kind of wanted to try libOpenCM3

start a project with

platformio init --board disco_f411ve

platformio run

The examples are invaluable

https://github.com/platformio/platform-ststm32/tree/develop/examples

ok. There is a blink for the Hardware abstraction layer (HAL) and Low level (LL)

Hmm. Neither blink examples work off the bat. SYS_CLOCK is undefined for Low level

and board not supported in the HAL.





Alright let's try libopencm3

https://github.com/libopencm3/libopencm3-examples

make in top directory first

follow directions to init submodule

alirght I guess I need to download the arm toolchain

https://developer.arm.com/open-source/gnu-toolchain/gnu-rm/downloads

I put them on my path

export PATH=~/Downloads/gcc-arm-none-eabi-7-2017-q4-major/bin:$PATH

Then ran make

also need to apt install gawk

editted the Makefile of miniblink

https://github.com/libopencm3/libopencm3/blob/master/ld/devices.data

stm32f411re stm32f4 ROM=512K RAM=128K

that's the right config even though re is wrong

Okay was getting weird error

sudo make flash V=1

the V=1 gives verbose

I may have had to apt install openocd?

Need to run under sudo. Go fig.

Alright got some blinking! WOOO

Ah I see. PD12 is PortD12. Makes sense.


