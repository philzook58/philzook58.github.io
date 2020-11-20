---
author: philzook58
comments: true
date: 2018-12-14 18:02:40+00:00
layout: post
link: https://www.philipzucker.com/nand2tetris-in-verilog-and-fpga-and-coq/
slug: nand2tetris-in-verilog-and-fpga-and-coq
title: Nand2Tetris in Verilog and FPGA and Coq
wordpress_id: 1112
---

Publishing these draft notes because it has some useful info in it and trying to reboot the project. It's very ambitious. We'll see where we get with it.

[https://github.com/philzook58/nand2coq](https://github.com/philzook58/nand2coq)



Old Stuff (Last Edited 6/23/18):

So my friends and I are starting the nand2tetris course. I feel like I have some amount of familiarity with the topics involved, so I'd like to put it into challenge mode for me.

Week 1 is about basic combinatorial logic gate constructions and sort of the ideas of an HDL.

I was trying to keep up in Verilog and failing. The verilog syntax is a little bit more verbose.

Still not so bad.

The easiest thing to use was assign statements.  The difference between = and <= in verilog is still a little opaque to me

I compiled them and ran them using Icarus verilog (iverilog and the vpp the output file).

I started using MyHDL but I'm not sure I saw why it was going to be easier? But the MyHdl docs did help me understand a bit why verilog is the way it is.



Here is a big list of interesting projects:

MyHDL - A python hardware description language. Can output VHDL and Verilog. based around python generators and some decorators.

Icarus Verilog - http://iverilog.wikia.com/wiki/Main_Page. iverilog Compiles verilog into a assembly format which can be run with vvp command.

example

    
    iverilog myor.v not.v
    
    vpp a.out




Verilator - Compiles Verilog to C for simulation

GTKWave - A Waveform viewer

IceStick - A cheap 20$ ish fpga usb board that can be programmed easily

IceStorm http://www.clifford.at/icestorm/ - An OpenSource toolchain for compiling to and programming ice40 fpga chips

IceStudio - a graphical block editor. Last I checked it was still a little clunky

EdaPlayground - online web app for writing code and giving to  simulators



Formal tools:

yosys-smtbmc

symbiyosys

http://www.clifford.at/papers/2016/yosys-smtbmc/

http://zipcpu.com/blog/2017/10/19/formal-intro.html



icestick floorplan - https://knielsen.github.io/ice40_viewer/ice40_viewer.html

ZipCPU

open source fpga twitter https://twitter.com/ico_tc?lang=en

https://opencores.org/



https://hackaday.com/2015/08/19/learning-verilog-on-a-25-fpga-part-i/



Upduino - interesting set of boards. Cheap.

http://gnarlygrey.atspace.cc/development-platform.html#upduino



Questionable: Clash?

installing icestick on the mac

https://github.com/ddm/icetools

https://github.com/Homebrew/homebrew-core/issues/9229

Had to pip uninstall enum34. Weird.



Verilog

Start with module statement

end lines with semicolons.

You need to name instantiated elements






yosys -p "synth_ice40 -top not1 -blif not.blif" not.v


[https://mcmayer.net/first-steps-with-the-icestorm-toolchain/](https://mcmayer.net/first-steps-with-the-icestorm-toolchain/)


../icetools/arachne-pnr/bin/arachne-pnr  -d 1k -P tq144 -o not.asc -p not.pcf not.blif 


https://gist.github.com/wbotelhos/46c37807c834ccb5bb406e426adfe347


../icetools/icestorm/icepack/icepack not.asc not.bin




iceprog not.bin




    
    <code class="language-bash">sudo kextunload -b com.FTDI.driver.FTDIUSBSerialDriver  </code>


The ftdi isn't working





    
    module alu(
    	  input [15:0] x
    	, input [15:0] y
    	, output [15:0] out
    	, input zx // zero x
    	, input zy // zero y
    	, input nx // negate result on x
    	, input ny // """
    	, input f // Plus is 1 or and if 0
    	, input no // negate result?
    	, output zr // is it exactly zero
    	, output ng // is out < 0
    	);
    
    wire [15:0] zerox;
    wire [15:0] zeroy;
    wire [15:0] notx;
    wire [15:0] noty;
    wire [15:0] andplus;
    
    assign zerox = zx ? 0 : x;
    assign notx = nx ? ~zerox : zerox;
    assign zeroy = zy ? 0 : y;
    assign noty = ny ? ~zeroy : zeroy;
    assign andplus = f ? x + y : x & y;
    assign out = no ? ~andplus : andplus; 
    
    assign zr = out == 0;
    assign ng = out[15] == 1; // check sign bit
    
    
    endmodule







