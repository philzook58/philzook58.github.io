---
author: philzook58
comments: true
date: 2016-01-27 22:17:39+00:00
layout: post
link: https://www.philipzucker.com/using-eda-playground/
slug: using-eda-playground
title: Using EDA Playground
wordpress_id: 385
---

So to write Verilog code you need to write a testbench.

    
    // Code your testbench here
    // or browse Examples
    module tb();
      reg clk, reset;
      wire speaker;
      music dut (.clk(clk), .speaker(speaker),.reset(reset));
      
      initial
      begin
        $dumpfile("dump.vcd");
        $dumpvars(0, dut);
        reset = 1'b1;
        clk = 1'b0;
        #20
        reset = 1'b0;
    	#140;
        $finish;
      end
    
      always
          #10 clk = ~clk;
    endmodule


The #10 type things are delays.

The dumpfile thing is needed by edaplayground

The reset logic was necessary or else the submodule had unspecified values

Make sure to check the open EPWave box on the side

Everything needs to be wrapped in a module endmodule.

The .clk is specifying the parameter. the clk inside the parentheses is the reg I'm passing it.

I set reset high. Wait, then turn it low.

To end the simulation you need the $finish command.



    
    // Code your design here
    module music(clk, speaker,reset);
    input clk, reset;
    output speaker;
    
    // Binary counter, 3-bits wide
      reg [2:0] counter;
    always @(posedge clk) 
      begin
        if(reset==1'b1)
          begin
            counter <=0;
          end
        else
      		counter <= counter+1;
      end
    // Use the most significant bit (MSB) of the counter to drive the speaker
      assign speaker = counter[2];
    endmodule


specify how this module can connect to the outside world

<= is some kind of sequential assignment. It tends to be what is used in these posedge type blocks.

= is used to form aliases using the assign command

If else stuff is fairly self explanatory

begin end are the equivalent of {} in other languages


