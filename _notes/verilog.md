---
layout: post
title: Verilog
---

HLS
SystemC - C++ classes for event driven simulation. Kind of an embedded dsl verilog ish
systemverilog - https://github.com/zachjs/sv2v/ systemverilgo to verilog converter 
[What is AXI](https://www.youtube.com/watch?v=1zw1HBsjDH8&ab_channel=DillonHuff)

https://en.wikipedia.org/wiki/Universal_Verification_Methodology - verification language


Bluespec 
Silicon Compiler - what is this?

Circt - llvm project


### Verilog

Verilog is a bit dual brained. In one sense it is a hardware design language. In this sense it's almost just a netlist, aka a graph data structure describing a circuit. Each module can has ports which are wired up internally. Internal instantiations of modules are named.

```verilog
module mynot(input a, output b);
    nand U1(b,a,a); // output, input, input.
endmodule;
```

In another sense it is a behavioral specification language describing parallel running tasks.

In another sense it a test bench language.

It is kind of a pile of hot garbage.


The delay annotation for 10 ticks is `#10`. I feel like this should have a semicolon (kind of a `sleep` statement), but it does not.

`assign` statements are a nice way to describe combinational logic.


icarus verilog is an easy enough to use simulator. <https://iverilog.fandom.com/wiki/Main_Page> <https://iverilog.fandom.com/wiki/Getting_Started>.

```
iverilog myfile.v
./a.out
```

Defining regular assertions <https://stackoverflow.com/questions/13904794/assert-statement-in-verilog>
Maybe a better approach is to use verilator?



```verilog
module foo;
  initial begin
        $display("hi");
        $finish;
        end
endmodule //foo
```

Comments are //
initial is not even a statement. What syntactic category is it?
The prduced file is a vvp textfile
bitvectors are described in a very odd way. `[lastbitindex:firstbitindex]`

tasks/processes: initial vs always
symbiyosys. Pretty cool seeming

<https://verilogguide.readthedocs.io/en/latest/index.html> FPGA design with verilog


bluespec - chris says. Chris is nuts though. he drank so much koolaid he slams through walls

<https://www.asic-world.com/verilog/veritut.html> verilog tutorial. There's some weird stuff in here

<https://twitter.com/pdp7/status/1458115920811868165?s=20> tiups on university courses using ice40 and open source
<https://github.com/icebreaker-fpga/icebreaker-workshop>


<https://github.com/philzook58/nand2coq/tree/master/verilog> actually some kind of fun stuff in here.

Staged bluespec

Bluespec - ready and enable signals. Do not a assume any particular latency
Also suppress clk signal

The essence of bluespec <https://www.youtube.com/watch?v=5W9v-n-EZuo&ab_channel=ACMSIGPLAN>
Koika
