---
author: Philip Zucker
date: 2021-11-12
layout: post
title: "Simple Nand2Tetris Verilog CPU"
---

I feel like my standards of what is worthy of a blog post are creeping up. I don't like that.

I also am haunted by the projects and ideas that I don't make progress on. They just keep piling up. An old one I keep thinking I should return to with my greater wisdom is nand2coq <https://github.com/philzook58/nand2coq>. The idea is to try and use my fancy formal methods knowledge and apply them to the nand2tetris course. You can find the code below in the verilog folder.

Here is a pretty simple verilog implementation of a nand2tetris cpu. It's based on a version I made a couple years ago. I inlined all the little pieces, which significantly increases the clarity I think at the expense of the point that the cpu is made of a hierarchy of smaller structures. Despite that, I suspect the implementation below is at least very close to acceptable to a fpga synthesis tool.

There is something a little more satisfying to using actual appropriate languages rather than the nand2tetris walled garden.

It can load a program from file and has a little testbench that reports the values of registers.

A problem I've had before is I was so focussed on getting it onto an fpga. That makes things tougher because the fpga toolchain is kind of a pain. By the time I get one up, my energy is spent for the day. sing the Icarus verilog simulator is pretty nice though and still pretty satisfying.

I hope the following is somewhat self explanatory if you've looked at the nand2tetris course <https://www.nand2tetris.org/course>
I'm probably delusional on that count though. Project 5 in particular has lots of useful tidbits, such as the instruction decoding table.

```verilog
`define PROGRAMFILE "setd.hack"

module Computer(input clk, input reset, output [0:15] PC, output [0:15] AReg,
            output [0:15] DReg, output [0:15] MReg, output [0:15] instruction);

reg [0:15] PC; // Current Program Counter
reg [0:15] AReg; // A register
reg [0:15] DReg; // D Register
wire [0:15] MReg; // M Register. A Pseudo register that is actuall the output of current index of ram
reg [0:15] ram[0:16383];
reg [0:15] rom[0:16383];

wire [0:15] instruction;
wire writeA; // Write to A
wire writeD; // Write to D
wire writeM; // Write to M
wire pcload; // Write to PC
wire [0:15] aluOut;

////////////////////////////
// Program Counter
// If you want to jump
assign pcload = ((j2 & zr) | (j1 & ng) | (j2 & !ng)) & i; // only jump on C commands

always @(posedge clk) begin
	if (reset == 1'b1)
		PC <= 16'b0;
	else if (pcload == 1'b1)
	    PC <= AReg;
	else
	    PC <= PC + 1;
end
//////////////////////////

//// ROM /////////////
assign instruction = rom[PC];
initial begin
    $readmemb(`PROGRAMFILE, rom);
end
/////////////////////

//// RAM ////////////
assign MReg = ram[AReg];
always @(posedge clk) begin
    // Also clear RAM on reset?
	if (writeM == 1'b1)
	   ram[AReg] <= aluOut;
end
/////////////////////

wire a, i, zx, zy, nx, ny, f, no;
wire d1, d2, d3;
wire j1, j2, j3;

/// CPU///////////
// Instruction bit interpretations
assign i  = instruction[0];  // instruction type. 0 = load immediate into AReg, 1 = compute alu function C command
assign a  = instruction[3];  // a = 0 use A as operand, if a = 1 use M as operand
assign zx = instruction[4]; // x is zero
assign nx = instruction[5]; // negate x
assign zy = instruction[6]; // y is zero
assign ny = instruction[7]; // negate y
assign f  = instruction[8]; // select addition vs. bitwise and
assign no = instruction[9]; // negate output

assign d1 = instruction[10]; // d1 controls loading into a
assign d2 = instruction[11]; // d2 loads into D
assign d3 = instruction[12]; // d3 loads into M (ram)

assign j1 = instruction[13];
assign j2 = instruction[14];
assign j3 = instruction[15];

// If the A register should be written
wire [0:15] aregIn;
assign aregIn =  i ? aluOut : instruction;
assign writeA =  !i | d1; // load the A reg if an A instruction or if that destination is set in C instruction
always @(posedge clk) begin
	if (writeA == 1'b1)
		AReg <= aregIn;
end

// If the D register should be written.
assign writeD = i & d2;
always @(posedge clk) begin
	if (writeD == 1'b1)
		DReg <= aluOut;
end

// If the M register should be written
assign writeM = i & d3;
/////////////

/// ALU /////////////
wire [0:15] x;
wire [0:15] y;
wire [0:15] zerox;
wire [0:15] zeroy;
wire [0:15] notx;
wire [0:15] noty;
wire [0:15] andplus;



assign y = a ? MReg : AReg; // The Y input to the alu is either A or M
assign x = DReg;

// Table 2.6 of Nand2Tetris book
assign zerox = zx ? 16'h0000 : x;
assign notx = nx ? ~zerox : zerox;
assign zeroy = zy ? 16'h0000 : y;
assign noty = ny ? ~zeroy : zeroy;
assign andplus = f ? (notx + noty) : (notx & noty);
assign aluOut = no ? ~andplus : andplus;

assign zr = aluOut == 16'h0000;
assign ng = aluOut[15] == 1; // check sign bit? Is this the right number?
/////////////////////

endmodule
```

The testbench

```verilog
module tb();
reg clk, reset;
wire [15:0] PC;
wire [15:0] AReg;
wire [15:0] DReg;
wire [15:0] MReg;
wire [15:0] instruction;
Computer U1(clk, reset, PC, AReg, DReg, MReg, instruction);
always #5 clk <= ~clk;

initial begin
    $monitor("%t PC = %h A = %h D = %h M = %h I = %b", $time, PC, AReg, DReg, MReg, instruction);
    clk = 0;
    reset = 1;
    #20
    reset = 0;
    #100
    $finish;
end

endmodule
```
You may compile a assembly program `myprog.asm` (I pulled this assembler of the internet. I can't find mine)
```python
python assembly.py myprog
```

And then set the variable at the top of `Computer2.v` to `myprog.hack` (yes this is super janky)

And run the computer via:
```
iverilog Computer_tb.v Computer2.v
./a.out
```

Here's a nothing program
```
@15
D=A
M=D+1
A=M+1
D=A-1
@0
0;JMP
```

It compiles to the following file
```
0000000000001111
1110110000010000
1110011111001000
1111110111100000
1110110010010000
0000000000000000
1110101010000111
```

Which outputs when run
```
philip@philip-desktop:~/Documents/fpga/nand2coq/verilog$ iverilog Computer_tb.v  Computer2.v && ./a.out
WARNING: Computer2.v:37: $readmemb(setd.hack): Not enough words in the file for the requested range [0:16383].
                   0 PC = xxxx A = xxxx D = xxxx M = xxxx I = xxxxxxxxxxxxxxxx
                   5 PC = 0000 A = xxxx D = xxxx M = xxxx I = 0000000000001111
                  15 PC = 0000 A = 000f D = xxxx M = xxxx I = 0000000000001111
                  25 PC = 0001 A = 000f D = xxxx M = xxxx I = 1110110000010000
                  35 PC = 0002 A = 000f D = 000f M = xxxx I = 1110011111001000
                  45 PC = 0003 A = 000f D = 000f M = 0010 I = 1111110111100000
                  55 PC = 0004 A = 0011 D = 000f M = xxxx I = 1110110010010000
                  65 PC = 0005 A = 0011 D = 0010 M = xxxx I = 0000000000000000
                  75 PC = 0006 A = 0000 D = 0010 M = xxxx I = 1110101010000111
                  85 PC = 0000 A = 0000 D = 0010 M = xxxx I = 0000000000001111
                  95 PC = 0001 A = 000f D = 0010 M = 0010 I = 1110110000010000
                 105 PC = 0002 A = 000f D = 000f M = 0010 I = 1110011111001000
                 115 PC = 0003 A = 000f D = 000f M = 0010 I = 1111110111100000
```

Some things that tripped me up:
- You really need to make sure you declare your variables. Verilog automatically assumes things if you don't which screw it up. Verilog is not a good language.
- I for some reason swapped some cases
- I'm still not sure my endianness is good
- My reset logic may not be so good. I may want to reset all ram and registers. This is probably asking for weird bugs.

### Bits and Bobbles

I want to verify this in some meaningful way. I suspect there are bugs in the above implementation.

ideas:

- Make a linker
- Make a dsl to compile to verilog
- Verify equivalence of different implementations
- Get running on Icestick
- Quickcheck or Brute force test using verilator. Equivalence to hack interpreter
- Verilator to ocaml bindings, compile coq interpeter and compare
- Symbolic Executor
- Datalog disassembler
- Horn clause translation of hack


<https://github.com/jopdorp/nand2tetris-verilog> Another implementation of nand2tetris cpu in verilog.
<https://gitlab.com/x653/nand2tetris-fpga/> another implementation of nand2teris in verilog
<https://misterfpga.org/viewtopic.php?t=28>

- Bluespec is quite cool
- Koika

Here's a fun idea:
Use symbiyosys <https://symbiyosys.readthedocs.io/en/latest/quickstart.html> for nand2tetris verification. One can write a "speclike" verilog implementation and compare with a "circuitlike" implementation. Seems to work for simple stuff.

```verilog

module mynot(input a, output b);
    nand U1(b,a,a);
endmodule

module mynot2(input a, output b);
    assign b = ~a;
endmodule

module myand(input a, input b, output c);
    wire d;
    nand  U1(d,a,b);
    mynot U2(d,c);
endmodule

module and_spec(input a, input b, output c);
    assign c = a & b;
endmodule

module Reg(input in,input load,input clk,output reg out);
    always @(posedge clk) begin
        case (load)
            1'b1 : out <= in;
            1'b0 : out <= out;
        endcase
    end
endmodule

module tb2();
    reg clk;
    wire out;
    reg in, load;
    Reg U1(in,load,clk,out);
    
    always #5 clk <= ~clk;
    initial begin
        $monitor("%t Reg : in = %b load = %b out = %b clk = %b", $time, in, load, out, clk);
        in = 0;
        load = 0;
        clk = 0;
        #1
        #10 in = 1;
        #10 load = 1;
        #10 in = 0;
        #10 load = 0;
        #10 in = 1;
        #25 $finish;
    end
endmodule
/*
module tb();
    reg a;
    wire b1;
    mynot U1(a,b1);
    initial begin
        $monitor("mynot : a = %b b = %b", a, b1);
        a = 1'b0;
        #1 a = 1'b1;
        #1 $finish;
    end
endmodule
*/
module mynoteq();
    reg a, b;
    wire b1, b2;
    mynot U1(a,b1);
    mynot2 U2(a,b2);

    wire and1, and2;
    myand U3(a,b,and1);
    and_spec U4(a,b,and2);


    `ifdef FORMAL
        always @(*) begin
            assert (b1 == b2);
            assert (and1 == and2);
        end
    `endif
endmodule
```

sby file
```
[options]
mode prove

[engines]
smtbmc z3

[script]
read -formal not.v
prep -top mynoteq

[files]
not.v
```