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

The rachit-averse
Filament - time aware data types
Dahlia

Conal Elliott - circuits as categories

# Logic Synthesis
Logic Optimizaton

https://www.iwls.org/iwls2023/program.php
 IWLS international workshop on logic synthesis


https://www.youtube.com/watch?v=bXdAIqeu9ck&ab_channel=IEEECASSRioGrandedoSulChapter Mischenko
EDA
Physical synthesis
word to bit - bit blastig
verific
delay aware, congestion aware bitg blasting
word level rewriting
open cores
SAT sweeper
NPN matcher
logic sharing extractoin
gat sizing
retiming
delay optimization
false path analysis
equiv checking
model checking
routing scheduling
bit-parallel SIM reverse SIM
deep ntegration of sat solver and simulator
cuts 
retiming - move flip flips through comibational nodes. Forward retiming, backward retiminig
Peichen Pan - retiming + mapping
miter
patching with equivalence checking
engineering change orders
ECO 2013 2021 comp

minisat aiger, si, abc, yoys, repklce the openroad project https://github.com/The-OpenROAD-Project
simple SOP
simple BDD
decomp using truth tabes
IWL contest

https://en.wikipedia.org/wiki/Engineering_change_order

simple partial product
booth partial product



algorithms for physical design https://www.youtube.com/watch?v=EHVGNaSF1Js&list=PLynNd6jjBBrrQ87Q4n0t-4QFG0MZdCgTq&index=10&ab_channel=IEEECASSRioGrandedoSulChapter

[Formal verification of modular multipliers using symbolic computer algebra and boolean satisfiability](https://dl.acm.org/doi/10.1145/3489517.3530605)



custom SAT solvers

SAT sweeper. Equivalence checking,
Align the subcircuits
Prove internal equivlanece. 2001 paper

NPN - euiqvalce classes of functions modulo negation or inputs, permuation, negation of outputs


Two level synthesis
ESPRESSO
Quine-Mcclusky
Petricek

Multi level logic syntehsis

binary decision diagrams
and inverter graphs, majority nverter graphs
algerbaic methods 
don't care optmization
https://si2.epfl.ch/~demichel/graduates/theses/winston.pdf SAT methods for multi level syntehsis. Recent

https://people.eecs.berkeley.edu/~alanmi/publications/other/multi_level.pdf multilevel review. Brayton 90
https://www.researchgate.net/profile/Satrajit-Chatterjee-3/publication/221061882_DAG-aware_AIG_rewriting_a_fresh_look_at_combinational_logic_synthesis/links/0c9605350467495133000000/DAG-aware-AIG-rewriting-a-fresh-look-at-combinational-logic-synthesis.pdf DAG aware AIG rewriting


And invertwr grapphs -
AIGR lbrary
https://github.com/arminbiere/aiger

ABC https://github.com/berkeley-abc/abc ABC: System for Sequential Logic Synthesis and Formal Verification
rewriting 4 input
logic cones
balancing


Multivariate horner schemes
https://mathoverflow.net/questions/28459/how-to-implement-horner-s-scheme-for-multivariate-polynomials
It isn't clear greedy isn't pretty good and it isn't clear that DAG matters. "Unfortunately", distributiity reifies DAG sharing into tree size.
https://math.stackexchange.com/questions/1436204/computationally-efficient-form-to-evaluate-multivariate-polynomials


yosys
technology mapping




Defunct?
MVSIS
SIS


Fraiging - functionally reduced aig. SAT sweeping
CEC engine


https://www.synopsys.com/glossary/what-is-equivalence-checking.html
connectivity checking
X propagation

https://github.com/lsils/lstools-showcase

https://github.com/google/skywater-pdk

### Networks
array
wallace tre
dadda tree
compressor tree

riple carry
carry look ahead
brent-kung adder
lander-fischer adder

[computer airthemtic algorithms](https://ashkanyeganeh.com/wp-content/uploads/2020/03/computer-arithmetic-algorithms-2nd-edition-Behrooz-Parhami.pdf)

### benchmarks
[OpenABC-D: A Large-Scale Dataset For Machine Learning Guided Integrated Circuit Synthesis](https://arxiv.org/pdf/2110.11292.pdf) https://github.com/NYU-MLDA/OpenABC
[EPFL benchamrk suite](https://core.ac.uk/download/pdf/148012141.pdf) https://www.epfl.ch/labs/lsi/page-102566-en-html/benchmarks/ https://github.com/lsils/benchmarks

IWLS benchmarks https://iwls.org/iwls2005/benchmarks.html

### ABC
https://www.dropbox.com/s/qrl9svlf0ylxy8p/ABC_GettingStarted.pdf getting started

```bash
echo "module rca2 (a0, b0, a1, b1, s0, s1, s2);
//-------------Input Ports Declarations-----------------------------
input a0, b0, a1, b1;
//-------------Output Ports Declarations-----------------------------
output s0, s1, s2;
//-------------Wires-----------------------------------------------
wire c0;
//-------------Logic-----------------------------------------------
assign s0 = a0 ^ b0 ;
assign c0 = a0 & b0 ;
assign s1 = a1 ^ b1 ^ c0;
assign s2 = (a1 & b1) | (c0 & (a1 ^ b1));
endmodule" > /tmp/example.v
```
```bash
echo "
read /tmp/example.v
strash
print_stats
#print_kmap
read_dsd a*b+c
read_truth 10000000; bdd; print_kmap
#write_verilog
#write_cnf
show
miter -h # conver to equivelnce checknig circuit
quit
" | abc
```

`read` command. There are a number of formats. One is just equations

`balance`
`renode`
`rewrite`

https://github.com/mvcisback/py-aiger-abc
SIMPLIFY_TEMPLATE = 'read {0}; dc2; dc2; dc2; fraig; write_aiger -s {0}'
### AIG
https://fmv.jku.at/aiger/
https://github.com/arminbiere/aiger
command line tools

py-aiger. Oh this is a pure python thing. Is there even much to it?
```python
import aiger

x, y, z, w = aiger.atoms('x', 'y', 'z', 'w')

expr1 = z.implies(x & y)
expr2 = z & w

circ1 = expr1.with_output('z').aig       # Get AIG for expr1 with output 'z'.
             
circ2 = circ1 >> circ2                # Feed outputs of circ1 into circ2.
```

aiger library - biere



```egglog

(datatype AIG
  (And AIG AIG)
  (Not AIG)
)

(rewrite (Not (Not x)) x)

```