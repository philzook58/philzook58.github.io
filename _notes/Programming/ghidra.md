---
title: Ghidra
---


Ghidra is a disassembler and decompiler built by the NSA (started somewhere in the early 2000s)and open source relatively recently. It has pretty thorough architecture support. It's a free decompiler.

Ghidra is programmable in Java and python for the gui.

The Ghidra decompiler is actually largely written in C++ and spoken to by the Java GUI frontend over some kind of protocol. You can find it in  `Ghidra/Features/Decompiler/src/decompile/` One can actually directily call functions of the decompiler. There are a couple projects that do this and more are being made everday it seems.

The help docuemntation inside ghidra itself is useful and I'm not sure it is reflected online anywhere.

shared projects and ghidra server - interesting. I'.ve never needed this,

`-overwrite`
`-process exe` analyze existing binary
`-scriptpath path/to/script`  to add a script
`-postScript scriptname` to actuallly run it. Also there is `-preScript`

# general Workflow

Figure out what functions are. Name them
Correct types
name variables

bytes view allows hex editting

## Ghidra Scripting

A lot of the juiciest stuff is in the FlatProgramAPI <https://ghidra.re/ghidra_docs/api/ghidra/program/flatapi/FlatProgramAPI.html>

The ghidra api docs are pretty decent. I also like to open up the python console (Window > Python) and tab autocomplete just to see what is available.

scripts have accss to a variable called `state`? <https://ghidra.re/ghidra_docs/api/ghidra/app/script/GhidraState.html>

```
currentProgram
currentAddress
```

```
import ensurepip
ensurepip.bootstrap()
import pip
```

hmm. This is not so successful

So. just import a list of tuples

```python


```

```python
import ghidra
f = getFunction("mufunname")
f.getAllVariables
f.localVariables
```

```python
from ghidra.app.decompiler import DecompInterface

  
decomp = DecompInterface()
decomp.openProgram(currentProgram)
timeout = None
res = decompiler.decompileFunction(func, 0, timeout)
    if res and result.decompileCompleted():
        result.getDecompiledFunction()

hf = res.getHighFunction()

res.getCCodeMarkup()
[c.getHighVariable().getInstances() for c in ccode if 'getHighVariable' in dir(c) and c.getHighVariable() != None]
highvar.getName()
highvar.getInstances() # a list of varnode https://ghidra.re/ghidra_docs/api/ghidra/program/model/pcode/VarnodeAST.html

vnode.getDef() # definition
vnode.getDescendents() # users

defpcode = vnode.getDef() # https://ghidra.re/ghidra_docs/api/ghidra/program/model/pcode/PcodeOpAST.html
defpcode.getParent() # parent basic block
seq = defpcode.getSeqnum() # sequence number? It looks like it has a code address in it
seq.getTarget() # returns assembly address. 
```

[seqnum](https://ghidra.re/ghidra_docs/api/ghidra/program/model/pcode/SequenceNumber.html) unique, maintains original address.

highsymbol
I can go from varnode to high var?
getlonedescend. getloneascend would also be useful

```python
proj = ghidra.base.project.GhidraProject.createproject("/tmp/", "testproject", False)
f = java.io.File("/bin/true")
prog = proj.importProgramFast(f)

api = ghidra.program.flatapi.FlatProgramApi(prog)
api.analyzeAll()
```

Widgets are available for quick GUI elements

```
import docking.widgets 
widg.OptionDialog.showInputMultilineDialog(
```

BasicCodeBlockModel
[high function](https://ghidra.re/ghidra_docs/api/ghidra/program/model/pcode/PcodeSyntaxTree.html#getBasicBlocks()) getbasicblocks

<https://ghidra.re/ghidra_docs/api/ghidra/program/model/pcode/PcodeBlockBasic.html>
start,address, stop address, iterate over pcode
InSize, getIn

```python
livein = {b.getStart() : set() for b in block}
liveout = {b.getStart() : set() for b in block}

for i in range(len(blocks)): # is this enough iterations? worst case is straight line graph?
    for blk in blocks:
        lives = {} #copy(liveout[b.getStart()])
        for outind in range(blk.OutSize()):
            succblk = blk.getOut(outind)
            live.add(livein[succblk.getStart()]) 
        for pcode in blk:
            lives.remove(pcode.outputs())
            lives.add(pcode.inputs())
        livein[blk.getStart()] = lives



for i in range(block.getOutSize()):
    block.getOut(i)



on write

availout = {}


for pcode in blk.getIterator():
    out = pcode.getOutput()
    highvar = out.getHigh()
    if highvar != None:
        avail[highVar.getName()] = set(out) 
    for v in pcode.getInputs(): # if in input, infers it is available here
        avail[v.highVar().getName()].add(v)

# but also being read from after the patch kind of infers it could be read from.
# polairty flips inside patch ode being replaced
# maybe if getTarget <= currentAddress <= nextInstruction


```

confidence scores? do monte carlo allocation
inline uniques

getFalseOut, getTrueOUt

## Commands

Ghidra has a [headless mode](https://ghidra.re/ghidra_docs/analyzeHeadlessREADME.html#examples) that is still using the Java stuff, but doesn't bring up the GUI window.
<https://static.grumpycoder.net/pixel/support/analyzeHeadlessREADME.html>

```
analyzeHeadless PATH_TO_PROJECTS PROJECT_NAME -import /path/to/binary
```

<https://github.com/galoget/ghidra-headless-scripts> simple headless scripts

```bash
echo '
import sys
from ghidra.app.decompiler import DecompInterface
from ghidra.util.task import ConsoleTaskMonitor

decompinterface = DecompInterface()
decompinterface.openProgram(currentProgram);
functions = currentProgram.getFunctionManager().getFunctions(True)

with open("decompiled_output.c", "w") as output_file:
    for function in list(functions):
        # Add a comment with the name of the function
        # print "// Function: " + str(function)
        output_file.write("// Function: " + str(function))

        # Decompile each function
        decompiled_function = decompinterface.decompileFunction(function, 0, ConsoleTaskMonitor())
        # Print Decompiled Code
        print decompiled_function.getDecompiledFunction().getC()
        #output_file.write(decompiled_function.getDecompiledFunction().getC())
' > /tmp/decompile.py

echo "
int foo(int x){
    return x*x + 1;
}
" > /tmp/foo.c
# huh. ghidra doesn't support dwarf 5? That seems nuts.
gcc -gdwarf-4 -c /tmp/foo.c -o /tmp/foo.o


cd ~/Downloads/ghidra_10.4_PUBLIC/support
rm -rf /tmp/ghidraproject
mkdir /tmp/ghidraproject
./analyzeHeadless /tmp/ghidraproject Project1 -import /tmp/foo.o -postScript /tmp/decompile.py #2>/dev/null
#./analyzeHeadless /tmp/ghidraproject Project1 -log /tmp/ghidralog -process foo.o -postscript /tmp/decompile.py /tmp/decompile.c
#cat /tmp/decompile.c
```

decomp_opt / decomp_dbg are command line tools hidden inside the ghidra directory structure. T

To get it working you need to set an environment variable SLEIGHHOME=myghidradirectory It needs this to find the archicture files. THese are compiled from sleigh specs `.sla` files.

```
make decomp_dbg
make doc
SLEIGHHOME=myghidradirectory ./decomp_dbg
```

load file /bin/true
save mysavefile.xml
restore
addpath
codedata init,target,,runnnnnnnnnn, dump hits, dump crossrefs - codedata.cc

[This is where most of the commands are registered](https://github.com/NationalSecurityAgency/ghidra/blob/master/Ghidra/Features/Decompiler/src/decompile/cpp/ifacedecomp.cc)

[this is the main of decomp](https://github.com/NationalSecurityAgency/ghidra/blob/da94eb86bd2b89c8b0ab9bd89e9f0dc5a3157055/Ghidra/Features/Decompiler/src/decompile/cpp/consolemain.cc)

[This](https://github.com/NationalSecurityAgency/ghidra/blob/master/Ghidra/Features/Decompiler/src/main/java/ghidra/app/decompiler/DecompileProcess.java) seems to be the java side of the communication to the decompiler is. i think the `ghidra` binary is the one with this interface not `decomp`?
[This is the main of ghidra_opt](https://github.com/NationalSecurityAgency/ghidra/blob/da94eb86bd2b89c8b0ab9bd89e9f0dc5a3157055/Ghidra/Features/Decompiler/src/decompile/cpp/ghidra_process.cc)

sligh_compile actually compiles sla files

ifacedecomp.cc - this is where most of them are
decompile
dump
force hex
map hash
load function
source
option
loadfile
print language
print xml
print C types
prit C
produce C
list action
print param

entry point of function can also be given manually

parse line - to give C prototypes?
parse file foo.h

load fine mytest
read symbols
load function main
decomp
print C
disassemble
rename param_1 argc
print high iStack12

pcode stuff: op.hh

consolemain.cc
funcdata.hh

## PCode

Pcode is the intermediate representation that instructions from different architecures are lifted to. Doing so is the first step of disassembling.

There is a difference between Raw pcode and high pcode. Raw comes right of an instruction, high pcode has a couple more constructs to encode higher level notions like phi nodes, function calls, etc. So Pcode kind of represents at least 2 IRs in a sense, that share datatypes.

<https://spinsel.dev/assets/2020-06-17-ghidra-brainfuck-processor-1/ghidra_docs/language_spec/html/pcoderef.html>

varnodes are inputs and outputs. address space, offset into space, and size

opcodes

uniform address space notion. Registers ar modelling as a separate RAM. Temporary address space and constant adress space

Basically its

- COPY
- STORE
- LOAD
- BRANCH
- CBRANCH
- and then a bunch of computational stuff like INT_ADD

## SLEIGH

[implementing new archtrcture is ghidra slides](https://guedou.github.io/talks/2019_BeeRump/slides.pdf)

[processors](https://github.com/NationalSecurityAgency/ghidra/tree/master/Ghidra/Processors)

[anltr grammar of sleigh](https://github.com/NationalSecurityAgency/ghidra/tree/master/Ghidra/Framework/SoftwareModeling/src/main/antlr/ghidra/sleigh/grammar)

xml scheme <https://github.com/NationalSecurityAgency/ghidra/tree/master/Ghidra/Framework/SoftwareModeling/data/languages>

[Specifying Representations of Machine Instructions](https://www.cs.tufts.edu/~nr/pubs/specifying.pdf) SLED paper, source of sleigh

[The University of Queensland Binary Translator (UQBT) Framework](https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.87.4982&rep=rep1&type=pdf)

Huh, they called jit's "dynamic compilers"

## Debugger

## Resources

[formal semantics for ghidra](https://link.springer.com/chapter/10.1007/978-3-031-25803-9_7) high pcode. mentions interpeter for low pcode.

- [Ghidra Class](https://github.com/NationalSecurityAgency/ghidra/tree/master/GhidraDocs/GhidraClass)
- [decompiler docs](https://grant-h.github.io/docs/ghidra/decompiler/index.html)
- [Mike Bell: Extending Ghidra: from Script to Plugins and Beyond](https://vimeo.com/377180466)
- [ghidra scripting](https://class.malware.re/2021/03/08/ghidra-scripting.html)

[Yara search](https://github.com/0x6d696368/ghidra_scripts/blob/master/YaraSearch.py)
[get basic blocks](https://gist.github.com/bin2415/15028e78d5cf0c708fe1ab82fc252799)

[kaiju](https://github.com/CERTCC/kaiju/blob/main/src/main/java/kaiju/tools/ghihorn/cfg/HighCfg.java) ghihorn

[Binary code coverage visualizer plugin for Ghidra](https://github.com/0ffffffffh/dragondance)

[ghidra chatgpt](https://github.com/SourceDiver42/Ghidra-ChatGPT)

[Ghidra script to export C pseudo-code on multiple files, including defined types](https://gist.github.com/borzacchiello/811288074a193fe571c8d6274f14f829)

[ghidra golf](https://ghidra.golf/)

[pypcode](https://pypi.org/project/pypcode/) How to bind to the lifter.

<https://github.com/niconaus/pcode-interpreter> a haskell pcode interpeter. niiice.
