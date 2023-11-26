
There is a lot of discussion of moe complicated encodings, but I think it is interesting to consider a relatively simple encoding of program control flow.
This is modelling jumps as tail calls, but it is not continuation passing style.

Simple imperative programs

Bril benchmarks

```

```

In datalog, there are sorts, relations, and rules.

- We describe the connection between a label and it's body by a rule

```egglog
(rewrite (myblock x y z)
         ()  

)
(myblock (arg 0) (arg 1) (arg 2))

(run 10)

```

```bash
echo "
#include<stdint.h>

int64_t myfun(int64_t x){
    return 2*x + 3;
}" > /tmp/myfun.c
clang /tmp/myfun.c -emit-llvm -S -o /tmp/myfun.ll
cat /tmp/myfun.ll
```

```python
import llvmlite.binding
import matplotlib.pyplot as plt
import networkx as nx
G = nx.DiGraph()
prog = open("/tmp/myfun.ll").read()
module = llvmlite.binding.parse_assembly(prog)
print(dir(module))
for func in module.functions:
    print(func)
    print(dir(func))
    for block in func.blocks:
        print(dir(block))
        G.add_node("block" + block.name)
        for insn in block.instructions:
            print(insn)
            print(insn.opcode)
            operands = list(insn.operands)
            dst = operands[0]
            print("dst", dst.name)
            srcs = operands[1:]
            for src in srcs:
                print(src)
                G.add_edge(src.name, insn.opcode)
            G.add_edge(insn.opcode, dst.name)
nx.draw(G, with_labels=True)
plt.show()
```

```python
# convert from ssa phi form to tail call form
for block in blocks:


```

liearity?
e-substitution
