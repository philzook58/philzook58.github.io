

title: Gettin Bappin with Bap

Bap is quite the beast.

To me starting out there was a lot to swallow. First I had to learn Ocaml, second I knew even less about program analysis and binary stuff than I do now.

```C
int main(){
    return 3;
}
```

```
gcc foo.c
objdump -d a.out
```



To make a basic file to explore some binary, first make a dune file

```ocaml


```




```ocaml


```

You can view information available about a file by


The bap command line has some stock features available + some plugins.

Ivan has an Ascii Cinema here



## The Knowledge Base


## Core Theory


# Project Structure


# Binary / Program Analysis

Call graph
Control flow graph
Functions
Blocks
insns

Dataflow analysis. Backwards Forwards. Fixedpoint on graphs, topological sort.
May/Must
