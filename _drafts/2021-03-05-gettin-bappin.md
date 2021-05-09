

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

Get some info from the Knowledge Base. 
`bap list`


## The Knowledge Base
The Knowledge Base is a key value store? Database.
It is also kind of an alternative class (like object oriented classes) system
It is also kind of a




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

## Other tidbits
JT's gists
Ivan's gists
Choice gitter tips

## Universal Values
https://discuss.ocaml.org/t/types-as-first-class-citizens-in-ocaml/2030
https://github.com/janestreet/core_kernel/blob/master/univ/src/univ.ml
http://binaryanalysisplatform.github.io/bap/api/odoc/bap/Bap/Std/Value/index.html
https://blog.shaynefletcher.org/2017/03/universal-type.html

locally abstract types. Using (type u) as an argument - useful for first class modules ande gadts

Storing first class modules in a hashtable is an example.

DIY typeclasses

universal value + registry of typeclass instances?



