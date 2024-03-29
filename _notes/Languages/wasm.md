---
layout: post
title: Wasm/Emscripten
---

- [WASM](#wasm)
  - [WASI](#wasi)
    - [WABT](#wabt)
    - [Running](#running)
    - [Wasm modules](#wasm-modules)
    - [Writing Wasm directly](#writing-wasm-directly)
- [Emscripten](#emscripten)
    - [Command line Utility Conversion](#command-line-utility-conversion)
    - [Souffle](#souffle)
  - [Minizinc](#minizinc)
- [Misc](#misc)

sqlite fuzzler

# WASM

https://github.com/ktock/container2wasm convert container to wasm?

[walloc](https://github.com/wingo/walloc) minimal malloc implementation for wasm. Makes for very small binary?

<https://medium.com/swlh/a-suduko-solving-serverless-endpoint-using-webassembly-and-or-tools-df9f7bb10044>
<https://github.com/google/or-tools/pull/2404>

[walrus](https://docs.rs/walrus/latest/walrus/) webassembly transformation library in rust

[awesome wasm tools](https://github.com/vshymanskyy/awesome-wasm-tools)

[program analysis for web assembly](https://2022.ecoop.org/home/paw-2022#event-overview)

<https://bytecodealliance.org/>

wasmtime - run we assembly outside the
cranelift - optimized code generator for jit and aot. experimental backend to rust.
wamr - webassembly micro runtime. interpeter for embedded and resource constrained
enarx - trusted xecutin environment

## WASI

<https://news.ycombinator.com/item?id=38634258>  Stop Hiding the Sharp Knives: The WebAssembly Linux Interface

Webassembly system interface

### WABT

(likely wascally wabbit) Web assembly binary toolkit
sudo apt install wabt

wasm2wat - binary totextual
wat2wasm - textual to binary
wasm-interp - interpet wasm
wasm-objdump - look at disassembly alongside bits
wasm-decomp

wasm2c - makes wasm file compilable by C cmpiler. Not sure how much partial evaluation it does. I think it uses a wasm runtime still? Sandboxing still? Interesting target for rewriting.

### Running

wasmer vs wasmtime? <https://wasmtime.dev/>
<https://github.com/wasm3/wasm3> another competitor? An interpeter?

wasmer?
Wait wasmer is a startup?
<https://news.ycombinator.com/item?id=27537541> zig as a wasm compiler for wasm C?
wasmer hello.wasm -i helloWorld
wasmtime

Simple javascript opening - instantiate streaming with fetch api.
You can directly compile WAT in browser.

wat2wasm hello.wat
 wasmer  hello.wasm -i mysquare 4
default wasmer is run. -i is invoke

<https://github.com/AssemblyScript/wabt.js> a port of wabt to assemblyscript

### Wasm modules

 interesting fields in module
 state
 memory
 data
 element adds stuff to table
 tables
 funcs

<https://wapm.io/> package manager - runs examples in browser?

### Writing Wasm directly

Named parameters vs anonymous.
Stack style vs "lispy" style

- <https://developer.mozilla.org/en-US/docs/WebAssembly/> Understanding_the_text_format
- <https://learnxinyminutes.com/docs/wasm/>
- <https://blog.scottlogic.com/2018/04/26/webassembly-by-hand.html> - writing wasm by hand
- <https://blog.scottlogic.com/2019/05/17/webassembly-compiler.html> - making a webassembly compiler

Books:

- <https://livebook.manning.com/book/webassembly-in-action/chapter-1/>
- Oreilly book is most current one?
- The Art of Webassembly - no starch press

```wat
 (; block comment ;)
 ;; line comment
(module
    ;; (memory 1) ;; generally things seems to take names $foo or can be referred to by index.
    ;; 1 means 1 page big. 
  ;;(global $g (import "js" "global") (mut i32))
  (func (result i32)
    (i32.const 42)
  )
  (func $mysquare (param $x i32) (result i32) 
    (i32.mul (local.get $x) (local.get $x))
   )
  (func (result i32)
     (call $mysquare (i32.const 42))
  )
  (func $fact (param $x i32) (result i32)
    (local $acc i32)
    (local.set $acc (i32.const 1))
    (block $done ;; out breaking block
        (loop ;; "loop" block
            (local.set $acc (i32.mul (local.get $x) (local.get $acc)))
            (local.set $x (i32.sub (local.get $x) (i32.const 1)))
            (i32.eqz (local.get $x))
            (br_if $done)
            (br 0)
        )
        )
        (return (local.get $acc))
  )
  (func $mymain)
  (export "helloWorld" (func 0))
  (export "mysquare" (func $mysquare))
  (export "fact" (func $fact))
  (start $mymain)


  
)
```

manual linking of webassembly by passing instantiated modules to other modules. That's cool.

import external functions
export internal definitions

<https://github.com/WebAssembly/wasi-sdk>
wasi-sdk vs emscripten vs binaryen
WASI I guess is kind of like POSIX system calls or libc in some respects?

Ok you can directly execute .wat files
wat2wasm --debug-names puts debug names into Custom section of wasm file

<https://wasdk.github.io/wasmcodeexplorer/> explore web assembly binary. highlights different pieces
<https://webassembly.studio/>

assemblyscript - an annotated version of typescript that compiles directly-ish to wasm

binaryen - an optmizing compiler that accepts some kind of cfg or wasm. Has C api.
wasm-opt will optimize wasm for me
wasm2js

# Emscripten

Finicky process.
There are sections in the above books about this
C++ exceptions and threads are something to look for.

Tips:

- `emccmake cmake yada yada`

You may need to puts flags into cmake projects.
You may need to shield things in your code undo macros

```
#ifndef EMSCRIPTEN

#endif
```

More often than not it is linking flags.

Some things are easier or harder on node vs web. You should try both.

Often you need to play with the filesystem FS to make sure stuff exists.

### Command line Utility Conversion

By default, emscripten refers to a global object called `Module`. You can create one with various flags and arguments.

```
<script>
var Module = {
   "print" : function(text){console.log(text)},
   "printErr" : function(text){console.error(text)},
   

}
</script>

<script src="myemscrtipt.js"></script>
```

You can add arguments, add to the file system, etc.

You may not want to thing to run as soon as the script tag is run. There is

`-sMODULARIZE` is a linking option

emcmake cmake -DCMAKE_EXE_LINKER_FLAGS="-sEXPORTED_RUNTIME_METHODS=ccall,cwrap -sEXPORTED_FUNCTIONS=_main"

### Souffle

emcmake cmake -S . -B build_wasm -DSOUFFLE_USE_SQLITE=OFF -DSOUFFLE_USE_OPENMP=OFF -DSOUFFLE_USE_ZLIB=OFF -DSOUFFLE_USE_LIBFFI=OFF -DSOUFFLE_USE_CURSES=OFF -DSOUFFLE_ENABLE_TESTING=OFF -DSOUFFLE_TEST_EVALUATION=OFF

-Wno-error

-DCMAKE_BUILD_TYPE=MinSizeRel

Needed to go into src/CMakeLists.txt and remove -Werror from

Is it actually using my flag?

cd /home/philip/Documents/prolog/souffle/build_wasm/src && /usr/bin/cmake -E cmake_link_script CMakeFiles/souffle.dir/link.txt --verbose=1
/home/philip/Documents/prolog/emsdk/upstream/emscripten/em++  -sMAIN_MODULE=2 -stdlib=libc++ -O3    -fuse-ld=lld -lc++abi @CMakeFiles/souffle.dir/objects1.rsp  -o souffle.js @CMakeFiles/souffle.dir/linklibs.rsp

Todo:
Support dlopen. MAIN_MODULE=2 somehow should work but maybe need -fpic on entire build?

Modularize=1 was important to get multiple runs independent
--no-proprocessor
-D -
Exposing the filesystem

It turns out link flags is where you put this stuff in cmake file. makes sense.

I believe you can renamed the module
<https://stackoverflow.com/questions/33623682/how-to-use-fs-when-modularize-and-export-name-are-used-in-emscripten>
-s EXPORT_NAME="'SOUFFLE'"

## Minizinc

It just worked. Incredible
Runnnig the file didn't do anything.
I needed to do

```
const lib = require("./minizinc.js");
//var MINIZINC = {arguments: ["--help"]};
console.log(lib());
```

on node

It seems like it was grabbing my node parameters.

In the browser, I was able to load in and pass in a Module object
MINIZINC({arguments : ["--help"]})

Trying to build gecode
emcconfigure ../configure
emmake make -j8

gecode build suggestions for emscripten
<https://github.com/Gecode/gecode/issues/67>
Hmm. They build a minizinc for wasm somewhere
<https://gitlab.com/minizinc/minizinc-js>
<https://www.npmjs.com/package/minizinc/v/1.0.4-alpha.77>

Ah I need release/6.3.0 branch which has the const fix.

# Misc

[MSWasm: Soundly Enforcing Memory-Safe Execution of Unsafe Code](https://arxiv.org/pdf/2208.13583.pdf)

<https://github.com/AlexAltea/capstone.js>
<https://github.com/bordplate/js86>
<https://github.com/AlexAltea/unicorn.js>
<https://github.com/AlexAltea/libelf.js>

Wasm baby

<https://www.minizinc.org/doc-2.5.5/en/installation_detailed_wasm.html> minizinc
graphviz
or-tools <https://github.com/google/or-tools/pull/2404/files>

The wasm reference interpeter is in ocaml
<https://github.com/WebAssembly/spec/tree/master/interpreter>

What could be cool?
SAT solver

Analysis on wasm
<https://github.com/synacktiv/toy-wasm-symbexp> toy symbolic executor in haskell

<https://github.com/WebAssembly/wabt> binary toolkit

How do you just run a command line tool in the browser?

<https://kripken.github.io/llvm.js/demo.html>

compiling miniznic
source yadayada./emsdk_env.sh
<https://www.minizinc.org/doc-2.5.5/en/installation_detailed_wasm.html>

mkdir build
cd build
emcmake cmake -DCMAKE_BUILD_TYPE=MinSizeRel ..
emmake cmake --build .

Hmm runnign with node does nothing.
I need to make a wrapper to call MINIZINC()
It needs to be in an mjs file

Lots of important stuff is in the api reference
Module, FS

[wasmcloud](https://wasmcloud.com/)

<https://stackoverflow.com/questions/48292269/how-can-i-run-an-interactive-program-compiled-with-emscripten-in-a-web-page>

<https://browsix.org/>

<https://xtermjs.org/>

<https://bellard.org/jslinux/>

<https://microsoft.github.io/monaco-editor/>

<https://github.com/jcubic/jquery.terminal> - for making web based terminals. Alternaitve for some pruposes to xterm.js

<https://news.ycombinator.com/item?id=29376105> compiling stock python to wasm
pyiodide

[cheerp](https://leaningtech.com/cheerp/) - an alternative to emscripten?

[webvm](https://medium.com/leaningtech/webvm-client-side-x86-virtual-machines-in-the-browser-40a60170b361) JIT compilation of stock x86 in the brwoser. Apparently higher perfomance than bessard's jslinux [hacker news discussion](https://news.ycombinator.com/item?id=30167403)

[virtual x86](https://copy.sh/v86/) a similar open source project but slower?

[postgres wasm](https://news.ycombinator.com/item?id=33067962)

sqlite fiddle

[official sqlite](https://news.ycombinator.com/item?id=33374402)

Wave - a verified wasi interface

<https://news.ycombinator.com/item?id=33385007> cowasm? another emscrtipen alternative based on zig somehw?

[tangle](https://github.com/kettle11/tangle) autosyncing of wasm state across multiple comps
