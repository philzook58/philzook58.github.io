---
layout: post
title: C/C++
---
[Beej's Guide to C](https://beej.us/guide/bgc/)

<https://stackoverflow.com/questions/7237963/a-c-implementation-that-detects-undefined-behavior>
See compcert and frama-c

static keyword


gcc flags
-E stop after preprcoessor. #include literally includes header file
-s output assembly (don't assemble)
-c output object file


gcc -shared foo.o -o foo.so  - makes a dynamically linkable file. You actually have to make a object file first before you do this

g++ _is_ gcc with some appropriate flags set for C++

`-lgsl` is the same as `-l gsl` and looks in system paths for a file called `libgsl.o`. It automatically appends `.o` and `lib`. Very odd to my sensibilities.

`-I` is useful to help 

Header files and prototypes actually become "code" in the sense they are entries in the object file.

### CPP

The C preprocessor.

It can be run on its own

- `#include` literally brings that file in. `<>` vs `""` is a difference in what search path it uses an prioritizes.
- `#define` 
mcpp is an alternative


It can be programmed. This is typically ill adviuced <http://conal.net/blog/posts/the-c-language-is-purely-functional> An amusing essay saying that cpp is a pureply function programminbg language

`__COUNTER__` is an autoincrementing thing
There are things for string concatenation

### Make
- <https://learnxinyminutes.com/docs/make/>
- <http://swcarpentry.github.io/make-novice/>

An amusing essay that `make` is logic programming language. It is true.
The file system is the database of sorts.


There is a default makefile that is included with every make invocation if you don't turn it off.



### CMake
<https://learnxinyminutes.com/docs/cmake/>

<https://www.youtube.com/watch?v=zOmUHM0sFOc&ab_channel=CyrillStachniss>


# Loading 
<https://news.ycombinator.com/item?id=29104841> <http://dbp-consulting.com/tutorials/debugging/linuxProgramStartup.html>

# Sanitization
Dynamic Bug detection technique
[SoK](https://oaklandsok.github.io/papers/song2019.pdf) sanitizing for security. Really interesting.

https://github.com/google/sanitizers/wiki
Address sanitizer [ASAN](https://en.wikipedia.org/wiki/AddressSanitizer) 
[memory snatizier](https://clang.llvm.org/docs/MemorySanitizer.html) -fsanitize=memory
https://github.com/google/sanitizers
ThreadSanitizier - detect race conditions
UBSan undefine behavior sanitizer

valgrind
SAFECode, and SoftBound

See also notes on CTF stuff and compilers

Shadow memory. mapping of memory to shadow memory where you can hold metadata.
Guard pages - try to access an overflow and hit unmapped page, you'll crash

fat pointers - make pointer a struct
tagged pointer - use unused bits in pointer. 64 bits is too many. ALignment makes low bits unused

# C++

Cherno 
Cyril Stachniss https://www.youtube.com/c/CyrillStachniss/videos

[nice C++ cheat sheets](https://hackingcpp.com/cpp/cheat_sheets.html) 

Class vs struct
Smart pointers
new/delete ~ malloc + constructor caling
static
const
virtual 
interfaces - classes that are all virtual methods
name mangling

precompiled headers (pch)

```cpp
#include <iostream>
int main(){
    std::cout << "hello world" << std::endl;
    std::cout << [](int x){ return x * 42; }(2); // lambda


    return 0; // don't have to though
}
```

[fmt library](https://github.com/fmtlib/fmt) C++20 has this in `#include<format>` ?

## Build Systems
Shake
https://www.microsoft.com/en-us/research/uploads/prod/2018/03/build-systems.pdf build systems a la carte
