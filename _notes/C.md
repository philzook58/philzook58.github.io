

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

# C++

Cherno 
Cyril Stachniss https://www.youtube.com/c/CyrillStachniss/videos


Class vs struct
Smart pointers
new/delete ~ malloc + constructor caling
static
const
virtual 
interfaces - classes that are all virtual methods
name mangling

precompiled headers (pch)



## Build Systems
Shake
