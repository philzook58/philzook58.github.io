
Idea: pretty printing a global C data structure into the .data section is kind of the eaisest way to turn a textual representation into a binary format

```bash
sudo apt install libdwarf-dev
```

Could also possibly use LLVm dwarf headers?

```bash
echo "
#include <dwarf.h>



" > /tmp/dwarf.c
gcc -I /usr/include/libdwarf/ -c /tmp/dwarf.c -o /tmp/dwarf.o


```

```
#include <dwarf.h>

int main(){
    // open file, go to dwarf entry point.

}

```
