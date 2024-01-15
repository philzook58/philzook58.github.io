
<https://arcana-research.io/shiva/>

<https://tmpout.sh/2/6.html> preloading the linker

<https://arcana-technologies.io/blog/the-philosophy-of-elves-in-linux-threat-detection/>

kprobe
ecfs
binary protector
kernel rootkit

dynamic linker fuzzing

<https://bitlackeys.org/#research>

```bash
echo "int foo(){
    return 42;
}
" | gcc -O1 -c -o /tmp/foo.o -x c -
objdump -d /tmp/foo.o
```

```bash
echo "
#include <stdio.h>
#include <stdint.h>
#include <sys/mman.h>
#include <string.h>

uint8_t foo[] = {
   0xf3, 0x0f, 0x1e, 0xfa,              //  endbr64 
   0xb8, 0x2a, 0x00, 0x00, 0x00,        //  mov    $0xa,%eax
   0xc3                    //  ret    
};

int main(){
    printf(\"hello world\n\");
    void* ptr = mmap(NULL, 4096, PROT_READ | PROT_WRITE | PROT_EXEC, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    memcpy(ptr, foo, sizeof(foo));
    int (*func)() = ptr;
    int retval = func();
    printf(\"%d\n\", retval);

    return 0;
}
" | gcc -Wall -Wextra -o /tmp/a.out -x c -

/tmp/a.out
```

<https://discourse.llvm.org/t/rfc-exposing-ghccc-calling-convention-as-preserve-none-to-clang/74233/28>

```bash
echo "
int f(int x);
__attribute__((regcall)) int foo(int x, int y, int z, int w){
    [[clang::musttail]] return f(x + y + z + w);
}
" | clang -O1 -c -o /tmp/foo.o -x c -



```

<https://sillycross.github.io/2023/05/12/2023-05-12/>

ifunc <https://sourceware.org/glibc/wiki/GNU_IFUNC>
<https://maskray.me/blog/2021-01-18-gnu-indirect-function>

```
int get_x();
int get_y();
int f(int x);
int foo(){
    int x = get_x();
    int y = get_y();
    return f(x + y);
} " | gcc -fPIC 

```

```bash
#/lib/ld-linux.so.2 --list /bin/ls
/lib64/ld-linux-x86-64.so.2 --list /bin/ls
```

```

examining stuff just "printf" style seems kind of nice. I don't like using gdb even for normal stuff.
