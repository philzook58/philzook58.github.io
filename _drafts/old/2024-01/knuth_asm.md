
```bash
echo '
#include <sys/syscall.h>
.extern _start
_start:
    mov $0x20,%rax
    int3
    mov $0x42,%rax
    mov $60, %rax # exit syscall number
    syscall
    int $0x80
    #int3
' > /tmp/myprog.s
gcc -nostdlib -static -o /tmp/myprog /tmp/myprog.s
qemu-x86_64 -d in_asm,cpu -singlestep /tmp/myprog

```
