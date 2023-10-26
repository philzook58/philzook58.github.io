---
layout: post
title: Binary Patching
---


Binary patching is an intimidating sounding topic. It is very low level and requires lots of fiddly little knowledge.

# Replacing and Deleting Code

Our first example is trying to patch a simple constant change.

```C
int foo(int x){
    return x + 1;
}

int foo_patched(int x){
    return x + 2;
}
```

```bash
echo "
int foo(int x){
    return x + 1;
} " > /tmp/foo.c
gcc -O1 /tmp/foo.c -c -o /tmp/foo.o
objdump -d -F /tmp/foo.o # -F shows offsets which helps us find the right place to patch
```

```asm
0000000000000000 <foo> (File Offset: 0x40):
   0:   f3 0f 1e fa             endbr64 
   4:   8d 47 01                lea    0x1(%rdi),%eax
   7:   c3                      ret    
```

Looking at it, I suspect that 0x1 corresponds to the 1 in the binary.
We can confirm by using the assembler to change that instruction and look at the output binary

```bash
echo "lea    0x2(%rdi),%eax" | as -o /tmp/toy - 
objdump -d /tmp/toy
```

We can then patch using `xxd`

```bash
echo "0000044: 8d4702" > /tmp/foopatchfile
xxd -r /tmp/foopatchfile /tmp/foo.o
objdump -d /tmp/foo.o
```

Using C compiler to generate helpful assembly.

The basic questions are:

1. Where to read info you need
2. Where writes need to go
3. What cannot be clobbered.

C compilers do not compile program fragments. They must be in function bodies. Nevertheless it can be very illuminating

If your variables need to read from registers, make them arguments to functions.
Make globals for things that need to be read from memory or use varargs to see how to read from the stack.
If your variables need to be written to registers, make them arguments to called functions.

In this way, you can get a starting point of decent assembly code you can manipulate.

Suggestions on how to be more careful
Save the objdump. Edit it to match your expectations. Do your patching, then diff this objdump with your intended objdump.

Suggestions on maintenance: Add a section to the patched binary documenting your edit.

## Tools

Ghidra makes for a much nicer experience

Hex editors mean you don't have to fiddle with `xxd`. VS Code has one for example.

You can also use `xxd` to dump the entire hex file, edit it, and then rebinarize it.

```bash
xxd -s 0x40 -l 8 /tmp/foo.o > /tmp/foo.o.hex
nano /tmp/foo.o.hex
```

## Fusing out a password check

```C
int patch_fun(char *passwd){
    if(strcmp(passwd, "MyGoodPassword7") == 0){
        return 0;
    }
    else{
        return -1;
    }
}

int patch_fun(char *passwd){
    if(0 == 0){
        return 0;
    }
    else{
        return -1;
    }
}


int main(){
    char* password = "MyGoodPassword";
    return patch_fun(password);
}
```

## Patching a Call

```C
int ret_3() { return 3; }

int ret_5() { return 5; }

int main() {
  return ret_5();
}

int main_patched() {
  return ret_3();
}
```

## Changing a Type

This is a nightmare.

```C

int foo(int x){
  if(x > 0){
    return 2;
  }
  else{
    return 1;
  }
}

int foo(unsigned int x){
  if(x > 0){
    return 2;
  }
  else{
    return 1;
  }
}

int main() {
  return foo(-1);
}
```

# Adding Code

We could make this harder. Now there won't be code to twiddle. Really we are adding functionality.

```C
int foo(int x){
    return x;
}

int foo_patched(int x){
    return x + 1;
}

```

### Code Caves

Clobber unused code. Maybe require patching that code too. Big enough binaries are full of junk. Get a symbol dump and maybe ask chatgpt.
Maybe just maybe there's a pile of nops somewhere. Look for them
Superoptimize some code that is

Elf padding
Add new segment

Virus techniques tend to be applicable, but we're using them for good right? Viruses need to find ways to add exectuable code too. We don't care about detection.

You tend to want space closer rather than farther from your patch point

Make the file relinkable via that weird project?

## Add Bounds Check

```C
int patch_fun(int a[],int i){
    return a[i];
}

int patch_fun(int a[],int i){
    if(i < 3 && i >= 0){
        return a[i];
    }
    return -1;
}

int main(){
    int x[] = {5,4,3};
    return patch_fun(x, 3);
}
```

## Null Ceck

```C
#include <stddef.h>


int patch_fun(int *x){
    return *x;
}

int patch_fun(int *x){
    if(x == NULL){
        return -1;
    }
    return *x;
}

int main(){
    int x = 5;
    return patch_fun(&x);
}
```

# Resources

<https://program-repair.org/index.html>

<https://codeflaws.github.io/> Nice chart of small patches
![](https://codeflaws.github.io/images/dtable-1.png)
