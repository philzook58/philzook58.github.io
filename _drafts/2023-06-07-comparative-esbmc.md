

Comparative checking of programs can be useful for reducing both the specification and verification burden.
In addition, there are some relational properties ("hyperproperties") that require talking about two different runs of a program. The canonical example is information security. If you run two programs with identical low security parts of the states, they must end with identical low security parts of the state. This is true if there is only influence or information transferral going from low to high.

- Translation validation
- Refinement
- Security properties
- Bug fixing


The simplest approach to doing comparative verification so is to use the more commonly available single program verifier on the "product program".

[esbmc](http://esbmc.org/) is a C bounded model checker.

```bash
echo '
#include <assert.h>
int safeprog(int low, int high){
    int foo = low ^ high;
    foo = ((foo << 1) ^ high) >> 1;
    return foo;
}

int main(){
    int high = nondet_int();
    int high1 = nondet_int();
    int low = nondet_int();
    //int high, high1, low;

    __ESBMC_assert(safeprog(low,high) == safeprog(low,high1), "information security property");
    return 0;
}
' > /tmp/test.c
esbmc /tmp/test.c
```


There are many bits of software out there that have security vulnerabilities.

Obviously, the easiest and most likely solution is to change the code in source, recompile, and push out the new version.
This is not always possible or desirable however.
- Even recompiling the original program may introduce bugs due to compiler difference versions
- You may not have the source
- 

It is in general an interesting problem to consdier the 50 year software stack.


Worse is better: A use case for dumb compilers








