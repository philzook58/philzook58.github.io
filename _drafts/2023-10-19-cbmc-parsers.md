
I'm very impressed by the SV-Comp style solvers, in partcular CBMC.

I thought CBMC might be defunct, since it's main webpage does not show recent development, but actually the github repo is very active. It appears Amazon is investing n it's usage with a number of significant C projects having CBMC based specs ad verification.

It's pretty easy to install and use.

Here's a basic example:

```bash
echo "
#include <assert.h>
#include <stdint.h>

int64_t myabs(int64_t x){
    return x < 0 ? -x : x;
}

int64_t nondet_int64();

int main(){
    int64_t x = nondet_int();
    int64_t y = myabs(x);
    assert(y >= 0);
}

" > /tmp/abs.c
cbmc /tmp/abs.c 
```

[Documentation](https://diffblue.github.io/cbmc//index.html)

```bash
echo "
#include<stdbool.h>

bool check_balance(char *input){
    int count = 0;
    while(*input != '\0'){
        if(*input == '(') count++;
        if(*input == ')') count--;
        input++;
    }
    return count == 0;
" > /tmp/parens.c
cbmc /tmp/parens.c 
```
