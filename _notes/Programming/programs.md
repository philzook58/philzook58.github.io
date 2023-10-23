---
layout: post
title: Programs
---


```C

/*@
2 requires \valid(a) && \valid(b);
3 assigns *a, *b;
4 ensures *a == \old(*b);
5 ensures *b == \old(*a);
6 */
7 void swap(int* a, int* b){
8 int tmp = *a;
9 *a = *b;
10 *b = tmp;
11 }
12
13 int main(){
14 int a = 42;
15 int b = 37;
16
17 swap(&a, &b);
18
19 //@ assert a == 37 && b == 42;
20
21 return 0;
22 }
```

## strlen
<https://stackoverflow.com/questions/57650895/why-does-glibcs-strlen-need-to-be-so-complicated-to-run-quickly>

```C

#include <string.h>

size_t
strlen(const char *str)
{
    const char *s;

    for (s = str; *s; ++s)
        ;
    return (s - str);
}
```
