---
layout: post
title: C++
---

# constexpr
[consetexpr maze](https://twitter.com/Cor3ntin/status/1507860690400419842?s=20&t=GsM8M-fHdbvp9M4n5S4-kg)
[constexpr interpeter](https://twitter.com/cfbolz/status/1506182747584401411?s=20&t=GsM8M-fHdbvp9M4n5S4-kg)

# Observable behavior
https://en.cppreference.com/w/cpp/language/as_if as if rule
https://en.cppreference.com/w/c/language/eval_order eval order
# CMake

# Misc

[exceptions under the hood](https://monoinfinito.wordpress.com/series/exception-handling-in-c/)

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

`extern "C"` blocks prevent name mangling for ffi purposes.


[embracing modern c++ safely](https://news.ycombinator.com/item?id=31559118)

[hidden cost of C++ exceptions](https://grenouillebouillie.wordpress.com/2022/05/09/the-hidden-cost-of-exception-handling/) if you torture the compiler



[Abseil](https://abseil.io/) - google C++ stdlib

[Folly](https://github.com/facebook/folly) - something similar by facebook https://news.ycombinator.com/item?id=29841271

[conan C/C++ pakcage manager](https://conan.io/)
[vcpkg](https://vcpkg.io/en/index.html)

Google test

google bench