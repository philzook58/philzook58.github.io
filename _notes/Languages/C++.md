---
layout: post
title: C++
---

# constexpr
[consetexpr maze](https://twitter.com/Cor3ntin/status/1507860690400419842?s=20&t=GsM8M-fHdbvp9M4n5S4-kg)
[constexpr interpeter](https://twitter.com/cfbolz/status/1506182747584401411?s=20&t=GsM8M-fHdbvp9M4n5S4-kg)

# CMake

# Misc

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