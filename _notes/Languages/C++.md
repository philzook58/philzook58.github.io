---
layout: post
title: C++
---

<https://learnxinyminutes.com/docs/c++/>

```cpp
#include <iostream>
#include <vector>
#include <set>
#include <map>
#include <tuple>
using namespace std;
int main(){
    cout << "hello world" << std::endl;
    auto myvec = vector<int>{1,2,3,4,5};
    myvec.push_back(6);
    for (auto i : myvec){
        cout << i << " ";
    }
    pair<int, int> biz = {1,2};
    map<string, int> bar = {{"one", 1}, {"two", 2}};
    bar.get("poop");
    for (auto [key, value] : bar){
        cout << key << " " << value << endl;
    }
    tuple<int,float,double> baz = {1, 2.0, 3.0};
    return 0;
}

```

<https://en.cppreference.com/w/cpp>

# std

string_view
const
regex
fstream

iterators `s.rbegin`
`for(auto c : mystr)`

`std::map mymap = {{1,"ffrd"}}`

shared_ptr
unique_ptr
weak_ptr

<https://github.com/mortennobel/cpp-cheatsheet>

## ranges

# Boost

# constexpr

[consetexpr maze](https://twitter.com/Cor3ntin/status/1507860690400419842?s=20&t=GsM8M-fHdbvp9M4n5S4-kg)
[constexpr interpeter](https://twitter.com/cfbolz/status/1506182747584401411?s=20&t=GsM8M-fHdbvp9M4n5S4-kg)

# Observable behavior

<https://en.cppreference.com/w/cpp/language/as_if> as if rule
<https://en.cppreference.com/w/c/language/eval_order> eval order

# Build

cmake

[conan C/C++ pakcage manager](https://conan.io/)
[vcpkg](https://vcpkg.io/en/index.html) <https://github.com/microsoft/vcpkg>

# Misc
<https://github.com/andreasfertig/cppinsights>

<https://github.com/verateam/vera> I dunno about thizs one. Programmable tool for verification analysis

<https://github.com/shuaimu/borrow-cpp/> borrow checker for c++

<https://github.com/federico-busato/Modern-CPP-Programming> modern cpp course

[exceptions under the hood](https://monoinfinito.wordpress.com/series/exception-handling-in-c/)

Cherno
Cyril Stachniss <https://www.youtube.com/c/CyrillStachniss/videos>

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

[Folly](https://github.com/facebook/folly) - something similar by facebook <https://news.ycombinator.com/item?id=29841271>

Google test

google bench

<https://github.com/microsoft/GSL> GSL: Guidelines Support Library
