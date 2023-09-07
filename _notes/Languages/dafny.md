---
layout: post
title: Dafny
---

```

method Triple(x : int) returns (r : int) 
ensures r == 3*x {
    var y := 2*x;
    r := y + x;
    assert r == 3*x;
}

method Abs(x: int) returns (y: int)
   ensures 0 <= y
{
   if x < 0 {
      return -x;
   } else {
      return x;
   }
}




```

- multiple returns
- 

Bitvector types
bv1
bv32

var mem : map<bv64, bv8>


[documentation](https://dafny.org/dafny/)

[Quick reference](https://dafny.org/dafny/QuickReference.html)

Program Proofs draft book

# WP

# Function vs Method
Functions are mathemtical functions whose body is transparent to the verifier. Compile time or runtime
Methods only present their pre and post conditions to the solver

# Invariants

# Termination

# ghost variables

# Frames


https://github.com/dafny-lang/compiler-bootstrap


```dafny
{% include_relative dafny/tutorial.dfy %}
```


try doing laff

