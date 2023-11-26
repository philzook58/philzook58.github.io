---
layout: post
title: Zig
---


<https://blog.logrocket.com/getting-started-zig-programming-language/>
`snap install zig --classic --beta`

`zig init-exe`
`zig translate-c`

```zig
//re
const std = @import("std");

pub fn main() void {
    std.debug.print("Hello Zig!\n", .{});
    std.debug.print("Hello {}\n", .{2023}); // Hello 2023
    std.debug.print("Hello {s}! {d}\n", .{"Zig", 2023}); // Hello Zig! 2023

    var x: i8 = -100;     // Signed 8-bit integer
    var y: u8 = 120;      // Unsigned 8-bit integer
    var z: f32 = 100.324; // 32-bit floating point

    std.debug.print("x={}\n", .{x});        // x=-100
    std.debug.print("y={}\n", .{y});        // y=120
    std.debug.print("z={d:3.2}\n", .{z});   // z=100.32
    
    const LogType = enum {
        info,
        err,
        warn
    };

    const ltInfo = LogType.info;
    const ltErr = LogType.err;

    std.debug.print("{}\n", .{ltInfo}); // main.main.LogType.info
    std.debug.print("{}\n", .{ltErr});  // main.main.LogType.err

}
fn add(a: i8, b: i8) i8 {
    return a + b;
}
```

zigzap/zap: A micro-framework for building web backends
JakubSzark/zig-string: A string library for Zig
kooparse/zalgebra: Linear algebra library for games and real-time graphics
zigimg/zigimg: Zig library for reading and writing different image formats
ziglibs/ini: A simple INI parser for Zig

<https://github.com/C-BJ/awesome-zig>

Good C interop supposedly. Such that you don't really need to write bindings?
`c_int`

No libc by default but easy to add in

```zig

```

ReleaseSafe mode detects undefined behavior.

# Comptime

Cool oppurtunirty for some staged metapgoramming stuff right?
Like KMP, parsers, etc
Generics are calculated types which feels a bit mindblowing (?)
Maybe that is'nt that crazy from system f perspective

# Allocators
