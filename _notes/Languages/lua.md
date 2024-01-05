---
layout: post
title: Lua
---

Lua is an easily embeddable scripting language. Hence it shows up in lots of other projects

LUAJit is suppposed to be a very impressive JIT implementation

<https://lucasklassmann.com/blog/2019-02-02-embedding-lua-in-c/>

`sudo apt install liblua5.4-dev`

```bash
echo '
#include <lua.h>
#include <lualib.h>
#include <lauxlib.h>

int main(int argc, char ** argv) {

    lua_State *L = luaL_newstate();
    luaL_openlibs(L);

    lua_close(L);
    return 0;
}
' > /tmp/mylua.c
gcc -o /tmp/mylua /tmp/mylua.c -I/usr/include/lua5.4 -llua5.4
/tmp/mylua

```
