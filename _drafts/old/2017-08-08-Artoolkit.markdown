---
author: philzook58
comments: true
date: 2017-08-08 16:38:58+00:00
layout: post
link: https://www.philipzucker.com/?p=787
published: false
slug: Artoolkit
title: Artoolkit
wordpress_id: 787
---

Downloaded ARtoolkit5

https://archive.artoolkit.org/documentation/doku.php?id=1_Getting_Started:about_installing

ran ./Configure

used video4linux2 and kept gcc. Not sure if smart choices. Didn't use the rest.

then make

error: ‘CV_CALIB_CB_ADAPTIVE_THRESH’ was not declared in this scope

Hooboy. Is opencv 2.x required rather than 3.x?

Or was this because I didn't use clang?

make clean and starting over

apt-get installed clang

build failed missing memory.h file

    
    <code><span class="pln">sudo apt</span><span class="pun">-</span><span class="pln">get install libc</span><span class="pun">++-</span><span class="pln">dev</span></code>


ok another problem occurred with the build at basic_string 1938

https://stackoverflow.com/questions/37096062/get-a-basic-c-program-to-compile-using-clang-on-ubuntu-16/37097327

Until the Debian bug mentioned in Mike Kinghan's reply is fixed, just adding the missing (but required) `noexcept` specification to the ctor definition manually allows to work around the problem, i.e. you could just add

    
    <code><span class="com">#if _LIBCPP_STD_VER <= 14</span><span class="pln">
        _NOEXCEPT_</span><span class="pun">(</span><span class="pln">is_nothrow_copy_constructible</span><span class="str"><allocator_type></span><span class="pun">::</span><span class="pln">value</span><span class="pun">)</span>
    <span class="com">#else</span><span class="pln">
        _NOEXCEPT
    </span><span class="com">#endif</span></code>


after the line 1938 of `/usr/include/c++/v1/string`.

Literally add it after line 1938. You'll need to sudo. This syntax means nearly nothing to me.ls

simpleLite is in the bin folder

https://archive.artoolkit.org/documentation/doku.php?id=7_Examples:example_simplelite

I aimed my webcam at the hiro pattern onscreen. I had to ctrl-minus the image to make it smaller.

Make sure you have good border on the image.






