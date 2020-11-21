---
author: philzook58
comments: true
date: 2016-09-03 20:42:46+00:00
layout: post
link: https://www.philipzucker.com/?p=500
published: false
slug: Stack and Yesod
title: Stack and Yesod
wordpress_id: 500
---

Trying out some Stack

https://docs.haskellstack.org/en/stable/README/

I like it so far.

Added

    
    library
      hs-source-dirs:      src
      exposed-modules:     Lib
      build-depends:       base >= 4.7 && < 5,
                           yesod


ran stack build.

Holy balls it is doing a lot.

K I'm a dummy. You need to put it in the build-depends of the actual executable, not the library.
