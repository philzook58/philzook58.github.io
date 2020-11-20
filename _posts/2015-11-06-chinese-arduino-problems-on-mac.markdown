---
author: philzook58
comments: true
date: 2015-11-06 19:45:11+00:00
layout: post
link: https://www.philipzucker.com/chinese-arduino-problems-on-mac/
slug: chinese-arduino-problems-on-mac
title: Chinese Arduino Problems on Mac
wordpress_id: 241
---

Followed instructions here. You need some drivers.

[http://0xcf.com/2015/03/13/chinese-arduinos-with-ch340-ch341-serial-usb-chip-on-os-x-yosemite/](http://0xcf.com/2015/03/13/chinese-arduinos-with-ch340-ch341-serial-usb-chip-on-os-x-yosemite/)

Remember to run that weirdo kext command before you restart

For some reason I couldn't get it to work the first couple times.

I needed to change the symbolic link a little. The thing arduino could actually see was cu.wch. not tty.ch, so just replace it with that.
