---
author: philzook58
comments: true
date: 2015-11-22 21:16:52+00:00
layout: post
link: https://www.philipzucker.com/folgertech-prusa-update-2/
slug: folgertech-prusa-update-2
title: Folgertech prusa update
wordpress_id: 257
---

SO, it turns out we've been printing mirror images of parts somehow. We just printed raspberry pi cases and they don't fit. I suppose we had been printing parts that are too symmetrical to observe this before.

What's extra bizarre is this makes the coordinate system of the printer not right handed. Now the maximum of x is towards the power supply side.

We played with some stuff in the marlin configuration file

Removed the #define disable_max_endstops line

#define INVERT_X_DIR true

#define X_HOME_DIR 1

Seems ok now.
