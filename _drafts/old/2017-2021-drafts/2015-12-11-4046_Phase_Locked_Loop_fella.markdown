---
author: philzook58
comments: true
date: 2015-12-11 06:11:26+00:00
layout: post
link: https://www.philipzucker.com/?p=299
published: false
slug: 4046 Phase Locked Loop fella
title: 4046 Phase Locked Loop fella
wordpress_id: 299
---

The 4046 is an ic with  a built in voltage controlled oscillator (vco) and phase comparator, the two bits needed to make a phase locked loop.

A phase locked loop is an oscillator that syncs itself up to an incoming periodic signal.

This is useful for demodulating a fm signal. The PLL locks onto the fm speeding up and slowing down the vco the keep up. The input to the vco then tracks the demodulated signal.

On the flip side, we can run a signal into a vco to modulate it into fm.

The thing isn't fast enough to lock onto straight fm radio btw. The vco is limitted to ~1Mhz. However, we can mix the fm radio down to the 10khz range ish or something, and then have our boy figure it out. Eventually I'll do this.



There is an example test circuit for demodulating fm right in the datasheet. To test it, I'm going to use gnu-radio to make an fm modulated signal.

[http://hackaday.com/2015/08/07/logic-noise-4046-voltage-controlled-oscillator-part-one/](http://hackaday.com/2015/08/07/logic-noise-4046-voltage-controlled-oscillator-part-one/)

![](https://hackadaycom.files.wordpress.com/2015/07/simple_vco-sch.png)

This was useful to just get going. The vco is some kind of relaxation oscillator using 3 external components R1, R2, and C1 to set the center frequency.

The formula is

w2aew is the goddamn man



There are two kinds of phase comparators in this chip. PC1 is just an xor gate




