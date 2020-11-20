---
author: philzook58
comments: true
date: 2015-10-21 00:08:26+00:00
layout: post
link: https://www.philipzucker.com/bootstrapping-myself-into-rf/
slug: bootstrapping-myself-into-rf
title: Bootstrapping myself into RF
wordpress_id: 206
---

I've dreamed radio dreams for many years.

I think I'm closer than ever to being able to goof around in the RF.

Previously I've taken a too low level approach, trying to build my own oscillators and amplifiers. Certainly doable, but not the easiest, and not actually the thing I'm most interested in.

The revelation came when I saw [this](http://ocw.mit.edu/resources/res-ll-003-build-a-small-radar-system-capable-of-sensing-range-doppler-and-synthetic-aperture-radar-imaging-january-iap-2011/) mit radar building guide. They're using little blocks that I understand from microcircuits. I think that's one of the easier ways into the high frequency regime.

So I went a huntin on ebay and bought anything that sounded reasonable. VCO, mixer, LNA. One tripping point was that I had no way to measure anything. My oscilloscope only goes up to 100Mhz.

So I bought a frequency Counter and Power Meter for real cheap.

The frequency counter works. Try wiggling between high and low mode and turning the filter off. It picked up my 2Mhz function generator signal and also the signal off the VCO I bought, which goes from 90Mhz to 190Mhz ish.

With the pin connector on the left the top is control, the two middle are ground and the bottom is power


