---
author: philzook58
comments: true
date: 2016-01-13 06:14:39+00:00
layout: post
link: https://www.philipzucker.com/?p=370
published: false
slug: Coherent Rtl Receiver
title: Coherent Rtl Receiver
wordpress_id: 370
---

So we've seen a hack where they rip off the crystals of multiple rtls and piggyback them into the the crystal of a master rtl-sdr. Reportedly the max you can do using this method is 2 slaves on 1 master. You can get rtl-sdrs off aliexpress for about 8 bucks.

http://kaira.sgo.fi/2013/09/16-dual-channel-coherent-digital.html

http://yo3iiu.ro/blog/?p=1450

http://superkuh.com/rtlsdr.html

I've seen one which uses capacitors to connect them instead of wires. This makes sense to me as it might block any dc offset occurring between . Also, more importantly, it is actually convenient.

We jumped 0.47uF capacitors, which were the biggest we had that weren't electrolytic. At the 28.8Mhz clock, that is on the order of 0.01ohms, so irrelevant if the capacitors don't have much stray impedances. Our usb hub (also from aliexpress) puts them in position to be jumpered directly using them. All in all, it makes for a pretty tight arrangement.

We also desoldered the mcx connectors to replace them with sma, since we didn't have many mcx to sma converters on hand. It might be al little nicer in some too.

All in all, a nice tight little setup.

We did not get 3 to work. We desoldered one. They weren't working when powered individually, but do work when both are powered, or at least they are recognized by lsusb.

okay, our usb hub was crap. bought a powered amazon basic one.

Was able to get two rtl-sdrs to work with straight connections, no capacitors. Can't seem to get three to work





gnuradio function probe. If we want variables to be set programmatically, I think this is the way to go. Make a integer ramp function. Put it into a histogram binning




