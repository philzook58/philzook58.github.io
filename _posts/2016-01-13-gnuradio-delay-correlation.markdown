---
author: philzook58
comments: true
date: 2016-01-13 22:05:40+00:00
layout: post
link: https://www.philipzucker.com/gnuradio-delay-correlation/
slug: gnuradio-delay-correlation
title: Gnuradio Delay Correlation
wordpress_id: 371
---

Trying to develop some software for coherent rtl synchronization. This is the first step, using internal gnuradio signal sources. Thinking that'll we'll use this setup + a synchronize button that will set the current delay. Or maybe sliders. Would kind of suck to have to synchronize manually every time, but not horrible. Maybe the synchronize button will set the slider values to the appropriate places. And could enable or disable all the extra processing with valve. Okay, did that. Set True to 0 default to 0 and false to 1 in gui checkbox. Then run that variable into the valve leading into all the correlation stuff.

Check this out. Learned some things. Stream to Vector packs such and such samples into a stream of vectors. Kind of ubiquitous in gnu radio, so I'm not sure why I didn't know about this already.

That is what you need for the fft

When you change the vector size, you need to change the window size parameter in the fft too or else you get an error.

[![delay_test.grc](http://philzucker.nfshost.com/wordpress/wp-content/uploads/2016/01/delay_test.grc_-300x240.png)](http://philzucker.nfshost.com/wordpress/wp-content/uploads/2016/01/delay_test.grc_.png)



https://en.wikipedia.org/wiki/Cross-correlation

You'll see that one way to calculate it is to fourier transform, conjugate multiply, then inverse fourier transform. We then plot this on a vector sink. And use the argmax to find the peak delay. It works really damn well in this simulation, but real world performance is to be determined. When the total delay is more than ~800 using vector size of 2048, it loses the peak. Negative delay wraps around back. That dip in the correlation is almost certainly due to the windowing done by the fft.
