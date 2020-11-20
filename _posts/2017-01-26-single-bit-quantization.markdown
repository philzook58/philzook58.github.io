---
author: philzook58
comments: true
date: 2017-01-26 04:20:32+00:00
layout: post
link: https://www.philipzucker.com/single-bit-quantization/
slug: single-bit-quantization
title: Single Bit Quantization
wordpress_id: 623
---

I'd heard that pifm, the raspberry pi radio pin thing used 1-bit quantization techniques. I was wondering what they were.

The basic idea of no free lunch states that you can trade the very high speed excess of a fast digital circuit for more effective bit depth of reconstruction.

A natural technique is pulse width modulation, but then you need an integration stage. Low pass filtering elements are more common. Sigma-Delta conversion is a technique that pushes quantization noise into higher frequencies such that a low pass filter will reconstruct the signal well. Pins natural have capacitance so you might get a low pass filter with no external circuitry at all if you're going really ghetto.

I did some things with dithering and Sigma-delta in python. Interesting.

[https://github.com/philzook58/python/blob/master/python/Sigma_Delta_Quantization.ipynb](https://github.com/philzook58/python/blob/master/python/Sigma_Delta_Quantization.ipynb)

Some scattered thoughts:

When sampling a signal into the digital world, you have to break it up into finite discrete chunks.

This distorts the thing. Question is how much and how should you do it?

[http://repository.upenn.edu/cgi/viewcontent.cgi?article=1144&context=ese_papers](http://repository.upenn.edu/cgi/viewcontent.cgi?article=1144&context=ese_papers)

The simplest scheme is to break the signal up into expected intervals and count them off.

This does not get all out of the signal.

One model for discussing this is quantization noise. We can assume that the error introduced is uncorrelated with the input and is just additive noise.

If it's quantized in steps of $latex \Delta$

$latex \Delta$

6n dB. For n bits be get another 6n of signal to noise.

[http://www.cs.tut.fi/sgn/arg/rosti/1-bit/](http://www.cs.tut.fi/sgn/arg/rosti/1-bit/)



Update: This seems like an interesting resource to dig into

[http://www.python-deltasigma.io/](http://www.python-deltasigma.io/)
