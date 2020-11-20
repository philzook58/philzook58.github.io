---
author: philzook58
comments: true
date: 2018-04-27 14:21:52+00:00
layout: post
link: https://www.philipzucker.com/noise-fluctuation-dissipation-theorem/
slug: noise-fluctuation-dissipation-theorem
title: Noise and The Fluctuation Dissipation Theorem
wordpress_id: 1053
---

I was looking at some slides the other day and they quoted noise power in units of $latex \frac{W}{\sqrt{Hz}}$. Being the ignoramus I am, I was wondering why it was scaled

First off, when a Watt is quoted in an electrical measurement, usually you're measuring Voltage with an instrument with a known input impedance Z. That's how you convert your fluctutating voltage measurement to Watts.

Second, the sqrt frequency thing? Nowadays, your measurement apparatus is probably a digital sampler and it performs an FFT giving you a spectrum. The width of your FFT is the sampling frequency roughly. Does that make sense that when you increase the width of your taken spectrum the height of the noise signal changes too? It does, but only because implicitly, most sampling circuits take an average of the signal over the same period as the sampling time. These two times are not necessarily intrinsically linked. One could have a system that takes a very fast snapshot and but can only save data or send it over a link at a much slower speed. The noise power is this snapshot time, not the data saving time. The data saving time would be the bandwidth in the FFT.

These two are engineered to be the same to avoid distortion of the frequency signal via aliasing.

But there is an even simpler way to see this. Suppose you have two measurements V1 and V2 that are the averages of time T with variance $latex \sigma$. Then the average of these two, V3, is over a time 2T. However, by the standard kind of manipulations (for Gaussian variables the squared variance of a sum = the sum of the squared variances, $latex \sigma^2_{\sum x_i}=\sum \sigma_{x_i}$ ), the variance of the new signal is $latex \sigma/\sqrt{2}$ which means it scales with the time window. Hence multiplying you actual measured variances by the square root of your time window gives you a time window invariant quantity.



While I was thinking about that in the car I realized that the fluctuation dissipation theorem is a mean field theory kind of thing. The fluctuation dissipation theorem feels weird and spooky, but I guess it is ultimately simple (or not).

Mean field theory tries to summarize all the complicated interactions with neighbors with a simple summary. For interacting spins, it tries to summarize as an effective B field from the surrounding spins. Then you have a 1-particle model which you can solve and try to find a self-consistent value of B. Here is a sketch in equations.

$latex H= \sum S\cdot S - B_{ext}\cdot S \rightarrow \sum - B_{eff}\cdot  S $

$latex Z=\sum_s e^{-\beta H}$

$latex M = <S> = \partial_{\beta B} \ln(Z)$

$latex B = \alpha M$

You can do something similar to find an effective permeability due to your surrounding neighbors. $latex \partial_B M = \chi$

The fluctuating force due to your neighbors is like B, a constant forcing term.

The damping is like the permeability. One may want to consider a system that starts with an intrinsic damping, that is one difference between the magnetic case and the fluctuation case, in that free space has a natural permeability but not a natural damping (I suppose there is always some damping, due to radiation and what not, but we have a tendency to totally neglect such things). One could imagine ball bearings being shaken in a cup of molasses or something. You might want to fluctuation due to being hit by other ball bearings, but consider the damping from the molasses to be the dominating damping term (the the thermal fluctuations from the molasses to be ignorable).

Another difference is that I think you really are going to need to work explicitly with time. Just the thermal average isn't going to cut it I think (at least not conceptually. There might be some dirty tricks you can play, but a typical Hamiltonian can't have damping terms. As I write this I am doubting it's truth).

$latex \ddot{x} = -\nu \dot{x}+ f$

calculate some averages ... Then use the self-consistency

$latex B = \alpha M \rightarrow f = f(\hat{x}) $

The dissipation will be related to your correlation with your neighbors. When you are moving faster, they have to tend to move in such a way to make you slow down on average.

To Be Continued
