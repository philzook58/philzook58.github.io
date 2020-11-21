---
author: philzook58
comments: true
date: 2017-08-27 16:47:02+00:00
layout: post
link: https://www.philipzucker.com/simple-gnuradio-sonar-rangefinding/
slug: simple-gnuradio-sonar-rangefinding
title: Simple GnuRadio Sonar Rangefinding
wordpress_id: 831
---



![random_source-grc](/assets/random_source.grc_.png)

A simple graph where you can see a peak move as you move the microphone closer and farther from the speaker.

Uses the FFT method to compute the cross-correlation between the source signal and the microphone signal.

The source signal is a random binary signal. The repetition of 2 helpful I think because of the window applied in the Fourier Transform elements. Since a binary signal at the sampling rate has a lot of high frequency components, I hypothesize that Even a very sharp low pass filter might hurt. Repetition ought to push the signal somewhere in the middle of the spectrum.

Suggestion:

Could use averaging to increase signal level.



The plan is to master the sonic case, where the electronics is much simpler, and then move into using my LimeSDR attached to IR diodes for a DIY Lidar unit. We'll see where we get.



An interesting package that i should have investigated first

https://github.com/kit-cel/gr-radar


