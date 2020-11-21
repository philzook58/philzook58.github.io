---
author: philzook58
comments: true
date: 2015-12-16 21:26:25+00:00
layout: post
link: https://www.philipzucker.com/nmr-a-baby-birds-first-fall-from-the-nest/
slug: nmr-a-baby-birds-first-fall-from-the-nest
title: 'NMR: a baby birds first fall from the nest'
wordpress_id: 285
---

The idea is to attempt to use commodity hardware (standard hacker toolkit) to see an NMR signal

We bought 3 disk magnets from amazon. 1.5"x.25".

Using our magnetometer made from a hall effect sensor, we're getting that that field in the bore ~0.5T.

Going off a guess that disk magnets have fields approximately that of coils, a helmholtz coil arrangement was attempted with 3d printed parts. The fit of the magnets in there is really tight.

We saturated the sensor (which saturates at 0.3T), but with theoretically the thing is taking the dot product with it's orientation with respect to the field. A perpendicular sensor does read approximately 0T. So we attenuated the field by tilting the sensor 45/2 degrees off of perpendicular and measured ~0.17T.

For the hydrogen nucleus, this is a resoannce freqeuncy of ~20Mhz.

[https://en.wikipedia.org/wiki/Gyromagnetic_ratio](https://en.wikipedia.org/wiki/Gyromagnetic_ratio).

We designed a [helmholtz coil ](https://en.wikipedia.org/wiki/Helmholtz_coil)setup (coils that are 1 radius apart. They look unnaturally close to my eye for some reason, but that it just opinion.), Oversizing things that have to fit by 0.01inch seems enough for a snug fit. Your mileage may vary.

It is quite unclear to me the electrical characteristics these coils are going to have at the design frequency of ~20Mhz.

Here is a GUESS. I haven't really done much hard work on this. But it's probably right to order of magnitude. The B is fairly uniform in the helmholtz coil. Basically the same result for a solenoid of same size.

N is number of turns on one coil.

$ B = (4/5)^{3/2} \mu_0 N I / r$

$ \Phi = L I$

$ \Phi = 2 N A B$

$ L =(4/5)^{3/2} \mu_0 N^2 2 \pi r $

$ A = \pi r^2 $



Gives an inductance of 7uH, impedance of ~1kOhm at 20Mhz with 10 turns per coil.

This estimate was confirmed

[http://www.benwiener.com/index.php/2015/12/16/some-rf-learnin/](http://www.benwiener.com/index.php/2015/12/16/some-rf-learnin/)
