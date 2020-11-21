---
author: philzook58
comments: true
date: 2016-11-28 19:38:05+00:00
layout: post
link: https://www.philipzucker.com/classical-landauer-buttiker/
slug: classical-landauer-buttiker
title: Classical Landauer-Buttiker
wordpress_id: 580
---

A simplistic picture of the Landauer-Buttiker picture says that the states in a 1-d ish system are quantized. Either your reservoir is filling that pipe or it doesn't depending on hour energy levels line up. That's how you get quantized conductance. (alternatively, to current is proportional to the velocity of electrons times the density of electrons, which is inversely proportional to velocity in 1-d. the two factors cancel out.)

Band structures and 1-d systems and Chern insulators all occur in classical wave systems, however an important piece of the story in the quantum case is the Pauli-exclusion principle. You just plain don't have that classically. Also the wavefunction is normalized since it has a probability interpretation. You don't have that classically either.

But, here's a thought: Instead of looking at energy or momentum flow (which is more or less the immediate analog of electrical current flow), instead consider information flow in the sense of the Shannon-Hartley theorem.

I must profess, that while I love and I think others love talking about information theory, I think applying it in physics mainly produces bullshit.

The Shannon Hartley theorem gives a way to estimate the maximum bit/s you can transmit through a channel.

The Shannon-Hartley makes sense. There are common physical limitations to channels.



 	
  1.  You have finite power or ability to make signal amplitude. Any system you make has a finite voltage it can go up to.

 	
  2.  You can't detect  detect arbitrarily weak signals. There will be thermal noise or even quantum noise stopping you at some point. You can't control everything.

 	
  3. You only have a certain bandwidth of sensitivity and production. Designs do not work arbitrarily fast.


Well, by the related Shannon sampling theorem a band limited signal is the same as a sampled signal, sampled at roughly the same frequency as the bandwidth. In a sense, a band limited signal can't change all that fast. You could come up with a similar bound by limiting the time derivative to stay below some value.

Then each sample only holds a finite number of bits. The noise level N chunks up the finite signal range S into a number of chunks S/N. This is ~ ln(S/N) bits.

Hence you have roughly BW * ln(S/N) bits per second being sent.

A slow wave has high spatial information density. But it also travels slow. In 1-d these cancel each other out just like in the quantum case.

You can only send information through the channels that can actually propagate, i.e. in the band.

The S/N quantization plays a role somewhat like the Pauli exclusion principle. Every channel can only be filled up with S/N bits like every channel can only be filled with 1 electron. I don't think the antisymmetry aspect of fermions is very relevant in this case.

The analog of current would be the difference in information rates between left to right and right to left. Worrying about a pretty silly extreme, Landauer's principle, this information has to be dissipated out somewhere or stored. Information has to be preserved at this extreme, like electrical charge

The conductance would be the derivative of information flow to bandwidth $ \dot S=G\Delta \omega$? And G=ln(1+S/N)?

Perhaps also, if you had thermal reservoirs at the two ends and you were communicating by raising and lowering the temperatures slightly? That would be somewhat analogous to the chemical potential reservoirs.

This isn't a perfect analogy, but it's not bad. I can't imagine why such considerations would be relevant to anyone.

Hmm. Perhaps this is an instance of quantized entropy flow conductance? . Now I'm really talking bullcrap. There is a universal quantum of heat conductance. Maybe this is an approach to that?

https://en.wikipedia.org/wiki/Thermal_conductance_quantum

http://www.nature.com/nature/journal/v404/n6781/full/404974a0.html




