---
author: philzook58
comments: true
date: 2019-10-13 21:00:36+00:00
layout: post
link: https://www.philipzucker.com/?p=2401
published: false
slug: Casadi Pendulum Model Predictive Control
title: Casadi Pendulum Model Predictive Control
wordpress_id: 2401
---




We built a physical pendulum that is controlled by a raspberry pi for another project to be announced soon. You can find the plans here.







I thought it would be a fun example to run a model predictive controller built with casadi with.







The opti interface is pretty nice. I like it. Casadi is pretty solid. I kind of feel like there is little reason to use the other interfaces. If you really wanted codegen? Maybe you'd be better off with sympy then anyhow. It does codegen. Me dunno.







Casadi support warm start and repeated solve. Pretty clutch.







For human purposes, IpOpt is pretty fast, but real-time seems like pushing it. In initial tests, I was a little disconcerted with how unreliable the solve times were. I don't think 0.3 seconds will cut it.







I have a suspicion that the bang bang nature was not kind.







I usually just use a very simple leap-frog/euler integrator, figuring that it isn't worth my time or the cost in simplicity to implement something better, but a better integrator can use fewer time steps, which may be really worth it in this case. At a coarse conceptual level, a better integrator doesn't seem to add much.







[https://epubs.siam.org/doi/pdf/10.1137/16M1062569](https://epubs.siam.org/doi/pdf/10.1137/16M1062569)



