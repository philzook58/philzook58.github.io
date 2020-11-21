---
author: philzook58
comments: true
date: 2016-01-01 00:21:38+00:00
layout: post
link: https://www.philipzucker.com/?p=362
published: false
slug: Return Loss Bridge
title: Return Loss Bridge
wordpress_id: 362
---

[http://www.qsl.net/kl7jef/Build%20a%20Return%20Loss%20Bridge.pdf](http://www.qsl.net/kl7jef/Build%20a%20Return%20Loss%20Bridge.pdf)

Used this toroid which I had from [this kit](http://www.kitsandparts.com/WA2EBY_toroidkit.php)

[http://toroids.info/FT50-43.php](http://toroids.info/FT50-43.php)

10 Turns of bifilar winding 24 gauge wire.

We used 47 ohm because we don't have 50ohm

Surface mount over a copper clad breadboard groundplane.

3 sma connectors

![](http://philzucker.nfshost.com/wordpress/wp-content/uploads/2016/01/Thu-Dec-31-2015-191301-GMT-0500-EST.png)

I think the basic idea is that 50 ohms is attached at L to ground, then the bridge is balanced and only the common mode goes across the inductor. But the common mode across the transformer is a huge inductance/ imedance so it blocks it from getting to the detector at D. When the bridge isn't balanced there is a different voltage across each of the coils, which can get through.
