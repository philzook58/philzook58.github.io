---
author: philzook58
comments: true
date: 2015-08-02 23:37:09+00:00
layout: post
link: https://www.philipzucker.com/routers-and-switches/
slug: routers-and-switches
title: Routers and Switches
wordpress_id: 92
---

So I've been a touch confused as to what the difference is between routers and switches. To an outsider they both look like boxes you plug ethernet cables into.

So there's a couple things. First off, ethernet is a standard for communication. Communicating over wireless (the "ether") requires careful planning to avoid screaming over the same frequencies at the same time, just like the roads need traffic rules to avoid collisions. Ethernet was designed for a bunch of computers attaching to the same hunk of copper (a coax cable) that they would all scream over so it needs a similar set of rules.

The switch I guess is operating on the ethernet protocol, and is IP agnostic. The switch itself does not necessarily need a MAC address

The router needs to be aware of ethernet protocols to work, but it also needs to be aware of IP. It needs it's own IP and MAC address.


