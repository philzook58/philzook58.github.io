---
author: philzook58
comments: true
date: 2016-03-23 02:53:01+00:00
layout: post
link: https://www.philipzucker.com/?p=421
published: false
slug: Amazon Problems man
title: Amazon Problems man
wordpress_id: 421
---

So when I shutdown my instances all my work was deleted. Unexpected.

It turns out spot instances do not have stopped states.

SO.

If you click don't delete on terminate you can at least keep the ebs around as root.

Then you can convert that

make sure the pick Hardware virtualization so that you can still use the g2 instance

Then boot up new instances from that base ami, with an ebs for work.

Here's how tp check and change delete on terminate

http://www.petewilcock.com/how-to-modify-deletion-on-termination-flag-for-ebs-volume-on-running-ec2-instance/
