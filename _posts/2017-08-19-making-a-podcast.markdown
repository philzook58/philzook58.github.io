---
author: philzook58
comments: true
date: 2017-08-19 13:51:53+00:00
layout: post
link: https://www.philipzucker.com/making-a-podcast/
slug: making-a-podcast
title: Making a Podcast
wordpress_id: 805
---

I followed a couple tutorial websites

I'm using Zencastr for the moment. It is a browser based skype recording thing. Our first episode came out really out of sync between the two tracks

I'm using audacity to mix the two tracks together into a single file.

Hosting is on a blogspot. I think this was a bad choice. Should have used wordpress. Anyway, simple enough. Make a post per episode.

Using Feedburner to collect up the RSS feed from the blogspot and giving it more metadata. This service feels so crusty and ancient. I wonder if it still best practice

Domain names on Google Domains.

Google Drive with shared links was used for hosting. This works ok, but is not good enough for itunes. It is missing byte range requests and maybe nice urls with filenames in them? Google drive has some abilities that stopped in 2015 that would've been helpful. If you modify the usual shared link to look like

https://drive.google.com/uc?export=download&id=0ByV2UyFOHalnSHdkbTZnLVJUc2M

it works better, replacing that junk at the end with your junk

Using Amazon S3 for storage. I already had an AWS account and bucket, so no biggy. The cost should be cheap according to what I'm seeing? $0.04 /GB/month for storage and a couple of cents per 1000 requests supposedly. We'll see. I've been burned and confused by AWS pricing before.

Submit podcast on https://podcastsconnect.apple.com/#/ for itunes




