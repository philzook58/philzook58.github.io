---
author: philzook58
comments: true
date: 2015-07-28 19:01:30+00:00
layout: post
link: https://www.philipzucker.com/the-particle-photon-a-cloud-enabled-arduino/
slug: the-particle-photon-a-cloud-enabled-arduino
title: 'The Particle Photon: A Cloud Enabled Arduino'
wordpress_id: 81
---

Bought one last month and it came in the mail.

Some Notes

Set it up with the particle app on your phone

curl https://api.particle.io/v1/devices/210040000340000009370006/ledToggle -d access_token=ef7c43146253453545ea635435e316445775474 -d "command=on"

The -d in curl commands allow you to send multiple post data.



I recommend not using curl and downloading the command line interface

npm install -g particle-cli

particle login

particle call my_device_name led on

Got to annoy people with beeps over the internet. Pretty good.
