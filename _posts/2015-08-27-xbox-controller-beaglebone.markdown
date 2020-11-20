---
author: philzook58
comments: true
date: 2015-08-27 04:18:24+00:00
layout: post
link: https://www.philipzucker.com/xbox-controller-beaglebone/
slug: xbox-controller-beaglebone
title: Xbox Controller BeagleBone
wordpress_id: 107
---

So I got my new beaglebone black in the mail today and decided to take it for a spin.

Go to getting started, install the drivers. Make sure you can write a blinking lights program.

Plug in the beaglebone to an ethernet port somewhere

Pull up your terminal

ssh 192.168.7.2

sudo apt-get install xboxdrv

in your cloud9 IDE terminal run this command

npm install node-xbox-drv

Very similar to arduino

Can just use a node library to attach to the controller

https://github.com/Jabbath/node-xboxdrv

Make a new file and put this in it
`
var xbox = require('node-xboxdrv');
var controller = new xbox("045e","028e",{});
var b = require('bonescript');`

b.pinMode("USR0", b.OUTPUT);
b.pinMode("USR1", b.OUTPUT);
b.pinMode("USR2", b.OUTPUT);
b.pinMode("USR3", b.OUTPUT);

controller.on('a',toggle);

var state = b.LOW;
controller.on('leftY',function(data){console.log(data);})
controller.on('leftY',function(data){console.log(data);})

function toggle() {
if(state == b.LOW) state = b.HIGH;
else state = b.LOW;
b.digitalWrite("USR3", state);
}
