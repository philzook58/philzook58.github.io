---
author: philzook58
comments: true
date: 2015-09-27 19:12:13+00:00
layout: post
link: https://www.philipzucker.com/playin-around-with-esp8266/
slug: playin-around-with-esp8266
title: Playin around with ESP8266
wordpress_id: 173
---

So I tried tying my esp8266 to the 2$ nano i just received in the mail. Was getting nothing for a while. Needed an external power supply to work. Too bad.

[http://rancidbacon.com/files/kiwicon8/ESP8266_WiFi_Module_Quick_Start_Guide_v_1.0.4.pdf](http://rancidbacon.com/files/kiwicon8/ESP8266_WiFi_Module_Quick_Start_Guide_v_1.0.4.pdf)

useful link

Set serial monitor to both NL & CR line returns and 9600 baud to get it to respond to AT with OK.

firmware version

AT+GMR
0018000902-AI03

AT+CWMODE=3

sets it into some mode? Necessary for the next step to work

CW stands for?

List Access Points

AT+CWLAP lists local access points

Join access point

AT+CWJAP="local access point"," password"

I've noticed that the esp is available from my computer

AT+CIFSR tells me the IP addresses

I belive one is its ip as a client and one as an access point.

I do not have a great success rate with commands. The serial is getting garbled

Gonna try loading up that custom firmware

https://github.com/tommie/esptool

Looks like there is a python script to load the firmware

https://github.com/nodemcu/nodemcu-firmware.

Or Maybe I'm done for today.




