---
author: philzook58
comments: true
date: 2016-05-23 14:37:26+00:00
layout: post
link: https://www.philipzucker.com/getting-goddamn-wifi-on-the-goddamn-orange-pi-pc/
slug: getting-goddamn-wifi-on-the-goddamn-orange-pi-pc
title: Getting goddamn wifi on the goddamn orange pi pc
wordpress_id: 446
---

I tried the Lubuntu and Raspbian distros, maybe another one would work out of the box. i've heard rumblings that an openelec distro might work with wifi? Also I've heard that 8188eu chipsets will work out of the box. Can't confirm either.

http://www.armbian.com/orange-pi-pc/

used the legacy jessie server 3.4.112 build here.  unpacked it using keka.

installed on sd card using dd. https://www.raspberrypi.org/documentation/installation/installing-images/mac.md

Made the wifi drivers as described here

http://forum.armbian.com/index.php/topic/749-orange-pi-pc-wireless-module-8192cu/

make scripts failed

After making the scripts I mostly followed the github itself instructions.

https://github.com/pvaret/rtl8192cu-fixes

I had to edit the kernel files to comment stuff out like discussed here

http://forum.armbian.com/index.php/topic/1121-unable-to-build-kernel-scripts/

Seemed to work.

(Putting the wifi dongle in the lower usb port might be important? I've heard reports of that)

iwlist scan wlan0

finds the local router

My Edimax RTL8188CUS adapter does appear to be close to working now. I am connected to the router

made a /etc/wpa_supplicant/wpa_supplicant file

with

    
    network={
            ssid="myssid"
            psk="my_very_secret_passphrase"
    }


changed the /etc/network/interfaces file to have

    
    auto wlan0
    iface wlan0 inet dhcp
        wpa-conf /etc/wpa_supplicant/wpa_supplicant.conf


Can't ping external ips. TBD if everything is actually fixed.

Edit:

    
    route add default gw 192.168.0.1 wlan0




http://www.cyberciti.biz/faq/linux-setup-default-gateway-with-route-command/

Gateway was misconfigured

Also added

    
    allow-hotplug wlan0


To the /etc/network/interfaces. I think until I did this it didn't find the wifi until you logged on with ethernet




