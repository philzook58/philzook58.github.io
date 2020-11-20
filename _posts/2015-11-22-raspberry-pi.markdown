---
author: philzook58
comments: true
date: 2015-11-22 21:24:29+00:00
layout: post
link: https://www.philipzucker.com/raspberry-pi/
slug: raspberry-pi
title: Raspberry Pi
wordpress_id: 252
---

Scan the network for a ip that shows up




nmap -sn 192.168.0.0/24







log in with ssh. You need (hypothetically I've heard tale of other ways, but just do this. You have a monitor. So much easier) to boot once with a monitor to set the ssh server on bootup.




ssh pi@192.168.0.20




password: raspberry




setting up wifi




    
    <code>iwlist wlan0 scan</code>


http://unix.stackexchange.com/questions/92799/connecting-to-wifi-network-through-command-line

https://learn.adafruit.com/adafruits-raspberry-pi-lesson-3-network-setup/setting-up-wifi-with-occidentalis

http://stackoverflow.com/questions/8191459/how-to-update-node-js

Jesus, had to update everything.

sudo crontab -e

    
    @reboot sh /home/pi/bbt/launcher.sh >/home/pi/logs/cronlog 2>&1


[https://github.com/npm/npm/issues/8412](https://github.com/npm/npm/issues/8412)

Ran into this issue. Needed to update npm.

[https://www.raspberrypi.org/documentation/configuration/wireless/wireless-cli.md](https://www.raspberrypi.org/documentation/configuration/wireless/wireless-cli.md)

sudo nano /etc/wpa_supplicant/wpa_supplicant.conf

network={ ssid="WORK" key_mgmt=NONE wep_key0=PASSKEY }

Ran into massive pyserial problems. I don't get it. Apparently the solution wast o change from the ubuntu repository version to the pip installed versions of pyserial

Bought a cheap aliexpress display. This worked:

[http://appdictive.dk/blog/projects/2015/10/30/cheap_tft_display_on_raspberry_pi/](http://appdictive.dk/blog/projects/2015/10/30/cheap_tft_display_on_raspberry_pi/)
