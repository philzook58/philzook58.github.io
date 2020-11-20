---
author: philzook58
comments: true
date: 2016-08-01 03:06:19+00:00
layout: post
link: https://www.philipzucker.com/triple-booting-macbook-for-ubuntu-on-flash-drive/
slug: triple-booting-macbook-for-ubuntu-on-flash-drive
title: Triple Booting Macbook for ubuntu on flash drive
wordpress_id: 477
---

So making a live usb of ubuntu seems to restrict you to 4gb space. I don't want that. I want the full space of my 64gb usb3 flash drive available.

This is harder than it seems it might be.

This was very useful

[http://askubuntu.com/questions/525845/how-to-finally-get-ubuntu-to-boot-on-a-mac-from-external-usb-storage](http://askubuntu.com/questions/525845/how-to-finally-get-ubuntu-to-boot-on-a-mac-from-external-usb-storage)

Didn't do the gdisk stuff?

I have a running ubuntu desktop to piggyback off of.

First I made an install usb drive on a lesser 8gb usb drive using create startup disk ubuntu utility

Choose "something else" in installation menu once plugged in and booted off my mac. (hold option key on startup to pick usb drive)

Then I installed  on the bigger blank usb drive by selecting it as the root partition. Picked ext4.  Used some space for swap. also I should have made an efi partition at this step but I did it later

made efi later using gparted. create a 200mb fat32 partition. Then set flag as boot. That is an efi partition I guess

[http://unix.stackexchange.com/questions/174495/creating-efi-bootable-gpt-partition-with-gdisk-on-previous-mbr-gpt-damaged](http://unix.stackexchange.com/questions/174495/creating-efi-bootable-gpt-partition-with-gdisk-on-previous-mbr-gpt-damaged)

downloaded refind binary. ran ./refind-install --usefault=/dev/sdb3 which was the efi partition I made.

Turn on macbook holding down option key

efi is there

picked the ubuntu icon on the right that mentioned my flash drive. There is another one. Not sure what that is?

Boots into ubuntu!

Okay. so that's good

My mac now default boots into grub? This panicked me for a moment, since I thought I did nothing to my hard drive. I suppose the ubuntu installer must have done something. Maybe this is what those deleting a MBR  with gdisk instructions are about. It's fine this way it is for me. Now I need to hold option if I want to boot into Mac. This is acceptable.

In ubuntu, My tilde key is mapping to <>. That's weird

http://askubuntu.com/questions/530325/tilde-key-on-mac-air-with-ubuntu



To get the facetime camera working i had to follow these very scary instructions

https://github.com/patjak/bcwc_pcie/wiki/Get-Started

Installed sudo apt-get checkinstall to run a line

Had to

    
    modprobe -r facetimehd
    
    modprobe -r bdc_pci
    
     modprobe  facetimehd
    
    modprobe  bdc_pci




as suggested near the bottom in order to find the webcam in cheese.

The color balance appears to be messed up. Futzing around with the hue settings you can get something that almost looks right. And conversion to black and white is fine. So That's good enough for a lot of my purposes.










