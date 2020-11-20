---
author: philzook58
comments: true
date: 2015-12-23 03:41:30+00:00
layout: post
link: https://www.philipzucker.com/ubuntu-virtualbox/
slug: ubuntu-virtualbox
title: Ubuntu Virtualbox
wordpress_id: 344
---

Download an ubuntu install distro

Download Virtualbox

Make a new virtual machine. Linux 64-bit probably

Under storage go the the cd and click on it. Select the installation disk.

Decide to erase and install, it's fine.

Insert the guest additions cd using the menu bar under devices. Install them. Now it should go full screen when you click the little green button on macs. You can slide all your fingers to switch workspaces.

TO be able to access shared folders

    
    sudo adduser USERNAME vboxsf
    


Also, checking 3d acceleration under Settings > Display and giving it all the video ram you can seems to make it run much zippier.

I also gave it 3gb of ram because i had a little extra to spare. Seems to like it.

    
    sudo apt-get install lxde


Can use a more lightweight desktop environment by selecting that little emblem at the login screen.
