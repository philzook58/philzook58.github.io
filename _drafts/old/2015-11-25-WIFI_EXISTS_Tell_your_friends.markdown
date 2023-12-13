---
author: philzook58
comments: true
date: 2015-11-25 17:40:02+00:00
layout: post
link: https://www.philipzucker.com/?p=263
published: false
slug: WIFI EXISTS. Tell your friends
title: WIFI EXISTS. Tell your friends
wordpress_id: 263
---



This command makes an alias to the built in wifi information doohickey on a mac

    
    sudo ln -s /System/Library/PrivateFrameworks/Apple80211.framework/Versions/Current/Resources/airport /usr/sbin/airport



    
    airport -s


on ubuntu, you can do something quite similar with

Direct access using Appkit

http://stackoverflow.com/questions/30839084/is-there-an-api-or-software-to-get-accurate-strength-of-a-wifi-signals-on-mac
