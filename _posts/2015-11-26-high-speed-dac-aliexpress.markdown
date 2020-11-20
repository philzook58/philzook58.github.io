---
author: philzook58
comments: true
date: 2015-11-26 03:08:04+00:00
layout: post
link: https://www.philipzucker.com/high-speed-dac-aliexpress/
slug: high-speed-dac-aliexpress
title: High Speed DAC Aliexpress
wordpress_id: 264
---

[http://www.aliexpress.com/item/High-Speed-AD-DA-Module-Matching-FPGA-Black-Gold-Development-Board/2053961415.html](http://www.aliexpress.com/item/High-Speed-AD-DA-Module-Matching-FPGA-Black-Gold-Development-Board/2053961415.html)

I bought this bad boy. Seems cool. Thought maybe I could brute force my way into AM radio land with it.

Also a good project for fpga. Microcontrollers are going to be too slow.

A noticeable problem is the missing of the pinout

[http://www.wayengineer.com/blackgold-high-speed-adda-module-for-fpga-development-board-p-2753.html#.VlYh2d-rQfE](http://www.wayengineer.com/blackgold-high-speed-adda-module-for-fpga-development-board-p-2753.html#.VlYh2d-rQfE)

[![AD:DA pinout](http://philzucker.nfshost.com/wordpress/wp-content/uploads/2015/11/ADDA-pinout-241x300.jpg)](http://philzucker.nfshost.com/wordpress/wp-content/uploads/2015/11/ADDA-pinout.jpg)

This appears to be the same product and I can at least confirm that this pinout does work for the DA side of things.

I wrote a quick test program to service it with a ramp function with an arduino. Good idea to sanity check before diving into the deeper waters of fpga.

[![IMG_0142](http://philzucker.nfshost.com/wordpress/wp-content/uploads/2015/11/IMG_0142-300x225.jpg)](http://philzucker.nfshost.com/wordpress/wp-content/uploads/2015/11/IMG_0142.jpg)

[![IMG_0143 2](http://philzucker.nfshost.com/wordpress/wp-content/uploads/2015/11/IMG_0143-2-300x225.jpg)](http://philzucker.nfshost.com/wordpress/wp-content/uploads/2015/11/IMG_0143-2.jpg)Ripping through the arduino code with no delay makes a ramp at 53.2Hz. Pathetic, but working.

    
    #define CLKPIN 2 
    //Lowest bit pin on 6, highest bit on 13
    
    void setup(){
      pinMode(CLKPIN, OUTPUT);
      digitalWrite(CLKPIN, HIGH);
      
      for(int i = 0; i< 8; i++){
        pinMode(13-i, OUTPUT);
      }
    }
    byte count = 0;
    
    void loop(){
      count++; 
      digitalWrite(CLKPIN, LOW);
      for(int i = 0; i < 8; i++){
        digitalWrite(6+i, count & (1 << i));
      }
      digitalWrite(CLKPIN, HIGH);
    }









