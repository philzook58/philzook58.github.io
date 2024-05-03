---
author: philzook58
comments: true
date: 2015-12-04 06:30:39+00:00
layout: post
link: https://www.philipzucker.com/?p=270
published: false
slug: Si5351 Clock generator
title: Si5351 Clock generator
wordpress_id: 270
---

[https://learn.adafruit.com/adafruit-si5351-clock-generator-breakout/wiring-and-test](https://learn.adafruit.com/adafruit-si5351-clock-generator-breakout/wiring-and-test)

[https://github.com/adafruit/Adafruit_Si5351_Library](https://github.com/adafruit/Adafruit_Si5351_Library)

Added this to arduino library. You know the drill. Go into toolbar and click import library. Sometimes, I have the clean up the filename before it works.

In fact this time I had to unzip it to get it to work, then pick the folder from the left pane. That is immensely counterintuitive.

The library is using Wire.h to communicate over i2c.

https://www.arduino.cc/en/Reference/Wire

For me this means A5 is SCL and A4 is SDA.

It also mentions this in their little tutorial.

Failed to compile. Needed to also install Adafruit sensor library

https://github.com/adafruit/Adafruit_Sensor

Import the library using the toolbar at the top.

NEAT IT WORKS.

[![IMG_0144](http://philzucker.nfshost.com/wordpress/wp-content/uploads/2015/11/IMG_0144-300x225.jpg)](http://philzucker.nfshost.com/wordpress/wp-content/uploads/2015/11/IMG_0144.jpg)



Why is this picture upside down? How mysterious.

[![IMG_0145](http://philzucker.nfshost.com/wordpress/wp-content/uploads/2015/11/IMG_0145-300x225.jpg)](http://philzucker.nfshost.com/wordpress/wp-content/uploads/2015/11/IMG_0145.jpg)



And I can see the 113Mhz signal on the oscilloscope. That is surprising since it's a 100Mhz scope. I never read the manual on the thing and I've never had an easy 100Mhz signal hooked up to it before.

Maximum time per division is 2 ns which is a  frequency of 500Mhz, so maybe I shouldn't be that surprised.

[https://blog.adafruit.com/2012/01/27/why-oscilloscope-bandwidth-matters/](https://blog.adafruit.com/2012/01/27/why-oscilloscope-bandwidth-matters/)

I guess the rated frequency is actually a -3dB roll off.

This is very odd to me. 200Mega samples per second. I really thought I was going to run up against

The signal is rounded off into a pretty nice sinusoid. I'd bet that is due to my external probes filtering.

I'm also receiving the signal on my nearby cable. Ordinarily annoying, but Neat. Capital NEAT.

I can tune to the frequency on my FM radio. You can tell because the static goes away.

I can also see the frequency on my RTL-SDR

I can switch back and forth between frequencies and hear a tone. Unfortunately the app





Simple serial control

    
    #include <Adafruit_Sensor.h>
    
    #include <Wire.h>
    #include <Adafruit_SI5351.h>
    
    Adafruit_SI5351 clockgen = Adafruit_SI5351();
    
    String inString = "";    // string to hold input
    /**************************************************************************/
    /*
        Arduino setup function (automatically called at startup)
    */
    /**************************************************************************/
    void setup(void) 
    {
      Serial.begin(9600);
    
      /* Initialise the sensor */
      if (clockgen.begin() != ERROR_NONE)
      {
        /* There was a problem detecting the IC ... check your connections */
        Serial.print("Ooops, no Si5351 detected ... Check your wiring or I2C ADDR!");
        while(1);
      }
    
    
      clockgen.setupPLL(SI5351_PLL_A, 24, 2, 3);
      clockgen.setupMultisynthInt(0, SI5351_PLL_A, SI5351_MULTISYNTH_DIV_8);
      
      /* Enable the clocks */
      clockgen.enableOutputs(true);
    }
    
    /**************************************************************************/
    /*
        Arduino loop function, called once 'setup' is complete (your own code
        should go here)
    */
    /**************************************************************************/
    
    void setClock(float freq){
      /* 
      Serial.print("Frequency: ");
          Serial.print(String(freq));
           Serial.print("Mhz");
       */
       
       float normfreq = freq/25*8;
       uint32_t intpart = floor(normfreq);
       Serial.print("Integer part: ");
          Serial.print(String(intpart));
       uint32_t fracpart = floor((normfreq - (long)normfreq )* 1048575) ; 
         Serial.print("\tFrac part:");
          Serial.println(String(fracpart));
       clockgen.setupPLL(SI5351_PLL_A, intpart, fracpart, 1048575);
       
       
      
    }
    
    
    void loop(void) 
    {  
      // Read serial input:
      while (Serial.available() > 0) {
     
        setClock(Serial.parseFloat());
      }
    
      
      
    }


Set to no newline character.

Set a really simple scheme. There is probably a better one. Used maximum denominator 1048575, and then just took the integer part

Left the divider on the integer divide by 8 setting

uint32_t was clutch.

Seems to stop responding somewhere below ~47Mhz. Oh. I know why. The integer part can't go lower than 15.


