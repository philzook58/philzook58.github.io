---
author: philzook58
comments: true
date: 2015-10-27 05:21:57+00:00
layout: post
link: https://www.philipzucker.com/avr-gcc-and-arduino/
slug: avr-gcc-and-arduino
title: Avr-gcc and Arduino
wordpress_id: 211
---

I'm using an arduino nano.

Way easier than wiring up my own bullcrap, even though I've got some raw chips and a programmer on hand.

Here's a short makefile that will get stuff to happen. You'll need to replace /dev/tty0USB0 with wherever you're device actually is.

    
    TARGET=led
    
    all: $(TARGET).c
    	avr-gcc -Os -DF_CPU=16000000UL -mmcu=atmega328p -c -o $(TARGET).o $(TARGET).c
    	avr-gcc -mmcu=atmega328p $(TARGET).o -o $(TARGET)
    	avr-objcopy -O ihex -R .eeprom $(TARGET) $(TARGET).hex
    
    flash: $(TARGET).hex
    	avrdude -F -V -c arduino -p ATMEGA328P -P /dev/ttyUSB0 -b 57600  -U flash:w:$(TARGET).hex




[This](https://balau82.wordpress.com/2011/03/29/programming-arduino-uno-in-pure-c/) was useful in figuring out how to make this makefile.

    
    #include <avr/io.h>
    
    int main(void)
    {
        // connect led to pin PC0
        DDRB |= (1 << 0);
        while(1)
        {
            PORTB ^= (0xFF << 0);    // toggles the led
        }
    }


This makes a fast switching program just to see what we can pump out. I measure 1.6Mhz

    
    avr-objdump -m avr -D fastswitch.hex > assembly


Also

Adafruit Shield version 1 works on my chinese DK electornics board. Nice.


