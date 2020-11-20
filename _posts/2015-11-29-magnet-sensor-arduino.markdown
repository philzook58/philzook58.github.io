---
author: philzook58
comments: true
date: 2015-11-29 03:18:14+00:00
layout: post
link: https://www.philipzucker.com/magnet-sensor-arduino/
slug: magnet-sensor-arduino
title: Magnet Sensor arduino
wordpress_id: 276
---

#  I got da




# A1302KUA-T




# It good?


It 1.0-1.6 mV/G sensitivity

oh I pooed

Front is cornered side.

PINOUT BABY

1 is power

2 is ground

3 is signal

![](http://philzucker.nfshost.com/wordpress/wp-content/uploads/2015/11/Sat-Nov-28-2015-220532-GMT-0500-EST.png)

left to right.

1 T = 10000G

Positive magnetic field pointing into the front face of the device.

Negative magnetic field is pointing out from front face of device



    
    const int analogInPin = A5;  // Analog input pin that the potentiometer is attached to
    
    int sensorValue = 0;        // value read from the pot
    int outputValue = 0;        // value output to the PWM (analog out)
    
    void setup() {
      // initialize serial communications at 9600 bps:
      Serial.begin(9600); 
    }
    
    void loop() {
      // read the analog in value:
      sensorValue = analogRead(analogInPin);            
      // map it to the range of the analog out:
      // 1.3mV/G * 2500mV full range = 3250
      outputValue = map(sensorValue, 0, 1023, -3250, 3250);  
      
      // print the results to the serial monitor:
      Serial.print("sensor = " );                       
      Serial.print(sensorValue);      
      Serial.print("\t B Field = ");      
      Serial.println(outputValue);   
    
      // wait 2 milliseconds before the next loop
      // for the analog-to-digital converter to settle
      // after the last reading:
      delay(2);                     
    }




Why have I written this like I'm a fucking idiot? FOR SOME SPICE. I'M A FREE SPIRIT.



A single little button cell looking magnet maxes out at 2950G when placed right up against the thing.

I would guess that this is about right though.

This value probably cannot be trusted. The snesor states that it goes nonlinear towards saturation

Maybe 1cm away the value is already reduced to 200-300G.

A stack has 700-800G at same position.

A stack caps out the meter with still .3cm left.

The field ramps up very quickly.

I couldn't venture really how strong the field is at the surface of the stack, but it's more.

I need to build some kind of apparatus. Maybe I can see what kind of power law we're talking.




# 
