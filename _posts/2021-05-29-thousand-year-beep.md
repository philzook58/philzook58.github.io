---
date: 2022-08-07
layout: post
title: "Fifty Year Beep"
description: Making an object that beeps once in 50 years
tags: projects laser cutter arduino
---



There is a fun idea of making a nice little object that will beep sometime in the future. Probably not a thousand years. Instad more like 50. Isn't it fun thinking about having this thing and bringig your friends and family who aren't dead to watch it on the prescribed time.

![](/assets/beep50/IMG-0121.jpg)

The humor of it is somehow that the beep is so short and anticlimactic. Not a long beep. More like a blip.

[Ben's blog notes](http://blog.benwiener.com/electronics/projects/programming/2021/10/15/beep.html) has a lot more technical detail

This is somewhat inspired my the [clock of the long now](https://en.wikipedia.org/wiki/Clock_of_the_Long_Now)

I waited a too long (6 months) and now my recollection of the technical details is a little fuzzy. Don't do that. Blog fresh.

It turns out that a hobbiest getting an electronic clock to nominally run for 50 years is actually on the edge of challenging. This is ignoring unforeseeable chemical issues like whiskering of solder or other weird stuff. 

Batteries come specced in amp-hours. So you need to get the standby current down of any device you are using. What ended up being key for us is getting some crazy nonrechargeable lithium chloride batteries. They have massive capacity and good discharge curves.

What we ended up on the controller side was using a combo architecture. The typical DS3231 RTC chip you find on amazon actually works amperage wise if you take off the LED. What it doesn't do is track the days correctly. I'm a little fuzzy now, but I'm not even sure it works beyond a month.

So what we also have if a QTpy, which is a SAMD based arduino which is small and pretty cheap. Ben mangled the LEDs off it with a soldering iron. You have to have no LEDs for low power. They are quite a large power draw compared to logic. We also do not go through a regulator, which can also suck power. Our battery is close enough to the working voltage of both chips to be okay (and again the disacharge curve of voltage vs amphours is pretty flat).

We also had a nice little board custom made to attach everything. The circuit all told is dead simple.

We tested it a couple times over week lengths and it worked ok.

There was an amusing event where we were about to seal them up, but then we checked the amperage one last time for a goof and it was way up after the first wake up.

There was an interesting bug that occurred at one point. We have this communication system of the RTC chip waking up the SAMD chip to reset the alarm. The various times at play are a little confusing to think about (communication time, computation time, wait time). It turned out that the right choice of them made a bug so that the thing would never beep. Will exclaimed at this point that "what is the point of your formal method bullshit if it can't do this!". He is both right and wrong. We are barely trying to understand what we are doing and wildly thrashing with random flags to turn down the amperage. We have basically no model of the times in question. C++ is a tough proposition. On the other hand, these are the questions that show up in real systems. Yeah, I dunno. Formal methods _is_ kind of bullshit. But everything is. Just do what you find interesting and get make an acceptable living off of. That's the only answer I got. I wish I remembered the exact bug to revisit it. You almost certainly could catch it with a model of some kind.

We made a dodecahedron contained for it. A nice technique is to use standard "dino bones" laser cutter construction, but then cover the pegs with cosmetic plates.

All told amperage wise we have a power of 10 wiggle room according to our calculation for the 1-year beep. We'll see in November.

### More Notes
To get started we're investigating using a stock RTC module

We had a couple nights confusion that ended up being due to a bad wire.

The zs-042 boards are built around ds3231 chips. The spec sheet states quite an imprssive accruacy of ~2 minutes a year. We desoldered the power led on the module to lower the amperage significantly from 1mA down to about 100uA.

We got some beefy boy batteries.

RTCLib
https://adafruit.github.io/RTClib/html/index.html

LowPower library. https://www.arduino.cc/en/Reference/ArduinoLowPower RThe external wakeup example is close to what we need.

Standby mode is aroudn 100uA.

We got a qt py which is a small and cheap board based aorund the samd21. The samd 21 has an internal real time clock system. In principle it is a one stop shop. However the internal oscillator is not very sccurate st all. We had about ~30minutes accuracy over a day. Not great. The external oscillator pins are not broken out on the qt py

We considered making a new baprd fresh or editting the 

by desoldering the led on the qt py we could lower the power by quite a bit. I believe setting the pins to INPUT_PULLUP also decreased the amerage by a nontirival amount

The qt py has a built in rtc.


```C++
#include "ArduinoLowPower.h"
#include <RTClib.h>

RTC_DS3231 rtc;

// Pin used to trigger a wakeup
const int INTERRUPT_PIN = 1;
const int BEEPER_PIN = 0;

bool ready_to_beep;
DateTime alarm;
TimeSpan WAKEUP_PERIOD =  TimeSpan(1, 0, 0, 0);
TimeSpan BUFFER_PERIOD =  TimeSpan(0, 0, 0, 10);


void setup() {
  // enable internal pullup on all
  pinMode(INTERRUPT_PIN, INPUT_PULLUP);
  pinMode(2, INPUT_PULLUP);
  pinMode(3, INPUT_PULLUP);
  pinMode(4, INPUT_PULLUP);
  pinMode(5, INPUT_PULLUP);
  pinMode(7, INPUT_PULLUP);
  pinMode(9, INPUT_PULLUP);
  pinMode(10, INPUT_PULLUP);
  pinMode(11, INPUT_PULLUP);
  pinMode(12, INPUT_PULLUP);
  pinMode(13, INPUT_PULLUP);
  pinMode(14, INPUT_PULLUP);

  pinMode(BEEPER_PIN, OUTPUT);
  
  double_beep();
  
  rtc.begin();

  rtc.adjust(DateTime(F(__DATE__), F(__TIME__)));
  alarm = rtc.now() + TimeSpan(6, 20, 0, 0);
  ready_to_beep = false;


  // we don't need the 32K Pin, so disable it
  rtc.disable32K();

  // stop oscillating signals at SQW Pin
  // otherwise setAlarm1 will fail
  rtc.writeSqwPinMode(DS3231_OFF);

  // turn off alarm 2 (in case it isn't off already)
  // again, this isn't done at reboot, so a previously set alarm could easily go overlooked
  rtc.clearAlarm(2);
  rtc.disableAlarm(2);

  set_alarm();
  
  // Attach a wakeup interrupt on pin 8, calling repetitionsIncrease when the device is woken up
  LowPower.attachInterruptWakeup(INTERRUPT_PIN, interrupt_handler, FALLING);
}

void interrupt_handler() {
  if (ready_to_beep) {
    beep();
    rtc.clearAlarm(1);
  } else {
    double_beep();
    set_alarm();
  }
}

void set_alarm() {
  // set alarm 1, 2 flag to false (so alarm 1, 2 didn't happen so far)
  // if not done, this easily leads to problems, as both register aren't reset on reboot/recompile
  rtc.clearAlarm(1);

  if (rtc.now() + WAKEUP_PERIOD + BUFFER_PERIOD > alarm) {
    ready_to_beep = true;
    rtc.setAlarm1(alarm, DS3231_A1_Date);
  } else {
    rtc.setAlarm1(rtc.now() + WAKEUP_PERIOD, DS3231_A1_Date);
  }
}

void loop() {
  LowPower.sleep();
}

void beep()
{
    digitalWrite(BEEPER_PIN, HIGH);
    delayMicroseconds(1000000);
    digitalWrite(BEEPER_PIN, LOW);
}

void short_beep()
{
    digitalWrite(BEEPER_PIN, HIGH);
    delayMicroseconds(100000);
    digitalWrite(BEEPER_PIN, LOW);
}

void double_beep() {
    short_beep();
    delayMicroseconds(100000);
    short_beep();
}
```