
Thousand Year Beep


[Ben's blog notes](http://blog.benwiener.com/electronics/projects/programming/2021/10/15/beep.html)

There is a fun idea of making a nice little object that will beep sometime in the future. Probably not a thousand years. Instad more like 50. Isn't it fun thinking about having this thing and bringig your friends and family who aren't dead to watch it on the prescribed time.

The humor of it is somehow that the beep is so short and anticlimatic. Not a long beep. More like a blip.


This is somewhat inspired my the [clock of the long now](https://en.wikipedia.org/wiki/Clock_of_the_Long_Now)

It turns out that a hobbiest getting an electronic clock to nominally run for 50 years is actually on the edge of challenging.

Batteries come speced in amp-hours. So you need to get the standby current down of any device you are using.







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


