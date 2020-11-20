---
author: philzook58
comments: true
date: 2015-09-04 18:05:27+00:00
layout: post
link: https://www.philipzucker.com/python-wave-file-fun-and-audio-on-arduino/
slug: python-wave-file-fun-and-audio-on-arduino
title: Python Wave File Fun and Audio on Arduino
wordpress_id: 117
---

I had never touched the struct library before. I believe it is the main way to use python to interact with bit formats.

[https://docs.python.org/2/library/struct.html](https://docs.python.org/2/library/struct.html)

Strings are byty things, so I guess struct uses them as a bridge between pythons weirdo types and the bare metal of c types. I think something similar can be done using numpy.

16 bit wave is signed integers, 8bit is unsigned. That goofed me off. I never got the resaved file to sound not alike a demon though, so there is something wrong in the code. The outputted c file worked like a charm, so I guess who cares. That's all I wanted anyhow, I was just rewriting the wave for debugging.

    
    import wave
    import struct
    
    myaudio = wave.open('test.wav', 'r')
    
    
    newaudio = wave.open('new.wav', 'w')
    newaudio.setparams((1, 1, myaudio.getframerate(), 0, 'NONE', 'not compressed'))
    
    f = open('music.c', 'w')
    
    f.write('const byte audio[] PROGMEM= {')
    
    f.write(str(myaudio.getnframes() >> 8 + 128))
    for i in range( myaudio.getnframes()-1):
    #for i in range(100):
        f.write(',')
        waveData = myaudio.readframes(1)
        data = struct.unpack("h", waveData)
        val = ( int(data[0])>> 8) + 128
    
        f.write(str( val ))
        packed_value = struct.pack('B', val) #unsigned char is 1 byte
    
        newaudio.writeframes(packed_value)
    
    
    print mymax
    print mymin
    f.write('};\n')
    myaudio.close()
    newaudio.close()
    f.close()
    


Tried using an R-2R ladder to make a ADC for the arduino. It worked, we buffered the output with a simple emitter follower circuit.

Way overkill though.

I was thinking of using the analog in in some kind of feedback loop with a capacitor as an ADC when I found this.

[http://highlowtech.org/?p=1963](http://highlowtech.org/?p=1963)

This does the same thing with no parts (well, still need a buffer to get full volume). Clev. Majorly clev.

A speaker can't respond at ~60kHz (nor would you hear it) so the fact that there is a pwm and not a true ADC going does not matter. Noice.



Incidentally, installed crayon for wordpress. Code looks way freaking better.
