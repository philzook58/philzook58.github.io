---
author: philzook58
comments: true
date: 2015-09-09 21:19:34+00:00
layout: post
link: https://www.philipzucker.com/recording-audio-in-python/
slug: recording-audio-in-python
title: Recording Audio in Python
wordpress_id: 128
---

I was thinking that maybe recording audio might be convenient way to get reasonable amounts of data into my computer. Probably better than using an arduino for a bunch of reasons. Plus I've already bought some external DACs for recording audio.

A useful Link

[http://www.swharden.com/blog/2013-05-09-realtime-fft-audio-visualization-with-python/](http://www.swharden.com/blog/2013-05-09-realtime-fft-audio-visualization-with-python/)

I followed these instructions [https://gist.github.com/jiaaro/9767512210a1d80a8a0d](https://gist.github.com/jiaaro/9767512210a1d80a8a0d)

to install

    
    pip install --allow-external pyaudio --allow-unverified pyaudio pyaudio


Here is some very slightly modified from the pyaudio example code. May want to eventually select which input device you want

    
    import pyaudio
    import numpy as np
    import matplotlib
    
    CHUNK = 1024
    FORMAT = pyaudio.paInt16
    CHANNELS = 2
    RATE = 44100
    RECORD_SECONDS = .5
    WAVE_OUTPUT_FILENAME = "output.wav"
    
    p = pyaudio.PyAudio()
    '''
    print("Input Device Info")
    print(p.get_default_input_device_info())
    print("Output Device Info")
    print(p.get_default_output_device_info())
    
    for i in range(p.get_host_api_count()):
        print(p.get_host_api_info_by_index(i))
    '''
    for index in range(p.get_device_count()):
        print(p.get_device_info_by_index(index))
    
    stream = p.open(format=FORMAT,
                    channels=CHANNELS,
                    rate=RATE,
                    input=True,
                    frames_per_buffer=CHUNK,
                    input_device_index=0)
    
    print("* recording")
    
    frames = []
    
    
    for i in range(0, int(RATE / CHUNK * RECORD_SECONDS)):
        data = stream.read(CHUNK)
        frames.append(data)
    
    
    print("* done recording")
    
    stream.stop_stream()
    stream.close()
    p.terminate()
    
    time = []
    
    
    audio = np.fromstring(b''.join(frames),dtype=np.int16)
    
    t = np.linspace(0,RECORD_SECONDS,num=audio.size)
    import matplotlib.pyplot as plt
    plt.plot(t,audio)
    plt.show()


Maybe I'll write in a moving fft or some realtime watching would be nice.

Pretty Good!


