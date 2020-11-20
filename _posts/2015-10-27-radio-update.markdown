---
author: philzook58
comments: true
date: 2015-10-27 03:50:17+00:00
layout: post
link: https://www.philipzucker.com/radio-update/
slug: radio-update
title: Radio Update
wordpress_id: 209
---

Got the thing to receive in my own python script. Pretty dang cool.

Now, some problems. The framerate variable makes no sense. My math must be wrong somewhere. Lower framerates devolve into industrial music.

Some good hiccups, had to convert from the default doubles to float32.

Using socket was pretty easy.

Declare variables global. I believe globals are supposed to be bad, but they sure are useful.

Tkinter is pretty good for quick stuff.

    
    #rtl_tcp -s 2048000 -f 101140000
    #-f 101140000 -g 40 -n 20480000
    
    #rtl_sdr -f 101140000 -g 40 -n 20480000 ab120_10s.dat
    
    from sys import argv
    #This will allow a command line assignment of the filename
    #script, filename = argv
    
    
    import struct
    import numpy as np
    from scipy import signal
    import matplotlib.pyplot as plt
    import scipy as sp
    
    import socket
    
    
    TCP_IP = '127.0.0.1'
    TCP_PORT = 1234
    BUFFER_SIZE = 1024
    
    import pyaudio
    
    p = pyaudio.PyAudio()
    
    # open stream (2)
    framerate = 204800 #10000 # for industrial music
    samplerate = 2048000
    
    s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    s.connect((TCP_IP, TCP_PORT))
    offset = -4.0e5
    def callback(in_data, frame_count, time_info, status):
        #data = wf.readframes(frame_count)
        data = ""
        #print frame_count
        for i in range(frame_count * samplerate / framerate / BUFFER_SIZE * 2):
            data = data + s.recv(BUFFER_SIZE)
    
        rawdata = np.fromstring(data,dtype=np.uint8)
        real = rawdata[0::2]-127.5
        imag = rawdata[1::2]-127.5
        vals = real + 1.j * imag
        T = frame_count / float(framerate) #seconds
        fshift = offset#-4.0e5 #-3.5e5
        #print offset
        vals = vals * np.exp ( 1.j *2 * np.pi * np.linspace(0, fshift * T  ,vals.size)) # number of cycles
        vals = sp.signal.decimate(vals,10)
        diff = vals[0:-1] * np.conj(vals[1:])
        sig = np.arctan2(np.real(diff),np.imag(diff))
        sig = sp.signal.resample(sig,frame_count)
        return (np.float32(sig/np.pi), pyaudio.paContinue)
        #return (sig/np.pi, pyaudio.paContinue)
    
    stream = p.open(format=pyaudio.paFloat32,
                    channels=1,
                    rate=framerate,
                    output=True,
                    stream_callback=callback)
    
    
    from matplotlib.widgets import Slider
    
    
    
    import signal
    import sys
    def signal_handler(signal, frame):
            print('You pressed Ctrl+C!')
            s.close()
            stream.stop_stream()
            stream.close()
    
            # close PyAudio (5)
            p.terminate()
            sys.exit(0)
    signal.signal(signal.SIGINT, signal_handler)
    '''
    axcolor = 'lightgoldenrodyellow'
    axfreq = plt.axes([0.25, 0.1, 0.65, 0.03], axisbg=axcolor)
    
    
    sfreq = Slider(axfreq, 'Freq', -5.e5, -3.e5, valinit=-4.e5)
    def update(val):
        offset = sfreq.val
    sfreq.on_changed(update)
    plt.ion()
    plt.show()
    '''
    
    from Tkinter import *
    
    def update(event):
        global offset
        offset = event.widget.get()
        #print offset
    
    master = Tk()
    w = Scale(master, from_=-10e5, to=0)
    w.pack()
    w.set(-4e5)
    w.bind('<ButtonRelease>', update)
    
    #w = Scale(master, from_=0, to=200, orient=HORIZONTAL)
    #w.pack()
    
    master.mainloop()
    
    signal.pause()
    



