---
author: philzook58
comments: true
date: 2015-12-16 22:26:04+00:00
layout: post
link: https://www.philipzucker.com/ipywidgets-useful-little-buggers/
slug: ipywidgets-useful-little-buggers
title: 'ipywidgets: useful little buggers'
wordpress_id: 328
---

So, the matplotlib slider functionality is basically garbage.

Let's see if ipywidgets and ipython notebooks do better

    
    sudo pip install ipywidgets




    
    ipython notebook




A basic program with sliders. You can go from there.

    
    %matplotlib inline
    import matplotlib.pyplot as plt
    import numpy as np
    from ipywidgets import interactive
    from IPython.display import display
    
    def beat_freq(f1=1.0, f2=1.0):
        times = np.linspace(0,3,100)
        signal = np.sin(2*np.pi*f1*times) + np.sin(2*np.pi*f2*times)
        #print(f1, f2, abs(f1-f2))
        plt.plot(times,signal)
        #display(Audio(data=signal, rate=rate))
    
    v = interactive(beat_freq, f1=(0.0,1.0), f2=(0.0,1.0))
    display(v)



