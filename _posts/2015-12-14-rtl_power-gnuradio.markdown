---
author: philzook58
comments: true
date: 2015-12-14 19:47:56+00:00
layout: post
link: https://www.philipzucker.com/rtl_power-gnuradio/
slug: rtl_power-gnuradio
title: rtl_power & gnuradio
wordpress_id: 293
---

You can take a big honkin spectrum with rtl_power

[http://kmkeen.com/rtl-power/](http://kmkeen.com/rtl-power/)

    
    <code>rtl_power -f 118M:137M:8k -g 50 -i 10 -e 1h airband.csv</code>


Frequency range and steps are self explanatory. Maximum steps is 2M ish (max sampling rate of SDR)

-i is integration time for each step (defualt is 10s)

-e is timeout time (will go forever if you don't set)

-g is gain

Each line of the output is one window of sampling basically. The db values at the end are interpolating the frequencies in the window of the line.

Set -i and -e to the same number to just take one spectrum.



[flatten.py ](https://raw.githubusercontent.com/keenerd/rtl-sdr-misc/master/heatmap/flatten.py) converts to a more sane format for my purposes, a list of frequencies and powers.

Then a short python script

    
    import numpy as np
    import sys
    import matplotlib.pyplot as plt
    
    
    filename = sys.argv[1]
    
    
    freq, db = np.loadtxt(filename, delimiter=',', usecols=(0, 1), unpack=True)
    
    plt.plot(freq,db)
    plt.xlabel('Hz')
    plt.ylabel('db')
    plt.show()


that talks the csv filename as an argument will make a simple plot. You could also do this with plt.plotfile maybe? Something to investigate in the future. numpy.loadtxt is pretty clutch.



Or you can just spreadsheet it up

or use gnuplot (ick)

[http://heat.wq.lc/#](http://heat.wq.lc/#)







Also,  you can get a simple scope in gnuradio by just taking the rtl_sdr block and hook it right up to a scope block. Pretty Handy little guy.

Autocompleting gr_ ( double tab ) on my comp gives a list of interesting built ins:


gr_constellation_plot  gr_plot_psd_c          gr_spectrogram_plot_c




gr_filter_design       gr_plot_psd_f          gr_spectrogram_plot_f




gr_modtool             gr_plot_qt             gr_spectrogram_plot_i




gr_plot_char           gr_plot_short          gr_spectrogram_plot_s




gr_plot_const          gr_psd_plot_b          gr_time_plot_b




gr_plot_fft            gr_psd_plot_c          gr_time_plot_c




gr_plot_fft_c          gr_psd_plot_f          gr_time_plot_f




gr_plot_fft_f          gr_psd_plot_i          gr_time_plot_i




gr_plot_float          gr_psd_plot_s          gr_time_plot_s




gr_plot_int            gr_read_file_metadata  gr_time_raster_b




gr_plot_iq             gr_spectrogram_plot    gr_time_raster_f




gr_plot_psd            gr_spectrogram_plot_b 




Presumably these are for giving files to. The b, f, i, s must be the value type that was saved to file (byte char short float?)




For some reason I found gnuradio terrifying upon first inspection, but now it seems so friendly. What up wit dat?
