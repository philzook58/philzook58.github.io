---
author: philzook58
comments: true
date: 2015-12-15 19:19:02+00:00
layout: post
link: https://www.philipzucker.com/interesting-command-line-guys-sox-and-socat/
slug: interesting-command-line-guys-sox-and-socat
title: 'Interesting Command Line Guys: Sox and Socat'
wordpress_id: 317
---

http://kmkeen.com/rtl-demod-guide/

Check out Socat. Let's you pipe a file quickly over tcp and then grab it with netcat. Makes sense.

https://github.com/simonyiszk/minidemod

    
    rtl_sdr -s 240000 -f 89500000 -g 20 - | tcc -lm -run minidemod-wfm.c \
        | sox -t raw -r 240000 -e unsigned -b 8 -c 1 - -t raw - rate 48000 \
        | mplayer -quiet -rawaudio samplesize=1:channels=1:rate=48000 -demuxer rawaudio -




Sox is a sound processing swiss army knife. Intriguing. Use it like image magick. Can quickly resample sound. That's what the rate 48000 does. -r specifies that rtl-sdr is outputting 240000 samples per second. -b is that they are byte samples. -c 1 is one channel (as compared to stereo)



spectrogram is an interesting option. It can produce a spectrogram of the signal. Could use this as a waterfall plot.

synth is also interesting. Can be used to make waveforms.

    
    sox −r 8000 −n output.wav synth 3 sine 300−3300


3 second sweep of a sine wave. 300Hz-3300Hz



http://sox.sourceforge.net/sox.html

http://sox.sourceforge.net/sox.html

http://sox.sourceforge.net/sox.html


