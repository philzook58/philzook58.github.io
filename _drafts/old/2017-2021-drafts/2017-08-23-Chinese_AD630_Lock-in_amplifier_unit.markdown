---
author: philzook58
comments: true
date: 2017-08-23 15:13:27+00:00
layout: post
link: https://www.philipzucker.com/?p=823
published: false
slug: Chinese AD630 Lock-in amplifier unit
title: Chinese AD630 Lock-in amplifier unit
wordpress_id: 823
---

Got this unit off [aliexpress](https://www.aliexpress.com/item/Balanced-modulator-AD630-lock-in-amplifier-module-for-weak-signal-detection-modulation-and-demodulation/32759816636.html?spm=2114.search0104.3.2.sg7Zjn&ws_ab_test=searchweb0_0,searchweb201602_1_10152_10065_10151_10068_10130_10324_10325_10326_10084_10083_10080_10307_10082_10081_10110_10178_10137_10111_10060_10112_10113_10155_10114_10154_10056_10055_10054_10312_10313_10059_10314_10315_10316_100031_10099_10078_10079_10103_10073_10102_10052_10053_10142_10107_10050_10051,searchweb201603_4,ppcSwitch_5&btsid=ae563c95-910e-4ad6-b1b9-5d6284f18965&algo_expid=fec7859e-079c-425a-a0fd-cae859205689-0&algo_pvid=fec7859e-079c-425a-a0fd-cae859205689). Kind of a rip. Pretty expensive. Hope it works well.

"Module default lock function, IN1 for the signal to be detected, IN2 for the synchronization signal, OUT output.

Onboard low pass filter configured to require the user to use the jumper switch."

[![htb1tnc7nvxxxxacaxxxq6xxfxxxd](http://www.philipzucker.com/wp-content/uploads/2017/08/HTB1Tnc7NVXXXXaCaXXXq6xXFXXXD-300x209.jpg)](http://www.philipzucker.com/wp-content/uploads/2017/08/HTB1Tnc7NVXXXXaCaXXXq6xXFXXXD.jpg)



So the docs are bit sparse on this one, but luckily we've got the data sheet and I can just make out the traces on the black pcb

[http://www.analog.com/media/en/technical-documentation/data-sheets/AD630.pdf](http://www.analog.com/media/en/technical-documentation/data-sheets/AD630.pdf)

2 back to back 9V batteries should be adequate for the split voltage supply. It appears to be within spec of both chips

The circuit appears to be configured largely in accordance with fig 35

In1 - pin 1 - RinA. A 2.5kOhm reistor to noninverting input of amplfiier A

In2 - pin 9 - SelB - Selects between A and B. Actually a comparator between selA and selB. selA (pin 10) is grounded.

In3 - pin 17 - RinB

Out connects to the back two pegs of the jumper

top jumper connects it to pin 13 - Vout.

Bottom connector wires it down to the auxiliary chip, which I think is a low-pass filter. It's a TI op amp with lots of unpopulated components. Hmm.

http://www.ti.com/lit/ds/symlink/op07d.pdf

ok. After a preliminary test, I do not know what the thing is doing

Putting the same 1Vpp signal on In1 and In2 gives roughly a sin^2 wave that peaks at -2V. This seems consistent with a gain of -2. It did not seem very clean however.

Using the second mode seemed to bottom out at the voltage rail.






