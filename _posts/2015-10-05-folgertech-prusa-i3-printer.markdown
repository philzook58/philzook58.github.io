---
author: philzook58
comments: true
date: 2015-10-05 00:13:56+00:00
layout: post
link: https://www.philipzucker.com/folgertech-prusa-i3-printer/
slug: folgertech-prusa-i3-printer
title: Folgertech Prusa i3 Printer
wordpress_id: 185
---

So we bought the Prusa i3 with the aluminum frame from folgertech about two weeks ago. Was tempted first to get a Chinese version off of aliexpress, but I've heard tales of long shipping times, plus possibly some kind of importing fee. WOuldn't have saved much money anyhow. Definitely the way to go. It shipped pretty fast. Got it in about 3 days or so. Noice.

Box was surprisingly heavy and small.

There were some small problems, but nothing super major

The thermoresistor leads were overcrimped. The bot is totally unresponsive if it is freaking out about the thermoresistors (including motor control. Odd.) They should measure ~100k if they're correct. We tried resoldering them, but too brittle. Hopefully getting a replacement from folgertech.

A little confusion about what the extra molex connector was for. For attaching to the thermistor

Missing 20mm screws


The 3d printed mounting piece for the extruder had its holes with poor spacing. We dremelled out some material in order to get both screws through.







The triple screw mounting of the Z-axis motor mounts torques the linear guide rails. We found just using the two upper screws to be better and leaving the third that goes into the vertical beam out.







We had a couple things that we changed in the firmware Configuration.h file  in order to get it working.







Our motors were only going one way until we disabled the max endstops. I guess it must have been registering nonexistant endstops as being hit.







#define X_HOME_DIR -1




#define INVERT_E0_DIR true




#define DISABLE_MAX_ENDSTOPS







There are no teeth in the stage belt connector (There probably should be some?)







Two of our motor drivers did not work. We were tearing our hair out over why the extruder motor wasn't turning until we popped another one in.







Also a brief moment of panic when the entire board would not respond, but removing motor driver that had blown brought everything back up.







We also bought a lcd screen. I recommend it. Pretty nice.







Used repetier and slic3r on mac and grabbed some models from thingiverse.







I think the nozzle is 4mm, based on the folgertech website selling the extruder unit with 4mm attached. Not super sure how I'm gonna measure that.




http://reprap.org/wiki/Calibration







Maximum layer height of .4*.8 = .32




extrusion width <= .4




#define DEFAULT_AXIS_STEPS_PER_UNIT   {80,80,3840,90}







http://reprap.org/wiki/Triffid_Hunter's_Calibration_Guide






    
    // NEMA 17 motor with T2 belt and 20-tooth pulley:
    (200 * 16) / (2 * 20) = 80.0







I wonder how much stretching will change this?






    
    // NEMA 17 with standard pitch M5 threaded rod:
    (200 * 16) / 0.8 = 4000







Hmm. 3840 in the stock firmware vs 4000 in Triffid's guide?







"Personally I go for layer height of 0.2mm, and extrusion width of 0.5mm regardless of which nozzle I'm using."







Tried 200C extruder temp




With painter tape on unheated bed. Seemed to be working until thermistor fix snapped







Triffid suggests printing at decremental temps




Also 65C bed for PLA.




Gotta try that.







So close.







So very close now.


















