---
author: philzook58
comments: true
date: 2017-08-10 22:38:56+00:00
layout: post
link: https://www.philipzucker.com/drone-notes/
slug: drone-notes
title: Drone Notes
wordpress_id: 701
---

April 2017

Racing firmware mostly

CleanFlight vs betaflight vs iNav. A family of related firmwares

iNav for autonomous, betaflight for latest

Betaflight might be taking over?





Ardupilot seems to be leader for autonomous drones

pixhawk is premier computer

http://ardupilot.org/dev/docs/raspberry-pi-via-mavlink.html



gstream for video streaming

http://www.einarsundgren.se/gstreamer-basic-real-time-streaming-tutorial/

https://gstreamer.freedesktop.org/documentation/tutorials/basic/gstreamer-tools.html



uv4l?

http://www.linux-projects.org/uv4l/

even better for streaming pi?

The only thing we have working is the webrtc brwoser based camera.

You need to click call to make it start





https://blog.athelas.com/a-brief-history-of-cnns-in-image-segmentation-from-r-cnn-to-mask-r-cnn-34ea83205de4





get avr branch of ardupilot

go into examples folder

make apm2

make apm2 upload

I am not registering my apm2.6 as a serial device. Ok,  my usb cable was bad. What are the odds?

installing apmplanner from http://ardupilot.org/planner2/docs/installation-for-linux.html

command is missing an underscore

rtl is return to launch





SITL is the recommended simulator

Installed vagrant to use SITL on mac

http://ardupilot.org/dev/docs/setting-up-sitl-using-vagrant.html

http://sourabhbajaj.com/mac-setup/Vagrant/README.html

I had to make a Vagrantfile to get it to work. By default vagrant was trying to use some nonsense

Make Vagrantfile with

    
    <code><span class="no">Vagrant</span><span class="p">.</span><span class="nf">configure</span><span class="p">(</span><span class="s2">"2"</span><span class="p">)</span> <span class="k">do</span> <span class="o">|</span><span class="n">config</span><span class="o">|</span>
      <span class="n">config</span><span class="p">.</span><span class="nf">vm</span><span class="p">.</span><span class="nf">box</span> <span class="o">=</span> <span class="s2">"ubuntu/xenial64"</span>
    <span class="k">end</span></code>


https://www.vagrantup.com/intro/getting-started/boxes.html





JMavSim for software in the loop on pixhawk 2

[https://pixhawk.org/users/hil](https://pixhawk.org/users/hil)

[https://pixhawk.org/dev/hil/jmavsim](https://pixhawk.org/dev/hil/jmavsim)





What is the difference between apm planner and mission planner?

Setup pi as access point. Could use as radio then. Not very long range

https://learn.adafruit.com/setting-up-a-raspberry-pi-as-a-wifi-access-point/overview



supposedly the apm2.6 will connect through usb

Dronekit

http://python.dronekit.io/guide/quick_start.html

Mavlink and pymavlink. Evidently dronekit uses pymavlink

pymavlink is a low level python control of MAVlink messages.

mavproxy - is a command line ground station software. More feature packed than apm planner? Has ability to use multiple linked ground stations.

mavproxy can forward data to a given port. Useful, but I can't find it documented in the mavproxy docs themselves



dronecode is a set of projects

https://www.dronecode.org/platform/

Really nice looking simulator

https://github.com/Microsoft/AirSim/blob/master/docs/linux_build.md

I had to sign up with epic games and link my gihub account to be able to clone the unreal engine

We're using a Turnigy 9x. Got a ppm encoder to be able to attach to pixhawk



Setting up the pixhawk 2:

The motors need to be plugged in according to their number

http://ardupilot.org/copter/docs/connect-escs-and-motors.html

Download APM planner 2

Flashed the firmware

Ran through the initial calibration. Followed onscreen instructions.

Not immediately getting all the buttons working

http://ardupilot.org/copter/docs/common-rc-transmitter-flight-mode-configuration.htmlSw

Swapped channels 5 and 6 on controller to have flight mode siwtch

Flight modes

Stabilize - self level roll and pitch axes

FS_THR_Value error. Not sure why

Compass is not calibrating. Not sure why.



We had lots of problems until we uploaded the latest firmware. It loaded firmware at the beginning, but I guess it wasn't the latest. We built APM Planner from source and perhaps that reupdating fixed the firmware to 3.5.1

Spinning up it flew but was spinning. We wired up the motors ccw and cw opposite to the wiring diagram but never changed it in the firmware.



Drone Code uses QGroundControl. This is sort of an APM Planner alternative.

v.channels gives a dict

channel 2 was right up down

channel 3 was left up down



Dronekit Cloud. Web apis for drone control? This kind of seems like for if you have a ton of drones. Forward looking



In the field we can connect to the drone using the phone as a hotspot.



It seems like only guided mode will accept mavlink commands

The controller modes override what the pi says.

Stabilize mode should ignore mavlink commands? In case they get wonky.

RTL.

So we set the controller to have flight mode settings. In those three modes, in case something goes wrong.

put this in a dronerun file


python "$@" &




So that you won't have the program stop when ssh pipe dies.




Need to set RTL speed and altitude. Dafult may be alarming




WPNAV_SPEED




250 up default




150 down default




Crash on RTL mode. (Toilet bowl behavior? Seemed to be moving in a circle. ) I also felt like the loiter mode responded counter intuitively to my commands.




We'd like to use raspberry pi camera for visual odometry


### VISION_POSITION_DELTA


Mavlink message is implemented in ardupilot

https://github.com/PX4/OpticalFlow

http://mavlink.org/messages/common#OPTICAL_FLOW_RAD

http://ardupilot.org/dev/docs/copter-commands-in-guided-mode.html

actual source

https://github.com/ArduPilot/ardupilot/blob/master/ArduCopter/GCS_Mavlink.cpp#L967






