---
author: philzook58
comments: true
date: 2017-08-16 17:51:57+00:00
layout: post
link: https://www.philipzucker.com/nerve-elixir-os-packager-raspberry-pi/
slug: nerve-elixir-os-packager-raspberry-pi
title: 'Nerve: Elixir OS packager  for Raspberry Pi'
wordpress_id: 799
---

I found out about Elxir Nerve on the Functional Geekery podcast. Seems right up my alley.

It builds a minimal linux image with erlang running. Runs on the raspberry pis and beaglebone.

Erlang and elixir does intrigue me a lot, but I haven't gotten over the hump yet.

Summary of experience so far: Kind of painful. Docs aren't great. Being an elixir newbie hurts. Strong suspicion that going outside the prebuilt stuff is gonna be tough.

https://hexdocs.pm/nerves/installation.html#linux

Installation

Getting Started

https://hexdocs.pm/nerves/getting-started.html#content

mix nerves.new hello_nerves

need to export the target variable. Why is this  not part of the config file. There probably is a reason.

export MIX_TARGET=rpi0

Building the firmware

mix firmware

writing to sd card

mix firmware.burn

says I need to install fwup

makes sense. Not in apt-get. Downloaded the deb file and installed

[https://github.com/fhunleth/fwup](https://github.com/fhunleth/fwup)



Booted up. Shows things on hdmi. Cool

went to

https://github.com/nerves-project/nerves_examples/tree/master/hello_wifi

run the following before building to set wifi stuff

    
    <span class="pl-k">export</span> NERVES_WIFI_SSID=my_accesspoint_name
    <span class="pl-k">export</span> NERVES_WIFI_PSK=secret


mix deps.get

mix firmware

mix firmware.burn



Hmm. Can't get it to work. i have Erlang 20 and It wants 19. Upon further inspection, this example is completely deprecated. Sigh.



Alright.

mix nerse.new wifi_test

https://github.com/nerves-project/nerves_examples/blob/master/hello_network/mix.exs

https://github.com/nerves-project/nerves_network

https://hexdocs.pm/nerves_network/Nerves.Network.html

add in the nerves_network dependency into mix.exs

    
    # Specify target specific dependencies
    def deps("host"), do: []
    def deps(target) do
    [ system(target),
    {:bootloader, "~> 0.1"},
    {:nerves_runtime, "~> 0.4"},
    {:nerves_network, "~> 0.3"},
    ]
    end


added

    
    config <span class="pl-c1">:nerves_network</span>,
      <span class="pl-c1">regulatory_domain:</span> <span class="pl-s"><span class="pl-pds">"</span>US<span class="pl-pds">"</span></span>


at the end of the config file



Alright. I admit temporary defeat. The pi zero is an awful thing.



Hmmm!

If you plug the usb port of the pi zero into your computer it shows up as a serial device

in my case /dev/ttyACM0

you can open that up with screen or the arduino serial monitor

baud 115200

And you have access to an elixir console.

Interesting.



I was able to get linklocal ethernet connection working. You have to setup nerves_network usb0 to use method :linklocal.

I used nerves_init_gadget

https://github.com/fhunleth/nerves_init_gadget

In addition on unbutu you have you go into the netowrk settings and change the ipv4 dropdown in the options to linklocal only. Then the pi is available at nerves.local



The edimax wifi dongle does not work by default

https://www.grappendorf.net/tutorials/nerves-pizero-edimax.html

hmm buildroot https://buildroot.org/

This is intriguing. It is a build tool for getting linux on embedded systems








