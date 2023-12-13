---
author: philzook58
comments: true
date: 2018-04-08 18:33:09+00:00
layout: post
link: https://www.philipzucker.com/?p=1013
published: false
slug: Snickerdoodle
title: Snickerdoodle
wordpress_id: 1013
---

I finally recieved my snickerdoodle in the mail.

It came with a little card That said I could just plug in to the serial or even ssh over wifi

I don't think that is right? It did not come with a bootable SD card. Is there onboard flash?

I followed the instructions here. I tried to use the script but I had permission issues so i went the manual route

https://wiki.krtkl.com/index.php?title=SD_Card

How do I write the img?

Ok now going the automatic route

okay trying sudo -E ./sd_create.sh

The -E flag retains environment variables.

Very spooky sudoing an internet script that is formatting stuff. Seems on the up and up though

kpartx command not found. sudo apt install kpartx

Have to plug and replug

There is an alarming amount of time with no text. The thing is blinking though. Maybe it's pumping its little heart out

It said it almost instantly sent a GB. That can't be right. Maybe this is playing catchup in those rsyncs.

Oh MAH GAWD its workin. Needed a back of the pc power port. Your mileage may vary





There are other similar boards out there that can help you get a leg up on the snickerdoodle



https://lauri.võsandi.com/hdl/zynq/zybo-quickstart.html

https://docs.python.org/2/library/mmap.html

https://reference.digilentinc.com/learn/programmable-logic/tutorials/zedboard-getting-started-with-zynq/start

http://www.instructables.com/id/Booting-Linux-on-the-ZYBO/



Intriguing

http://hackage.mobilehaskell.org/

https://medium.com/@zw3rk/what-is-new-in-cross-compiling-haskell-759adaa7e1c





Gettting Vivado working

You need to have the constraint file. It is not mentioned by the snickerdoodle book.

Put down the zynq in a block design file then click the automated thingy that appears on the top. Itll treat you right



gpio does not have the default 32 ports wired up. Checkout the example project.
