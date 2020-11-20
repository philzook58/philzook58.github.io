---
author: philzook58
comments: true
date: 2017-08-10 22:38:25+00:00
layout: post
link: https://www.philipzucker.com/movidius-neural-compute-stick/
slug: movidius-neural-compute-stick
title: Movidius Neural Compute Stick
wordpress_id: 786
---

[https://developer.movidius.com/getting-started](https://developer.movidius.com/getting-started)

Installed VirtualBox and ubuntu 16.04 on my macbook (welcome to the dangerzone). Nice and fresh. sudo apt-get update and upgrade. I ran into problems eventually that are not cleared up on the forum. Switched to using a native 16.04 installation. The setup ran without a hitch. Beautiful.

Get the latest SDK

https://ncs-forum-uploads.s3.amazonaws.com/ncsdk/MvNC_SDK_01_07_07/MvNC_SDK_1.07.07.tgz

following these instructions

https://developer.movidius.com/getting-started/software-setup

I had to restart the terminal before running setup.sh for ncapi. It added something to my bashrc I think. Ok. Actually that is mentioned in the manual. Nice.

Now to test. In the bin folder

    
    make example00


also example 01-03

They all seem to run. Excellent.

Looks like ~100ms for one inference for whatever that is worth

"example00 compiles lenet8 prototxt to a binary graph, example01 profiles GooLeNet, example03 validates lenet8 using a simple inbuilt image."

https://developer.movidius.com/getting-started/run-inferencing-on-ncs-using-the-api

Go to ncapi/c_examples

make

    
    ./ncs-fullcheck -l2 -c1 ../networks/AlexNet ../images/cat.jpg




options for ncs-fullcheck are inference count and loglevel

go to py_examples

stream_infer

It really likes oxygen mask.

But was successful on sunglasses and a coffee mug. Although it did oscillate a little.

The README is interesting in the stream_infer

Stat.txt holds the average rgb and std dev values.

I wonder if I could run two sticks?

A lot of the stuff is gstreamer related

The movidius beef seems to be

    
    import mvnc.mvncapi as fx
    ncs_names = fx.EnumerateDevices()
    dev = fx.Device(ncs_names[0])
    dev.OpenDevice()
    gGraph = dev.AllocateGraph(get_graph_from_disk())
    
    gGraph.LoadTensor(preprocessed_image_buf ,"frame %s" % frame_number)
    
    inference_result, user_data = gGraph.GetResult()
    
     gGraph.DeallocateGraph()
     dev.CloseDevice()


You just load the tensor and then get it back.

There is some recommended preprocessing of the image and grabbing the label files and stuff but that is all standard python. Change the mean and std dev to match the netowrk. Also convert to a float16 array. Resize to 227x227

I've never used gstreamer. I wonder if there is a problem using the standard opencv stuff. Doesn't seem like there should be.



In the last couple days, they released instructions on how to run on a raspberry pi.



object localization would be very useful for us.

Get the script for the faster r-cnn

https://github.com/rbgirshick/py-faster-rcnn/blob/master/data/scripts/fetch_faster_rcnn_models.sh

copy contents

chmod +x that script and run it



To take a new network and make it run

you run the  mvNCCompile on the prototxt ( which describes the shape of the network and other things) and the caffemodel weightfile

for example

python3 ./mvNCCompile.pyc ./data/lenet8.prototxt -w ./data/lenet8.caffemodel -s 12 -o ./lenet8_graph

then you can profile and check it's correctness. It is unclear at this point how easy it will be to take stock networks and get them to run.

https://huangying-zhan.github.io/2016/09/22/detection-faster-rcnn.html






