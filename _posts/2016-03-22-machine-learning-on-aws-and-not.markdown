---
author: philzook58
comments: true
date: 2016-03-22 15:38:01+00:00
layout: post
link: https://www.philipzucker.com/machine-learning-on-aws-and-not/
slug: machine-learning-on-aws-and-not
title: Machine Learning on AWS and not
wordpress_id: 408
---

So gonna give machine learning a try on AWS. Ultimately, I think this is not economically viable, but since I'm just screwing around, whatever.

I searched for a prebuilt AMI ami-180ad670 called gpu_theano or something. Picked the first one for no reason except it seemed reasonable.

I picked a spot instance with .30$ per hour as max rate. g2.2xlarge

ran some script inside called check_theano.py. Theano appears to be working on the gpu. (theano )

Let's see if we can get this puppy running

[https://github.com/alexjc/neural-doodle](https://github.com/alexjc/neural-doodle)


Error: Command '['/home/ubuntu/neural-doodle/pyvenv/bin/python3', '-Im', 'ensurepip', '--upgrade', '--default-pip']' returned non-zero exit status 1




Okay. Forget doing the virtual env stuff. Not worth it on a burner computer.


sudo apt-get install python3-dev

sudo apt-get install python3-pip

sudo python3 -m pip install numpy

sudo python3 -m pip install scipy

Why aren't these in requirements.txt

I wonder if I could use python2. scipy and numpy are probably already installed.


sudo python3 -m pip install --upgrade setuptools




sudo python3 -m pip install --upgrade cython




sudo apt-get update




    
    <code><span class="pln">sudo apt</span><span class="pun">-</span><span class="pln">get build</span><span class="pun">-</span><span class="pln">dep matplotlib</span></code>




sudo apt-get install libfreetype6-dev




sudo apt-get build-dep pillow




sudo python3 -m pip install --upgrade scikit-image




sudo python3 -m pip install  theano




sudo python3 -m pip install lasagne




Bad move DOn't install lasagne and theano on their own




    
    python3 -m pip install --ignore-installed -r requirements.txt




This is running slow as hell. What is up. Github page




Using screen so ssh failing won't quit job




use screen




run your job




detach with ctrl-a ctrl-d




then you can reattach with screen -r


[https://github.com/BVLC/caffe/wiki/Install-Caffe-on-EC2-from-scratch-(Ubuntu,-CUDA-7,-cuDNN)](https://github.com/BVLC/caffe/wiki/Install-Caffe-on-EC2-from-scratch-(Ubuntu,-CUDA-7,-cuDNN))

Interesting Link. Should try this next time.


Okay. I got a free nvidia graphics card (GTX 560 ti) from a bro. I set up my router to forward port 22 to my desktop so I can ssh in from anywhere. Installed cuda and cudnn. Tensorflow by default does support this old of a graphics card. Saw some rumblings




FInally got scipy to install once I download the blas and lapack libaryr prerequisites using apt-get.




I was having a lot of trouble installing scikit-image with some kind of error about pgen. Eventually I renamed /usr/local/bin/pgen which is not the porgram it is expecting to /usr/local/bin/pgentmp  and then it seems txo get past it fine.




sudo apt-get install libatlas-base-dev




Needed to install some matplotlib dependancies




Needed to set a .theanorc file. Change cude5.5 to the verison you have


http://stackoverflow.com/questions/18165131/getting-theano-to-use-the-gpu

Finally running.

I'd say the speed is on par with the AWS. It will take about an hour or two to finish the job at 40 iterations.

Phase 3 is the beast.

Failed at phase 3. My card has only 1GB of ram. Not enough I guess.

I'll post this for now, but clearly a work in progress.




