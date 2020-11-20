---
author: philzook58
comments: true
date: 2017-04-17 03:28:54+00:00
layout: post
link: https://www.philipzucker.com/deep-learning-basic-shapes/
slug: deep-learning-basic-shapes
title: Deep Learning Basic Shapes
wordpress_id: 586
tags:
- aws
- deep learning
- keras
- tensorflow
---

Our Github Source: [https://github.com/ishmandoo/shape_classifier](https://github.com/ishmandoo/shape_classifier)

We are trying to get some basic deep learning to happen. Don some MNIST tutorials before, but there in lies the problem. These tutorials have a lot already done for you.

So we're going to try an even simpler task. Classifying computer generated shapes.

We generate images of shapes using scikit-image.

We started off using Caffe (because it has support for non cuda gpu) and were displeased. It's heavily configuration file based. The python api mostly is about generating configuration files for you. You need to dip into C to get some stuff done. You need to put your files into an intermediate database file. The docs mostly consist of tutorial python notebooks. It was just all too much barrier for getting started. We may return for various reasons though at some point. It has a database of pretrained networks. Also supposedly Caffe is fast.

Once we switched over to Keras, things started going a lot smoother.

We copied the VGG convolutional example network and chopped out some of it's layers and lessened the size of the hidden layers. The more complicated the network, the more time and data its going to need. This is a simple task so it shouldn't need so much.

We had an initial problem with the loss diverging. Our learning rate was too high. We had to cut it down. I read somewhere that a rule of thumb is to decrease the learning rate by factors of 2 until the loss stops diverging.

We also weren't sure what cross-entropy was. This helped.

[http://datascience.stackexchange.com/questions/9302/the-cross-entropy-error-function-in-neural-networks](http://datascience.stackexchange.com/questions/9302/the-cross-entropy-error-function-in-neural-networks)

The cross entropy is the number of bits you'd need to determine the actual answer after the neural network gave you its guess for the probabilities of the answer given the input. If the neural network gives you a 1 for one answer then it is absolutely certain and you need no more bits. If it gives you a 1 for the wrong answer, you'd need infinitely many bits if you were encoding answers using the networks guesses. In efficient coding, impossible answers take infinite bits. Kind of funny thing.

If I understand it right, the cross entropy of a randomly guessing neural network would be $latex \log _2 (3 )$, since you'd expect it to take that many bits to encode 3 options. The starting point tends to be around 6 or so though?

The tensorflow vs theano backend is a constant problem. I suppose we're going to use the tensorflow backend. Tensorflow has momentum behind it.

You can change the backend by changing keras file. https://keras.io/backend/

But you also need to constantly be switching the channel ordering.

The decay parameter is a thing that decreases the learning rate. Basically I think it is 1/iteration at which you want the learning to slow down?

[http://stats.stackexchange.com/questions/211334/keras-how-does-sgd-learning-rate-decay-work](http://stats.stackexchange.com/questions/211334/keras-how-does-sgd-learning-rate-decay-work)

[https://blog.keras.io/how-convolutional-neural-networks-see-the-world.html](https://blog.keras.io/how-convolutional-neural-networks-see-the-world.html)

I think we're going to use AWS for now rather than buy a nice graphics card. Unfortunately, it is important to have CUDA capability and our card is a Radeon.

AWS isn't so bad. We experienced maybe a 10x speedup in a very unofficial test compared to local cpu on a g2.xlarge.

[https://github.com/ritchieng/tensorflow-aws-ami](https://github.com/ritchieng/tensorflow-aws-ami)

This is useful. Although the software is constantly going out of date. It has enough to get running.

The smallest g2 instances are currently 0.60$/hour for a regular instance.

Spot instances are often suggested. They cannot be stopped, only terminated which sucks. You can [mount an external EBS](http://docs.aws.amazon.com/AWSEC2/latest/UserGuide/ebs-using-volumes.html). Spot instance are somewhere between 0.20$ and 0.6$ per hour.

You can check here

[https://aws.amazon.com/ec2/spot/pricing/](https://aws.amazon.com/ec2/spot/pricing/)

Or on your AWS console.




