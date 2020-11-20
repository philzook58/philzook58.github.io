---
author: philzook58
comments: true
date: 2017-08-21 17:39:47+00:00
layout: post
link: https://www.philipzucker.com/couple-interesting-deep-learning-topics/
slug: couple-interesting-deep-learning-topics
title: A couple of interesting deep learning topics
wordpress_id: 780
---

https://hackernoon.com/up-to-speed-on-deep-learning-july-update-4513a5d61b78

Image Segmentation

How to find objects as subimages in an image:

https://blog.athelas.com/a-brief-history-of-cnns-in-image-segmentation-from-r-cnn-to-mask-r-cnn-34ea83205de4

Basically, use classifying networks on suggested subboxes. Then there are some tricks layered on top of that idea, like using a netowkr to suggest possible subboxes. There exist implementations of these things in tensorflow, caffe and others.

http://blog.qure.ai/notes/semantic-segmentation-deep-learning-review

One shot learning

https://hackernoon.com/one-shot-learning-with-siamese-networks-in-pytorch-8ddaab10340e

Differentiate whether two pictures are of the same object using only the one image.

One-Shot Imitation learning

https://arxiv.org/abs/1703.07326
