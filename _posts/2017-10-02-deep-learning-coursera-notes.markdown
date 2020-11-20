---
author: philzook58
comments: true
date: 2017-10-02 19:23:53+00:00
layout: post
link: https://www.philipzucker.com/deep-learning-coursera-notes/
slug: deep-learning-coursera-notes
title: Deep Learning Coursera Notes
wordpress_id: 895
---



cross-entropy - expectation value of log(p).

initialization - randn for weights. use 2/sqrt(input size) if using relu. See He. Avoids blow up

epoch - one run through all data

mini-batch - break up data into 1 gpus worth chunks. Worth trying different values to see

momentum - smooths gradients that are oscillating and lets build up

Adam - combined momentum and RMS prop. Works better often? 0.9 for beta1 and 0.999 for beta2 are common parameters.



Hyperparameter search - random points use log scales for some things.

reevalute your hyperparametrs occasionally

batch normalization - adds a normalization and mean subtraction at every hidden layer. makes later neurons less susceptible to earlier changes

tensorflow - variables - placeholder, make sessions, run a trainer

strategy - fit training set, dev set, test set, real world

use better optimizer bigger network if not fitting training

use more dat, rgularize if not

satisficing metric

add weight to realyy important examples

bias  - perforance on triainig set - human level is good benchmark

error analysis - ceiling on performance. Find out how many of some kind of problem are happening to figure out what is worthwhile. Do it manually

reasonably robust to random errors in training set

build first fast, iterate fast

if you need to use a different distro from training set, use the real stuff mostly in your dev and test

Break up into train dev and train-dev. so that you can know if the problem is due to mismatch or due to overfitting

manually try to make training set more like dev set on problem cases. Maybe add noise or find more examples of the error prone thing

Transfer learning

Multi-task learning

end to end - use subproblems if you have data for subproblems



And... I can't access the two last ones yet. Poo.




