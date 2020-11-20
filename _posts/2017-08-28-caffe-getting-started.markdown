---
author: philzook58
comments: true
date: 2017-08-28 15:24:50+00:00
layout: post
link: https://www.philipzucker.com/caffe-getting-started/
slug: caffe-getting-started
title: 'Caffe: Getting Started'
wordpress_id: 830
---

To Use the Movidius neural network stick we have to use caffe.

http://caffe.berkeleyvision.org/install_osx.html

http://caffe.berkeleyvision.org/installation.html#compilation

Caffe is not super friendly or well documented in my opinion.

I'm having lots of installation problems on my mac.

Segmentation Fault 11

https://github.com/BVLC/caffe/issues/2677

Trying the last thing here. Be sure to change the version numbers in the path

I eventually got it to import with

PYTHON_INCLUDE := /usr/local/Cellar/python/2.7.13/Frameworks/Python.framework/Versions/2.7/include/python2.7 \
/usr/local/Cellar/python/2.7.13/Frameworks/Python.framework/Versions/2.7/lib/python2.7/site-packages/numpy/core/include/

PYTHON_LIB := /usr/local/Cellar/python/2.7.13/Frameworks/Python.framework/Versions/2.7/lib

in MakeFile.config

I run the command with python2 which supposedly is the homebrew python.


python2 -m pip install protobuf scikit-image




Ok. Now we can start.



It is configuration file based. You make this protobuf file with the network and then load it up.

In standard configuration, you pull the data off of a database.

Data layers have the training data

top parameter is output of a layer

bottom is input

include Train Test are ways to include different guys at different stages

http://caffe.berkeleyvision.org/tutorial/loss.html

Any loss layer contributes to the eventual loss. You can weight them with a weighting parameter.  The solver runs to optimize loss layers by default. There is no parameter to specify which.

Some beginner files for syntax and exploration.

Sets input blobs in python (probably not the preferred methodology but it is fast to get up and running. Should probably at least dump into an hdf5)

Performs InnerProduct which is a matrix product and computes a euclidean loss.

Check out the mnist folder in caffe/examples. It has the clearest stuff.

    
    name: "SimpleMult"
    #input: "thedata"
    #input_dim: 2
    #input_dim: 3
    #input_dim: 100
    #input_dim: 101
    layer {
      name: "inarray"
      type: "Input"
      top: "thedata2"
      input_param { shape: { dim: 1 dim: 1 dim: 2 dim: 5 } }
    }
    layer {
      name: "inarray2"
      type: "Input"
      top: "trueoutput"
      input_param { shape: { dim: 1 dim: 1 dim: 1 dim: 1 } }
    }
    
    
    layer{
    #  name: "scalelayer"
    #  type: "Scale"
      type:"Exp"
      bottom: "thedata2"
      top: "scaleddata"
    
    
    }
    
    layer{
      name: "innerlayer"
      type: "InnerProduct"
      bottom: "thedata2"
      top: "ip"
      inner_product_param {
          num_output: 1 #the thing produces 1 output, the inner prduct. num_output however goes into the channel dim
          weight_filler {
            type: "gaussian"
            std: 0.01
          }
          bias_filler {
            type: "constant"
            value: 0
          }
        }
    }
    
    layer{
      name: "loss"
      type:"EuclideanLoss"
      bottom: "trueoutput" #needs two bottoms to compare
      bottom: "ip"
      top: "loss"
      loss_weight: 1
    }




    
    import sys
    import numpy as np
    import matplotlib.pyplot as plt
    
    sys.path.append('../caffe/python')
    import caffe
    
    #caffe.set_device(0)
    caffe.set_mode_cpu()
    #load numpy array into caffe
    net = caffe.Net('simplemult.prototxt', caffe.TEST)
    print(dir(net))
    print("inputs " , net.inputs)
    print("blobs ", net.blobs)
    print("params ", net.params)
    print(dir(net.blobs['thedata2']))
    print(net.blobs['thedata2'].num)
    print(net.blobs['thedata2'].channels)
    print(net.blobs['thedata2'].height) # num, width,
    print(net.blobs['thedata2'].width)
    
    myarray = np.arange(10).reshape((1,1,2,5))
    output = np.arange(1).reshape((1,1,1,1))
    print("start forward")
    
    net.blobs['thedata2'].reshape(*myarray.shape)
    net.blobs['thedata2'].data[...] = myarray
    
    net.blobs['trueoutput'].reshape(*output.shape)
    net.blobs['trueoutput'].data[...] = output
    print(net.blobs['thedata2'].channels)
    print(net.blobs['thedata2'].num)
    print(net.blobs['thedata2'].data)
    print("start forward")
    out = net.forward()
    print(out)
    
    #out = net.forward()
    
    #net.blobs['data'].data[...] = transformer.preprocess('data', im)
    
    
    #Using a Solver.
    #solver = caffe.get_solver(solver_prototxt_filename)
    #solver.solve()
    # solver.net.forward()
    # if intending to import network for solving
    # import via get_solver, then set input data using solver.net.blobs[]
    #solver.step(1)
    
    
    #use caffe to mutiply
    
    
    
    
    
    # receive numpy array
    



    
    # The train/test net protocol buffer definition
    net: "examples.prototxt"
    # test_iter specifies how many forward passes the test should carry out.
    # In the case of MNIST, we have test batch size 100 and 100 test iterations,
    # covering the full 10,000 testing images.
    test_iter: 100
    # Carry out testing every 500 training iterations.
    test_interval: 500
    # The base learning rate, momentum and the weight decay of the network.
    base_lr: 0.01
    momentum: 0.9
    weight_decay: 0.0005
    # The learning rate policy
    lr_policy: "inv"
    gamma: 0.0001
    power: 0.75
    # Display every 100 iterations
    display: 100
    # The maximum number of iterations
    max_iter: 10000
    # snapshot intermediate results
    snapshot: 5000
    snapshot_prefix: "examples/mnist/lenet"
    # solver mode: CPU or GPU
    solver_mode: CPU
    










This is the location of caffe.io

It has some routines for conversion to and from arrays and preprocessing in Transformer.

https://github.com/BVLC/caffe/blob/master/python/caffe/io.py



http://adilmoujahid.com/posts/2016/06/introduction-deep-learning-python-caffe/



http://christopher5106.github.io/deep/learning/2015/09/04/Deep-learning-tutorial-on-Caffe-Technology.html



https://medium.com/@liyin_27935/different-layers-in-caffe-8b49fd6fb493

https://prateekvjoshi.com/2016/02/02/deep-learning-with-caffe-in-python-part-i-defining-a-layer/

https://github.com/BVLC/caffe/wiki

You can set certain layers to not train by setting learnign rate to 0
