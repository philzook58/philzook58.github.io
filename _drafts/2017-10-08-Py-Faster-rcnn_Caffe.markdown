---
author: philzook58
comments: true
date: 2017-10-08 14:23:47+00:00
layout: post
link: https://www.philipzucker.com/?p=902
published: false
slug: Py-Faster-rcnn Caffe
title: Py-Faster-rcnn Caffe
wordpress_id: 902
---

I'm using Ubuntu 17.04, Cuda 9

Lots of cuda 9 based errors

Need to delete  any lines in Makefile.config that mention compute_20 which is no longer supported


CUDA_ARCH :=    -gencode arch=compute_20,code=sm_20 \




Insano error




/usr/local/cuda/include/crt/common_functions.h:64:24: error: token ""__CUDACC_VER__ is no longer supported.  Use __CUDACC_VER_MAJOR__, __CUDACC_VER_MINOR__, and __CUDACC_VER_BUILD__ instead."" is not valid in preprocessor expressions




#define __CUDACC_VER__ "__CUDACC_VER__ is no longer supported.  Use __CUDACC_VER_MAJOR__, __CUDACC_VER_MINOR__, and __CUDACC_VER_BUILD__ instead."




go into /usr/local/cuda/include/crt/common_functions.h and replace that string wtih




#define __CUDACC_VER__   __CUDACC_VER_BUILD__




also needed to make symbolic links to libhdf5 files


https://github.com/NVIDIA/DIGITS/issues/156



https://github.com/BVLC/caffe/issues/2690

changed the include dirs to find -lhdf5

    
    <span class="pl-mi1">INCLUDE_DIRS := $(PYTHON_INCLUDE) /usr/local/include /usr/include/hdf5/serial/</span>
    <span class="pl-mi1">LIBRARY_DIRS := $(PYTHON_LIB) /usr/local/lib /usr/lib /usr/lib/x86_64-linux-gnu/hdf5/serial/
    </span>
    


This is another good one for finding hdf5.h

https://ahmedibrahimvt.wordpress.com/2017/02/19/fatal-error-hdf5-h-no-such-file-or-directory/

export CPATH="/usr/include/hdf5/serial/"







A similar project

https://github.com/weiliu89/caffe/tree/ssd

https://github.com/BVLC/caffe/wiki/GeForce-GTX-1080,---CUDA-8.0,---Ubuntu-16.04,---Caffe

had to edit config file like said to stop error

even worse errors ensued. Trying to isntall gcc5

VideoCapture error

    
    sudo apt-get install libopencv-dev python-opencv


http://milq.github.io/install-opencv-ubuntu-debian/








