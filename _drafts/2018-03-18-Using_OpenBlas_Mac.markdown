---
author: philzook58
comments: true
date: 2018-03-18 22:25:49+00:00
layout: post
link: https://www.philipzucker.com/?p=1014
published: false
slug: Using OpenBlas Mac
title: Using OpenBlas Mac
wordpress_id: 1014
---

brew install openblas


gcc -lblas -I /usr/local/Cellar/openblas/0.2.20/include/ hello.c







    
    #include <cblas.h>
    
    int main(){
    
    return 0;
    
    }




useful stuff

https://software.intel.com/sites/default/files/managed/83/0a/mkl-2018-developer-reference-c_0.pdf

cblas_daxpy is what blas functions look like

we should probably be using the gnu scientific library


