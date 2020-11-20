---
author: philzook58
comments: true
date: 2016-02-17 22:17:22+00:00
layout: post
link: https://www.philipzucker.com/attaching-the-jordan-wigner-string-in-numpy/
slug: attaching-the-jordan-wigner-string-in-numpy
title: Attaching the Jordan Wigner String in Numpy
wordpress_id: 397
tags:
- condensed matter
- numpy
- physics
- python
- quantum
- scipy
---

Just a fast (fast to write, not fast to run) little jordan wigner string code

    
    import numpy as np
    from numpy import kron, identity
    import numpy.linalg as la
    
    
    # sigma functions
    
    sigma_x = np.array([[0, 1],[1, 0]])
    sigma_y = np.array([[0, -1j],[1j, 0]])
    sigma_z = np.array([[1, 0],[0, -1]])
    
    # standard basis
    
    spin_up = np.array([[1],[0]])
    spin_down = np.array([[0],[1]])
    
    # spin ladder operators
    
    sigma_plus = sigma_x + 1j * sigma_y
    sigma_minus = sigma_x - 1j * sigma_y
    
    # pauli spin
    
    
    
    N = 3
    def chainify(mat, pos):
        if pos == 0:
            newmat = mat
        else:
            newmat = identity(2)
        for j in range(1,N):
            if j == pos:
                newmat = kron(newmat,mat)
            else:
                newmat = kron(newmat,identity(2))
        return newmat
    
    
    def sx(i):
        return chainify(sigma_x,i)
    def sy(i):
        return chainify(sigma_y,i)
    def sz(i):
        return chainify(sigma_z,i)
    def sp(i):
        return chainify(sigma_plus,i)
    def sm(i):
        return chainify(sigma_minus,i)
    
    
    #print sz(0)
    #print sz(1)
    #print sz(2)
    
    
    #print np.dot(sp(0),sp(0))
    # sp sm = 2 + 2 sz
    #print np.dot(sp(0),sm(0))- 2*identity(2**N) - 2*sz(0)
    
    I = identity(2**N)
    
    fdag = lambda i: sp(i)/2
    f = lambda i: sm(i)/2
    
    def stringify(mat, pos):
        if pos == 0:
            newmat = mat
        else:
            newmat = sigma_z
        for j in range(1,N):
            if j == pos:
                newmat = kron(newmat,mat)
            elif j<pos:
                newmat = kron(newmat,sigma_z)
            else:
                newmat = kron(newmat,identity(2))
        return newmat
    
    def cdag(i):
        return np.mat(stringify(sigma_plus/2, i))
    
    def c(i):
        return np.mat(stringify(sigma_minus/2, i))
    
    #print np.dot(cdag(1),c(1)) + np.dot(c(1),cdag(1)) # This is 1
    #print np.dot(cdag(1),c(2)) + np.dot(c(2),cdag(1)) # This is 0
    
    #It does appear to work.
    
    print cdag(1)*c(1) + c(1)*cdag(1) # This is 1
    print cdag(1)*c(2) + c(2)*cdag(1) # This anticommutator is 0.
    


What fun!
