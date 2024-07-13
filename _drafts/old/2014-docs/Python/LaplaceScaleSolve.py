# -*- coding: utf-8 -*-
"""
Created on Wed Oct 30 21:33:39 2013

@author: Philip
"""

import numpy as np
import numpy.fft as fft
import scipy as sp
import matplotlib.pyplot as plt
from scipy import linalg
import Matlib

N = 4 

L = Matlib.C(N)

print L
UdagL = fft.fftshift(fft.fft(L,axis=1),axes=1)
print UdagL
UdagLU = fft.fftshift(fft.ifft(L,axis=0),axes=0)
print UdagLU

I = np.identity(N)
L2 = np.kron(L,I) + np.kron(I,L)

def Schur(A,B,C,D):
    return A - np.dot(np.dot(B,linalg.inverse(D)),C)

#Schur

#def fftmatrix()