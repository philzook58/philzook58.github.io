import numpy as np
import scipy as sp
import matplotlib.pyplot as plt
import Matlib

# this is omega
w = 1.
size = 10

#Make periodic first derivative  
firstrow = np.zeros(size)
firstrow[-1] = 1
firstrow[1] = -1
Dc = sp.linalg.circulant(firstrow)

print Dc

#build parity matrix
P = np.fliplr(np.eye(size))
print P

# Build u operator

uDD =U*np.dot(np.dot(Dc.T,P),Dc)

#Build v operator

vDD = np.dot(Dc.T,Dc)
# build iw*Delx

iwD = w * 1j * Dc

L = iwD - vDD - uDD
