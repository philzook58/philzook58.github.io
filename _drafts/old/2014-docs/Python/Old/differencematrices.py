import numpy as np
import scipy as sp
import matplotlib.pyplot as plt


size = 10

K = np.tri(size,k=1)-np.tri(size,k=-2)-3*np.identity(size) #2nd deriv matrix, no dx
print "Second Difference"
print K

T = np.tri(size,k=1)-np.tri(size,k=-1)-2*np.identity(size) #forward difference mat
print "Forwards Difference"
print T

U = -T.transpose() #backwards difference
print "Backwards Difference"
print U

print np.dot(T,U)


