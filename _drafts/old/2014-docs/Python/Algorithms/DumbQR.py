import numpy as np
import scipy as sp
import matplotlib.pyplot as plt
from scipy import linalg



size = 3
A = np.random.random((size,size))
#A = np.identity(size)
Q = np.zeros((size,size))
R = np.zeros((size,size))

temp = np.zeros(size)
Q[:,0] = A[:,0]/linalg.norm(A[:,0])

R[0,0]= linalg.norm(A[:,0])

for i in range(size):
    Q[:,i] = A[:,i]
    
    for j in range(i):
        R[j,i]= np.dot(Q[:,i],Q[:,j])
        Q[:,i]= Q[:,i]-Q[:,j]*np.dot(Q[:,i],Q[:,j])
    R[i,i]= linalg.norm(Q[:,i])
    Q[:,i] = Q[:,i]/linalg.norm(Q[:,i])

print A                                
print Q
print R
print "Error"
print str(np.dot(Q,R)-A)
print "Scipy QR"
print linalg.qr(A)
