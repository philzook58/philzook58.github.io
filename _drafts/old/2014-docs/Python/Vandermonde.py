import numpy as np
import matplotlib.pyplot as plt
import scipy as sp
import scipy.linalg as linalg
import numpy.linalg as nplinalg

"""
for i in range(10):
    points = np.linspace(0,1,10*i+1)
    polyterm = 3
    V = np.vander(points,polyterm)
    #print points
    print i*10
    print linalg.svdvals(V)

#print V
"""
num = 30
samples = range(num)

polyorder = 3
cond = np.zeros((num,polyorder))
for j in range(polyorder):
    for i in samples:
        points = np.linspace(0,1,i+1)
        polyterm = j+1
        V = np.vander(points,polyterm)
        #print points
        #print i*10
        #print linalg.svdvals(V)
        cond[i,j] = nplinalg.cond(V)

#print V
#print samples
#print cond
    for j in range(polyorder):
        plt.plot(samples,cond[:,j])
plt.show()
