import numpy as np
import scipy as sp
import matplotlib.pyplot as plt


size = 10
matbig = np.zeros((size,size))
matsmall = np.zeros((size/2,size/2))

K = np.tri(size,k=1)-np.tri(size,k=-2)-3*np.identity(size) #2nd deriv matrix, no dx

print K
x = np.linspace(0,1,size)

dx = x[0]-x[1]
D2 = -K/(dx**2)

y = x

z = (np.linalg.inv(D2)).dot(np.ones(size))

plt.plot(x,y)
plt.plot(x,z)
plt.show()


#def project(mat):
    

#def solve(mat):



#def combine(mat):
    
