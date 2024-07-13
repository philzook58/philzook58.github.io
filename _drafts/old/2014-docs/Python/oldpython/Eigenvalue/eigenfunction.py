import numpy as np
import scipy as sp
import matplotlib.pyplot as plt


size = 100

K = np.tri(size,k=1)-np.tri(size,k=-2)-3*np.identity(size) #2nd deriv matrix, no dx


x = np.linspace(0,1,size)

dx = x[0]-x[1]
D2 = -K/(dx**2)



q = np.linalg.eig(D2)[1][58]
print q

plt.plot(x,q)
plt.show()
