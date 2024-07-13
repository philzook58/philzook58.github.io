import numpy as np
import scipy as sp
import matplotlib.pyplot as plt


c = 1 #this constant is C^2*dt^2/dx^2
size = 25
steps = 1
K = np.tri(size,k=1)-np.tri(size,k=-2)-3*np.identity(size)
dx = sp.pi/(size+2)
K=-K/dx**2
#K = c*K + np.identity(size)
"""
K[0,0]=1
K[0,1]=0
K[1,0]=0

K[size-1,size-1]=1
K[size-1,size-2]=0
K[size-2,size-1]=0
"""
#print K

x=range(size)
eig = np.linalg.eig(K)
eigenvalues = np.sort(eig[0])
lowesteigs = np.argsort(eig[0])
print eigenvalues
def square(x):
    return x**2
squares = np.arange(1,size+1)**2
#squares = np.fromfunction(square,(size))

print squares
print (squares-eigenvalues)/squares
shouldbesine = eig[0][lowesteigs[0]]
print eig[0][lowesteigs[0]]
same = np.dot(K,shouldbesine)
#plt.plot(x,same)

#print np.linalg.eig(K)
#for i in range(3):
plt.plot(x,  eig[1][lowesteigs[7]])
    #plt.show()
#Plots all the green's functions


""" 
G = np.linalg.inv(K)
print G
x=range(size)
for i in range(size):
    plt.plot(x,G[i])

    """
"""plt.plot(x,G[1])
plt.plot(x,G[2])
plt.plot(x,G[50])"""
plt.show()

    


