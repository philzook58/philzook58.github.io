import numpy as np
import scipy as sp
import matplotlib.pyplot as plt



size = 75
p = 1
K = np.tri(size,k=1)-np.tri(size,k=-2)-3*np.identity(size)


K = K*p + 2*np.identity(size)

K[0,0]=1
K[0,1]=0
K[1,0]=0

K[size-1,size-1]=1
K[size-1,size-2]=0
K[size-2,size-1]=0


def plottimes(n):
    for i in range(1,n):
        plt.plot(x,y[Time/i-1,:])
        
print K
Time = 10
x= np.arange(size)
y = np.zeros((Time,size))
""" #moving delta function
y[0,size/2]=1
y[1,size/2+1]=1
"""
#Oscillating sine wave with given nodes
mode = 7
y[0,:]=np.sin(mode*sp.pi*x/(size-1))
y[1,:]=.9*y[0,:]

for i in range(2,Time):
    y[i,:]=np.dot(K,y[i-1,:])-y[i-2,:]

#plottimes(20)
for i in range(Time):
        plt.plot(x,y[i-1,:])
#plt.plot(x,y[0,:])
#plt.plot(x,y[5,:])
plt.show()


"""
#Plots all the green's functions

G = np.linalg.inv(K)
print G*4
x=range(size)
for i in range(size):
    plt.plot(x,G[i])
"""
def plotmovie():
    for i in range(Time):
        plt.clf()
        plt.plot(x,y[i,:])
        plt.axis([0,size,0,1])
        name = "Heatrand/"+str('%03d' % i)+".png"
        plt.savefig(name)
    


