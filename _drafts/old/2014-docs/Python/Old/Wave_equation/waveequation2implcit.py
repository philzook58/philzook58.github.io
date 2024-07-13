import numpy as np
import scipy as sp
import matplotlib.pyplot as plt



size = 100
L = 1. #Total x length
dx = L/size

timestep = 1500
Time = 2.
dt = Time/timestep
c = 1 #c, speed of wave
c2 = c**2
K = np.tri(size,k=1)-np.tri(size,k=-2)-3*np.identity(size)


K = -K/dx**2*c2*dt**2 + np.identity(size)

def Gaussian(x,b,sigma):
    return np.exp(-((x-b)/sigma)**2)

K[0,0]=1
K[0,1]=0
K[1,0]=0

K[size-1,size-1]=1
K[size-1,size-2]=0
K[size-2,size-1]=0


def plottimes(n):
    for i in range(1,n):
        plt.plot(x,y[timestep/i-1,:])
        
print K
x= np.linspace(0,L,size)
y = np.zeros((timestep,size))
#moving Gaussian function
y[0,:] = Gaussian(x,L/2,5*dx)
plt.plot(x,y[0,:])

y[1,:]=Gaussian(x,L/2 + c*dt,5*dx)



"""
#Unmoving delta function
y[0,size/2]=1
y[1,size/2]=1
"""

"""
#Oscillating sine wave with given nodes
mode = 7
y[0,:]=np.sin(mode*sp.pi*x/(size-1))
y[1,:]=.9*y[0,:]
"""

G = np.linalg.inv(K)
for i in range(2,timestep):
    y[i,:]=np.dot(G,2*y[i-1,:]-y[i-2,:])

#plottimes(20)
leg = []
for i in range(1,7):
        plt.plot(x,y[i/8.*timestep,:])
        leg.append('t = ' + str(i))
#plt.plot(x,y[0,:])
#plt.plot(x,y[5,:])
plt.legend(leg)
plt.show()


"""
def plotmovie():
    for i in range(Time):
        plt.clf()
        plt.plot(x,y[i,:])
        plt.axis([0,size,0,1])
        name = "Heatrand/"+str('%03d' % i)+".png"
        plt.savefig(name)
"""


