import numpy as np
import scipy as sp
import matplotlib.pyplot as plt
from scipy import interpolate

#Grid Size
size = 25
a = 0
b = sp.pi
x = np.linspace(a,b,size)
Time = 10
timesteps = 40
dt = Time/timesteps
dx = (b-a)/size
c2 = 1#wave speed squared
p = 1
K = np.tri(size,k=1)-np.tri(size,k=-2)-3*np.identity(size)

K = K/dx**2

K = K*c2*dt**2 + 2*np.identity(size) #Prepares matrix of wave equation

K[0,0]=1
K[0,1]=0
K[1,0]=0

K[size-1,size-1]=1
K[size-1,size-2]=0
K[size-2,size-1]=0

def deriv(xvalue,y):
        yspline = interpolate.splrep(x,y,s=0) #creates spline of y
        return interpolate.splev(xvalue,yspline,der=1)
    
def plottimes(n):
    for i in range(1,n):
        plt.plot(x,y[Time/i-1,:])
        
print K

#x= np.arange(size)
y = np.zeros((timesteps,size))

a = np.zeros(timesteps) #position of particle at each time
#Particle initial conditions
a[0]=size/2+3
a[1]=size/2+3
 #moving delta function
y[0,size/2]=1
y[1,size/2+1]=1
"""
mode = 1
y[0,:]=np.sin(mode*sp.pi*x/(size-1))
y[1,:]=.9*y[0,:]
"""
g=1
for i in range(2,timesteps):
    y[i,:]=np.dot(K,y[i-1,:])-y[i-2,:] #d^2y/Dx^2*c^2*dt^2 + 2Y(t)- y(t-1)
    derivxa1 = deriv(a[i-1],y[i-1,:]) #y[i-1,int(a[i-1]-1)]- y[i-1,int(a[i-1]+1)]
    derivxa2 =  deriv(a[i-2],y[i-2,:]) #y[i-2,int(a[i-2]-1)]- y[i-2,int(a[i-2]+1)]
    a[i]=2*a[i-1]-a[i-2]-g*derivxa1 + (derivxa1-derivxa2)
    
print a

#plottimes(20)
for i in range(timesteps):
        plt.plot(x,y[i-1,:])
        plt.plot(a[i-1],y[i-1,int(a[i-1])],'bo')
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
    for i in range(timesteps):
        plt.clf()
        plt.plot(x,y[i,:])
        plt.axis([0,size,0,1])
        name = "Heatrand/"+str('%03d' % i)+".png"
        plt.savefig(name)
    


