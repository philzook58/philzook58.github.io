import numpy as np
import scipy as sp
import matplotlib.pyplot as plt
import Matlib

size = 500
L = 1. #Total x length
dx = L/size

timestep = 1500
Time = 1.
dt = Time/timestep
c = 1 #c, speed of wave
c2 = c**2

#Dx2 = Matlib.C(size)
Dx = c * Matlib.Dc(size) / dx

def Parityflip(u):
    return u[::-1]

def Gaussian(x,b,sigma):
    return np.exp(-((x-b)/sigma)**2)

def plottimes(n):
    for i in range(1,n):
        plt.plot(x,y[timestep/i-1,:])

G = np.linalg.inv(np.eye(size)+dt*Dx)
x= np.linspace(0,L,size)
y = np.zeros((timestep,size))

y[0,:]=Gaussian(x,L/2,10*dx)



for i in range(1,timestep):
    y[i,:]=np.dot(G,y[i-1,:])

leg = []
for i in range(0,7):
        plt.plot(x,y[i/8.*timestep,:])
        leg.append('t = ' + str(i))
#plt.plot(x,y[0,:])
#plt.plot(x,y[5,:])
plt.legend(leg)
plt.show()
    
#I should propagate the deriviative field, not the field itself. integrate
#if inclinded. the derivative field is the electron denisty btw

