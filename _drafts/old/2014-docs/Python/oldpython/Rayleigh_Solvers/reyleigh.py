import numpy as np
import scipy as sp
import matplotlib.pyplot as plt
dx = 0.5
x = np.arange(0,10,dx)
print x
y = np.sin(3.14/10*x)
y[0]=0
y[9]=0
print y
#plt.plot(x,y)
#plt.show()
z = np.zeros(10/dx)
def forwderiv(y):
    for i in range(1,len(y)-1):
        z[i] = (y[i+1]-y[i])/dx
    return z

def backderiv(y):
    for i in range(1,len(y)-1):
        z[i] = (y[i]-y[i-1])/dx
    return z
                   
def rayleigh(q):
    norm = dx * np.dot(q,q)
    print norm
    oneder = forwderiv(q)
    print oneder
    twoder = backderiv(oneder)
    print twoder
    grad = (twoder/norm - 2.*q*np.dot(oneder,oneder)*dx/norm/norm)
    print grad
    return q - grad

sol1 = rayleigh(y)
sol2 = rayleigh(sol1)
for i in range(0,10):
    sol2 = rayleigh(sol2)
    plt.plot(x,sol2)

#sol3 = rayleigh(sol2)
plt.plot(x,sol1)
plt.plot(x,sol2)
#plt.plot(x,sol3)
plt.show()
