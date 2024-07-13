import matplotlib.pyplot as plt
import scipy as sp
import numpy as np
import scipy.linalg as linalg
import scipy.integrate as integ




mu = 7

def deriv(x,t):
    y = x[0]
    v = x[1]
    a = -y + mu*(1-y*y)*v
    return np.array([v,a])
    

x0 = np.array([1.0,0])

time = np.linspace(0,100.0, 1000)

x = integ.odeint(deriv,x0,time)









#plt.plot(time,x)
plt.figure()
plt.plot(x[:,0],x[:,1])
#print x[0,:]
plt.show()
