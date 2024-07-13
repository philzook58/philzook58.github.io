import matplotlib.pyplot as plt
import scipy as sp
import numpy as np
import scipy.linalg as linalg
#import scipy.integrate as integ
import Matlib


#Do 2d wave equation
#2d laplace
#compare to 


Nx = 25
Nt = 25

a = .1
tau = .1

"""
L=20
T=20
Nx = int(L/a)
Ny = int(T/tau)
"""

Lx = Matlib.C(Nx)/a**2
Lt = Matlib.R(Nt)/tau**2
Ix = np.eye(Nx)
It = np.eye(Nt)
#print Lx
L = np.kron(Lx,It) - np.kron(Ix,Lt) + 0.00001j * np.kron(Ix,It)
#print L
jx = np.zeros(Nx)
jx[Nx/2]=1
jt = np.zeros(Nt)
jt[Nt/2]=1

j = np.kron(jx,jt)
#print j
phi = linalg.solve(L,j)
#print phi
phi2 = np.reshape(phi, (Nx,Nt))
plt.imshow(np.abs(phi2))
#plt.figure(2)
#plt.plot(phi2[Nx/2,:])
plt.show()

