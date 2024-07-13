import matplotlib.pyplot as plt
import scipy as sp
import numpy as np
import scipy.linalg as linalg
import scipy.integrate as integ
import Matlib



N=50

dx = 1
L = dx * N
hbar = 1
m = 1

K0 = hbar**2 /2 / m * Matlib.K(N)
I = np.identity(N)
K = np.kron(K0,np.kron(I,I)) + np.kron(I,np.kron(K0,I)) + np.kron(I,np.kron(I,K0))

x = np.linspace(-L/2,L/2,num=N)
y = np.linspace(-L/2,L/2,num=N)
z = np.linspace(-L/2,L/2,num=N)
xx, yy, zz= np.meshgrid(x, y, z)


V =

H = K + V

linalg.eigsomething
