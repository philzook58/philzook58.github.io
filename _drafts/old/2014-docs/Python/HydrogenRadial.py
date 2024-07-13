import matplotlib.pyplot as plt
import scipy as sp
import numpy as np
import scipy.linalg as linalg
import scipy.integrate as integ
import Matlib


N=50

a = 5.29e-11
dx = 4 a / N
L = dx * N
hbar = 1.05457e-34 #6.582e-16 #eV s  1.05457e-34 Js
m =  9.11e-31 #0.510998e6
q = 1.602e-19
k = 8.987e9

K = hbar**2 /2 / m / dx**2  * Matlib.K(N)

r = np.linspace(0,L/2,num=N)

V0 = hbar**2*l(l+1)/r**2 - q**2 / r
V[0]=0

V = np.diag(V0)

H = K + V

energy = linalg.eigvalsh(H)

print "Hydrogren Ground State Energy:"
print(energy[0] + "eV")
