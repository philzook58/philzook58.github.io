import matplotlib.pyplot as plt
import scipy as sp
import numpy as np
import scipy.linalg as linalg
import scipy.integrate as integ
import Matlib





a = 1. # size of cell
n = 10 #divisions per cell
N=50 #Number of cells)
m = 1

#momentum squared op
P2 = Matlib.C(N*n) / (a/n)**2
#kinetic energy
T =  P2 / 2 / m

#A diffrent way of making a potental
#x = np.linspace(0, N*a,num = N * n)
#Pot = np.sin(x) + np.sin(3*x)

x = np.linspace(0, a,num = n)
Pot = np.zeros(n)
U = -100
#Builds a krmnig pennry type potential
Pot[:n/3] = U
plt.figure(0)
plt.plot(x,Pot)
V = np.kron(np.identity(N),np.diag(Pot))
#V = np.diag(Pot)
plt.figure(1)

H = T + V

#There was interesting talk of sturm sequences as a manner of finding eig dist
#What is a good way of finding?
spectrum = linalg.eigvalsh(H)

plt.hist(spectrum, bins = 100, range = [-100,0])

plt.show()
