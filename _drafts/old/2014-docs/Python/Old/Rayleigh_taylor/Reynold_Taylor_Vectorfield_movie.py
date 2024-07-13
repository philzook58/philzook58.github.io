import numpy as np
import scipy as sp
import matplotlib.pyplot as plt

h1 = 1
h2 = 1
k = 1.
xres=20
zres=20
time = 100
w = 0.05
for t in range(time):

    X2,Z2 = np.meshgrid(np.linspace(0,4*sp.pi/k,xres), np.linspace(-h2,0,int(zres*h2/(h1+h2))))
    X1,Z1 = np.meshgrid(np.linspace(0,4*sp.pi/k,xres), np.linspace(0,h1,int(zres*h1/(h1+h2))))

    vx1 = -k / np.sinh(-k*h1) * np.sin(k*X1 - w*t)*np.cosh(k*(Z1-h1))
    vz1 = k / np.sinh(-k*h1) * np.cos(k*X1 - w*t)*np.sinh(k*(Z1-h1))
    vx2 = k / np.sinh(k*h2) * np.sin(k*X2-w*t)*np.cosh(k*(Z2+h2))
    vz2 = k / np.sinh(k*h2) * np.cos(k*X2-w*t)*np.sinh(k*(Z2+h2))

    plt.clf()
    plt.quiver(X1,Z1,vx1,vz1,pivot='mid',color='r')
    plt.quiver(X2,Z2,vx2,vz2,pivot='mid',color='b')
    name = "movie/"+str('%03d' % t)+".png"
    plt.savefig(name)

    #plt.show()
