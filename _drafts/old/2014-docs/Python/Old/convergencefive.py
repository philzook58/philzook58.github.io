
import numpy as np
import scipy as sp
import matplotlib.pyplot as plt

G = .5
b = .2
e = .1
eps = 0.01
exp = 5
def func(x):
    return G*(b+e*x**exp)


def converge(x):
    for i in range(30):
        x = func(x)
    z = func(x)
    return abs(x-z) < eps

size = 100
a = -2
b = 2
x = np.linspace(a,b,size)
y = np.linspace(a,b,size)
x1 = []
y1 = []
for i in range(size):
    for n in range(size):
        if converge(x[i]+1.j*y[n]):
            x1.append(x[i])
            y1.append(y[n])

plt.scatter(x1,y1)
plt.show()
