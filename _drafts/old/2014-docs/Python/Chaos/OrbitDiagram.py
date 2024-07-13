import numpy as np
import scipy as sp
import matplotlib.pyplot as plt


min_c = -2
max_c = 0.25
cgrid = 300
points = 100

"""
def func(y,c):
    return y**2+c
#    return (2*y)%1 #Goes way wrong
"""


c = np.linspace(min_c,max_c,num=cgrid,endpoint=False)
y = np.zeros(cgrid)

for i in range(100): #initialize to asymtpotics
    y = y**2 + c
for i in range (points):
    y = y**2 + c
    plt.scatter(c,y,s=.1,marker=',')

plt.show()
