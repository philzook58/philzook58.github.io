import numpy as np
import scipy as sp
import matplotlib.pyplot as plt

c = 0.360284+.100376j
iterate = 60
res =300
"""
def func(y,c):
    return y**2+c
#    return (2*y)%1 #Goes way wrong
"""



for real in np.linspace(-1,1,res):
    for imag in np.linspace(-1,1,res):
        y = real + imag * 1j
        for i in range(iterate): #initialize to asymtpotics
            y = y**2 + c
        if y < abs(c):
            plt.scatter(real,imag,s=.3,marker=',')
        

plt.show()
