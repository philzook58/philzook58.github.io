import numpy as np
import matplotlib.pyplot as plt
import scipy as sp
import scipy.integrate as integrate
import scipy.special as special


terms = 20
def f(x):
    return x

jzeros = special.jn_zeros(0,terms)

def coeffintegrand(x,n):
    return x * special.jn(0,x*jzeros[n] ) * f(x)

def normint(x,n):
    return x * special.jn(0,x* jzeros[n])**2
print normint(2,2)
    
coeff = np.zeros(terms)

for i in range(terms):
    coeff[i] = integrate.quad(coeffintegrand,0,1,args=(i))[0]/ integrate.quad(normint,0,1,args=(i))[0]

def evalsum(coeffic,x):
    y = np.zeros(len(x))
    for i in range(terms):
        y = y + coeffic[i]*special.jn(0 , x * jzeros[i])
    return y


x = np.linspace(0.,10.,100)


plt.plot(x,evalsum(coeff,x))
plt.show()




