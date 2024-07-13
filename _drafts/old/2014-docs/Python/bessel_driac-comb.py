import numpy as np
import matplotlib.pyplot as plt
import scipy as sp
import scipy.integrate as integrate
import scipy.special as special

#Ridiculuos hypthesis, use -1 1 interval and use both sets of zeros.
pos =0.2
terms = 50
def f(x):
    return 1

jzeros = special.jn_zeros(0,terms)

#def coeffintegrand(x,n):
    
    #return x * special.jn(0,x*jzeros[n] ) * f(x)

def normint(x,n):
    return x * special.jn(0,x* jzeros[n])**2

    
coeff = np.zeros(terms)

for i in range(terms):
    #coeff[i] = integrate.quad(coeffintegrand,0,1,args=(i))[0]/ integrate.quad(normint,0,1,args=(i))[0]
    coeff[i] = pos * special.jn(0,pos*jzeros[i] )/ integrate.quad(normint,0,1,args=(i))[0]

def evalsum(coeffic,x):
    y = np.zeros(len(x))
    for i in range(terms):
        y = y + coeffic[i]*special.jn(0 , x * jzeros[i])
    return y


x = np.linspace(0,30,1000)


plt.plot(x,evalsum(coeff,x))
plt.plot(x,20*special.jn(0,x* jzeros[0]))
#plt.plot(x,20*special.jn(0,x))
plt.show()




