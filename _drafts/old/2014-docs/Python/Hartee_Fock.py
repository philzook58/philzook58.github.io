import scipy.special as special
import numpy as np

#array of basis orbital functions
def orbital(x,y,z,n,l,m,Z):
    
    #special.eval_laguerre(n,x)
    alpha = 2*l+1
    L = special.eval_genlaguerre(n,alpha,x)
    r = np.sqrt(x**2+y**2+z**2)
    
    theta = np.arctan(rho/z)
    phi = np.arctan(y/x)
    Y = special.sph_harm(m,n,theta,phi)
    
    return L*Y


basis = 

#Find Matrix Elements
def coulomb(r1, Z1, r2, Z2):
  #  integrate orbital 1 * orbital 2 * coulomb


# overlap integrals
def overlap(r1, Z1, r2, Z2):
    #integrate orbital 1 times orbital 2
    

def kinetic(r1, Z1, r2, Z2):

#Find Kinetic Energy Elements



#Hartree Fock Section
def exchange:


def repulsion:


