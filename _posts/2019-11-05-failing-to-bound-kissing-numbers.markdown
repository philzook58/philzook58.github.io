---
author: philzook58
comments: true
date: 2019-11-05 03:14:49+00:00
layout: post
link: https://www.philipzucker.com/failing-to-bound-kissing-numbers/
slug: failing-to-bound-kissing-numbers
title: Failing to Bound Kissing Numbers
wordpress_id: 2437
categories:
- Formal Methods
- Optimization
tags:
- failure
---




[https://en.wikipedia.org/wiki/Kissing_number](https://en.wikipedia.org/wiki/Kissing_number)







Cody brought up the other day the kissing number problem.Kissing numbers are the number of equal sized spheres you can pack around another one in d dimensions. It's fairly self evident that the number is 2 for 1-d and 6 for 2d but 3d isn't so obvious and in fact puzzled great mathematicians for a while. He was musing that it was interesting that he kissing numbers for some dimensions are not currently known, despite the fact that the first order theory of the real numbers is decidable [https://en.wikipedia.org/wiki/Decidability_of_first-order_theories_of_the_real_numbers](https://en.wikipedia.org/wiki/Decidability_of_first-order_theories_of_the_real_numbers)







I suggested on knee jerk that Sum of Squares  might be useful here. I see inequalities and polynomials and then it is the only game in town that I know anything about.







Apparently that knee jerk was not completely wrong








https://windowsontheory.org/2016/08/27/proofs-beliefs-and-algorithms-through-the-lens-of-sum-of-squares/








[https://arxiv.org/pdf/math/0608426.pdf](https://arxiv.org/pdf/math/0608426.pdf)







Somehow SOS/SDP was used for bounds here. I had an impulse that the problem feels SOS-y but I do not understand their derivation.







One way the problem can be formulated is by finding or proving there is no solution to the following set of equations constraining the centers $ x_i$ of the spheres. Set the central sphere at (0,0,0,...) . Make the radii 1. Then$ \forall i. \|x_i\|^2 = 2^2 $ and $ \forall i j.  \|x_i - x_j\|^2 \ge 2^2 $







I tried a couple different things and have basically failed. I hope maybe I'll someday have a follow up post where I do better.







So I had 1 idea on how to approach this via a convex relaxation







Make a vector $ x = \begin{bmatrix} x_0 & y _0 & x_1 & y _1 & x_2 & y _2 & ... \end{bmatrix}$ Take the outer product of this vector $ x^T x = X$ Then we can write the above equations as linear equalities and inequalities on X. If we forget that we need X to be the outer product of x (the relaxation step), this becomes a semidefinite program. Fingers crossed, maybe the solution comes back as a rank 1 matrix. Other fingers crossed, maybe the solution comes back and says it's infeasible. In either case, we have solved our original problem.






    
    
```python

import numpy as np
import cvxpy as cvx


d = 2
n = 6
N = d * n 
x = cvx.Variable((N+1,N+1), symmetric=True)
c = []
c += [x >> 0]
c += [x[0,0] == 1]
# x^2 + y^2 + z^2 + ... == 2^2 constraint
x1 = x[1:,1:]
for i in range(n):
    q = 0
    for j in range(d):
        q += x1[d*i + j, d*i + j]
    c += [q == 4] #[ x1[2*i + 1, 2*i + 1] + x[2*i + 2, 2*i + 2] == 4]

#c += [x1[0,0] == 2, x1[1,1] >= 0]
#c += [x1[2,2] >= 2]

# (x - x) + (y - y) >= 4
for i in range(n):    
    for k in range(i):
        q = 0
        for j in range(d):
            q += x1[d*i + j, d*i + j] + x1[d*k + j, d*k + j] - 2 * x1[d*i + j, d*k + j] # xk ^ 2 - 2 * xk * xi 
        c += [q >= 4]
print(c)
obj = cvx.Maximize(cvx.trace(np.random.rand(N+1,N+1) @ x ))
prob = cvx.Problem(obj, c)
print(prob.solve(verbose=True))
u, s, vh = np.linalg.svd(x.value)
print(s)

import matplotlib.pyplot as plt
xy = vh[0,1:].reshape(-1,2)
print(xy)
plt.scatter(xy[0], xy[1] )
plt.show()
```








Didn't work though. Sigh. It's conceivable we might do better if we start packing higher powers into x? 







Ok Round 2. Let's just ask z3 and see what it does. I'd trust z3 with my baby's soft spot.







It solves for 5 and below. Z3 grinds to a halt on N=6 and above. It ran for days doin nothing on my desktop. 






    
    
```python

from z3 import *
import numpy as np

d = 2 # dimensions
n = 6 # number oif spheres

x = np.array([ [ Real("x_%d_%d" % (i,j))     for j in range(d) ] for i in range(n)])
print(x)

c = []
ds = np.sum(x**2, axis=1)
c += [ d2 == 4 for d2 in ds] # centers at distance 2 from origin


ds = np.sum( (x.reshape((-1,1,d)) - x.reshape((1,-1,d)))**2, axis = 2)

c += [ ds[i,j]  >= 4  for i in range(n) for j in range(i)] # spheres greater than dist 2 apart
c += [x[0,0] == 2]
print(c)
print(solve(c))
```








Ok. A different tact. Try to use a [positivstellensatz](https://en.wikipedia.org/wiki/Positivstellensatz) proof. If you have a bunch of polynomial inequalities and equalities if you sum polynomial multiples of these constraints, with the inequalities having sum of square multiples, in such a way to = -1, it shows that there is no real solution to them. We have the distance from origin as equality constraint and distance from each other as an inequality constraint. I intuitively think of the positivstellensatz as deriving an impossibility from false assumptions. You  can't add a bunch of 0 and positive numbers are get a negative number, hence there is no real solution.







I have a small set of helper functions for combining sympy and cvxpy for sum of squares optimization. I keep it here along with some other cute little constructs [https://github.com/philzook58/cvxpy-helpers](https://github.com/philzook58/cvxpy-helpers)






    
    
```python

import cvxpy as cvx
from sympy import *
import random
'''
The idea is to use raw cvxpy and sympy as much as possible for maximum flexibility.

Construct a sum of squares polynomial using sospoly. This returns a variable dictionary mapping sympy variables to cvxpy variables.
You are free to the do polynomial operations (differentiation, integration, algerba) in pure sympy
When you want to express an equality constraint, use poly_eq(), which takes the vardict and returns a list of cvxpy constraints.
Once the problem is solved, use poly_value to get back the solution polynomials.

That some polynomial is sum of squares can be expressed as the equality with a fresh polynomial that is explicility sum of sqaures.

With the approach, we get the full unbridled power of sympy (including grobner bases!)

I prefer manually controlling the vardict to having it auto controlled by a class, just as a I prefer manually controlling my constraint sets
Classes suck.
'''


def cvxify(expr, cvxdict): # replaces sympy variables with cvx variables in sympy expr
     return lambdify(tuple(cvxdict.keys()), expr)(*cvxdict.values()) 

def sospoly(terms, name=None):
    ''' returns sum of squares polynomial using terms, and vardict mapping to cvxpy variables '''
    if name == None:
        name = str(random.getrandbits(32))
    N = len(terms)
    xn = Matrix(terms)
    Q = MatrixSymbol(name, N,N)
    p = (xn.T * Matrix(Q) * xn)[0]
    Qcvx = cvx.Variable((N,N), PSD=True)
    vardict = {Q : Qcvx} 
    return p, vardict



def polyvar(terms,name=None):
    ''' builds sumpy expression and vardict for an unknown linear combination of the terms '''
    if name == None:
        name = str(random.getrandbits(32))
    N = len(terms)
    xn = Matrix(terms)
    Q = MatrixSymbol(name, N, 1)
    p = (xn.T * Matrix(Q))[0]
    Qcvx = cvx.Variable((N,1))
    vardict = {Q : Qcvx} 
    return p, vardict

def scalarvar(name=None):
    return polyvar([1], name)

def worker(x ):
    (expr,vardict) = x
    return cvxify(expr, vardict) == 0
def poly_eq(p1, p2 , vardict):
    ''' returns a list of cvxpy constraints '''
    dp = p1 - p2
    polyvars = list(dp.free_symbols - set(vardict.keys()))
    print("hey")
    p, opt = poly_from_expr(dp, gens = polyvars, domain = polys.domains.EX) #This is brutalizing me
    print(opt)
    print("buddo")
    return [ cvxify(expr, vardict) == 0 for expr in p.coeffs()]
    '''
    import multiprocessing
    import itertools
    pool = multiprocessing.Pool()

    return pool.imap_unordered(worker, zip(p.coeffs(),  itertools.repeat(vardict)))
    '''

def vardict_value(vardict):
    ''' evaluate numerical values of vardict '''
    return {k : v.value for (k, v) in vardict.items()}

def poly_value(p1, vardict):
    ''' evaluate polynomial expressions with vardict'''
    return cvxify(p1, vardict_value(vardict))

if __name__ == "__main__":
    x = symbols('x')
    terms = [1, x, x**2]
    #p, cdict = polyvar(terms)
    p, cdict = sospoly(terms)
    c = poly_eq(p, (1 + x)**2 , cdict)
    print(c)
    prob = cvx.Problem(cvx.Minimize(1), c)
    prob.solve()

    print(factor(poly_value(p, cdict)))

    # global poly minimization
    vdict = {}
    t, d = polyvar([1], name='t')
    vdict.update(d)

    p, d = sospoly([1,x,x**2], name='p')
    vdict.update(d)
    constraints = poly_eq(7 + x**2 - t, p, vdict)
    obj = cvx.Maximize( cvxify(t,vdict) )
    prob = cvx.Problem(obj, constraints)
    prob.solve()
    print(poly_value(t,vdict))

```








and here is the attempted positivstellensatz.






    
    
```python

import sos
import cvxpy as cvx
from sympy import *
import numpy as np

d = 2
N = 7

# a grid of a vector field. indices = (xposition, yposition, vector component)
'''xs = [ [symbols("x_%d_%d" % (i,j)) for j in range(d)] for i in range(N) ]
gens = [x for l in xs for x in l ]
xs = np.array([[poly(x,gens=gens, domain=polys.domains.EX) for x in l] for l in xs])
'''
xs = np.array([ [symbols("x_%d_%d" % (i,j)) for j in range(d)] for i in range(N) ])

c1 = np.sum( xs * xs, axis=1) - 1
c2 = np.sum((xs.reshape(-1,1,d) - xs.reshape(1,-1,d))**2 , axis=2) - 1

print(c1)
print(c2)
terms0 = [1]
terms1 = terms0 + list(xs.flatten())
terms2 = [ terms1[i]*terms1[j] for j in range(N+1) for i in range(j+1)]
#print(terms1)
#print(terms2)
vdict = {}
psatz = 0
for c in c1:
    lam, d = sos.polyvar(terms2)
    vdict.update(d)
    psatz += lam*c
for i in range(N):
    for j in range(i):
        c = c2[i,j]
        lam, d = sos.sospoly(terms2)
        vdict.update(d)
        psatz += lam*c
#print(type(psatz))
print("build constraints")
constraints = sos.poly_eq(psatz, -1, vdict)
#print("Constraints: ", len(constraints))
obj = cvx.Minimize(1) #sum([cvx.sum(v) for v in vdict.values()]))
print("build prob")
prob = cvx.Problem(obj, constraints)
print("solve")
prob.solve(verbose=True, solver= cvx.SCS)
```








It worked in 1-d, but did not work in 2d. At order 3 polynomials N=7, I maxed out my ram.







I also tried doing it in Julia, since sympy was killing me. Julia already has a SOS package






    
    
```julia

using JuMP
using SumOfSquares
using DynamicPolynomials
using SCS
N = 10
d = 2
@polyvar x[1:N,1:d]
X = monomials(reshape(x,d*N), 0:2)
X1 = monomials(reshape(x,d*N), 0:4)

model = SOSModel(with_optimizer(SCS.Optimizer))

acc = nothing
for t in sum(x .* x, dims=2)
    #print(t)
    p = @variable(model, [1:1], Poly(X1))
    #print(p)
    if acc != nothing
        acc += p * (t - 1)
    else
        acc = p * (t - 1)
    end
end

for i in range(1,stop=N)
    for j in range(1,stop=i-1)
        d  = x[i,:] - x[j,:]
        p = @variable(model, [1:1], SOSPoly(X))
        acc += p * (sum(d .* d) - 1)
    end
end

#print(acc)
print(typeof(acc))
@constraint(model, acc[1] == -1 )
optimize!(model)
```








It was faster to encode, but it's using the same solver (SCS), so basically the same thing.







I should probably be reducing the system with respect to equality constraints since they're already in a Groebner basis. I know that can be really important for reducing the size of your problem







I dunno. 













Blah blah blah blah A bunch of unedited trash







[https://github.com/peterwittek/ncpol2sdpa](https://github.com/peterwittek/ncpol2sdpa) Peter Wittek has probably died in an avalanche? That is very sad.







These notes







[https://web.stanford.edu/class/ee364b/lectures/sos_slides.pdf](https://web.stanford.edu/class/ee364b/lectures/sos_slides.pdf)







Positivstullensatz. 







kissing number







Review of sum of squares







minimimum sample as LP. ridiculous problem  
min t  
st. f(x_i) - t >= 0







dual -> one dual variable per sample point  
The only dual that will be non zero is that actually selecting the minimum.







Hm. Yeah, that's a decent analogy.







How does the dual even have a chance of knowing about poly airhtmetic?  
It must be during the SOS conversion prcoess. In building the SOS constraints,  
we build a finite, limittted version of polynomial multiplication  
x as a matrix. x is a shift matrix.  
In prpducing the characterstic polynomial, x is a shift matrix, with the last line using the polynomial  
known to be zero to   
eigenvectors of this matrix are zeros of the poly.







SOS does not really on polynomials persay. It relies on closure of the suqaring operaiton







maybe set one sphere just at x=0 y = 2. That breaks some symmettry







set next sphere in plane something. random plane through origin?







order y components - breaks some of permutation symmettry.







no, why not order in a random direction. That seems better for symmettry breaking



