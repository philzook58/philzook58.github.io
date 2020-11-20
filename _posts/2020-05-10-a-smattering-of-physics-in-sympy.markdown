---
author: philzook58
comments: true
date: 2020-05-10 00:08:36+00:00
layout: post
link: https://www.philipzucker.com/a-smattering-of-physics-in-sympy/
slug: a-smattering-of-physics-in-sympy
title: A Smattering of Physics in Sympy
wordpress_id: 2788
categories:
- Physics
tags:
- python
- sympy
---




Sympy is fun. I've been enjoying trying out some simple physics problems and seeing what kind of fun angles sympy brings to the table. It does pretty good on concrete problems, not so good at abstract derivations.







### Kinematics







Ah such fond memories! In high school, I was taught by Ric Thompson "the big four". 







$latex x_f = x_i + v_i t + \frac{1}{2} a t^2$







$latex v_f = v_i + a t$







$latex v_f^2 = v_i^2 + 2 a d$







$latex  d = \frac{v_f + v_i}{2} t $







The equations are of course, overcomplete. They are all implied by $latex \frac{d^2}{dt^2}x = a$, but even with only algebra then second two are derivable from the first two.







Of course a natural way of  deriving the equations is to solve one equation for a variable and substitute it into the other equation. sympy makes this pretty dang easy.






    
    <code>from sympy import *
    init_printing()
    t,a,d,vf,vi = symbols("t a d vf vi")
    e1 = Eq(d , vi * t + 1/2 * a * t ** 2)
    tsub = solve(Eq(vf , vi + a * t),t)[0]
    print(tsub) # This is assuming a is nonzero though.
    expand(simplify(e1.subs(t,tsub)))</code>






    
    <code>(vf - vi)/a
    Eq(d, 0.5*vf**2/a - 0.5*vi**2/a)</code>







However, there is a more automated approach. 







It turns out that a decent chunk of physics equations are or can be well approximated by a system of polynomial equations. There are systematic methods that are guaranteed to solve the problem (albeit maybe not in the lifetime of the universe).







A grobner basis is an equivalent set of polynomial equations that has useful properties. For some simple purposes, all you need to know is that if you give the variables you want to eliminate first, the Groebner basis will contain equations without those variable. Here we specify t as one to eliminate, so we get an equation without t in it






    
    <code>
    G = groebner(  [vi * t + 1/2 * a * t ** 2 - d,  
                    vi + a * t - vf] , 
                     t,vf,d,a,vi  )
    for e in G:
        print(e)</code>






    
    <code>-2.0*d + 1.0*t*vf + 1.0*t*vi
    1.0*a*t - 1.0*vf + 1.0*vi
    -2.0*a*d + 1.0*vf**2 - 1.0*vi**2</code>







I've actually been pleasantly surprised at how many physics problems reduce ultimately to systems of polynomial constraints. Energy and momentum conservation are polynomial constraints (classical feynman diagrams kind of). Special relativity questions can be reduced to polynomial constraints using the proper time.






    
    <code>#elephant problem
    # elephants give birth at 21 months. On a rocket at velocity v
    # how long T until you see it give birth? 
    tau , t1, t2, x1, v, c, T = symbols("tau t1 t2 c1 v c T")
    
    eqs = [
        tau**2 - (t1**2 - x1**2 / c**2), # proper time
        x1 - v * t1, # distance away
        c * t2 - x1, # time for light to travel back
        T - t1 - t2, # total time
        tau - 21 # proper time is 21 months
        
    ]
    
    groebner(eqs, tau , t1, t2, x1, v, T)</code>







### Lagrangian Mechanics







The Structure and Interpretation of Classical Mechanics is an [interesting book](https://groups.csail.mit.edu/mac/users/gjs/6946/sicm-html/book-Z-H-3.html#%_toc_start). 







It points out that notation we use is extremely imprecise and implicit. This is a source of great confusion.







A great benefit of programming up such examples is that it makes explicit (sometimes painfully so) steps that were implicit before.







In the Euler Lagrange equation, first partially differentiates considering q and $latex \dot{q}$ to be independent parameters. Then a substitution is makde for a function $latex x(t)$ and then we procede with a differentiation with respect to time.






    
    <code># simple harmonic oscillator lagrangian style
    m, k = symbols("m k", real = True, positive=True)
    v, q = symbols("v q")
    K = Rational(1,2) * m * v ** 2 #kinetic energy
    V = Rational(1,2) * k * q ** 2 # potential energy
    L =  K - V  #Lagrangian
    F = diff(L,q) # force
    p = diff(L,v) # momentum
    
    x_ = Function("x")
    t = symbols("t")
    
    x = x_(t)
    
    subst = { v : diff(x,t),
             q : x} # replacement to turn q into a function x
    
    # euler-lagrange equations of motion
    eq = F.subs( subst ) - diff( p.subs(subst)  , t )
    dsolve(eq) # general solution cosine and sines</code>







Here's an analogous thing for a pendulum 






    
    <code>#simple harmonic oscillator lagrangian style
    m, g, L = symbols("m g L", real = True, positive=True)
    theta, w = symbols("theta omega")
    K = Rational(1,2) * m * (w * L) ** 2 #kinetic energy
    V = - Rational(1,2) * m * g * L * cos(theta) # potential energy. angle is defined as 0 = hanging down
    L =  K - V  #Lagrangian
    F = diff(L,theta) # force
    p = diff(L,w) # momentum
    F
    p
    
    x_ = Function("theta")
    t = symbols("t")
    
    x = x_(t)
    
    subst = { w : diff(x,t),
             theta : x} # replacement to turn q into a function x
    
    # euler-lagrange equations of motion
    eq = F.subs( subst ) - diff( p.subs(subst)  , t )
    eq
    #dsolve(eq) </code>







Another place where an implicit stated substitution is absolutely vital is in the Legendre transform going from the Lagrangian to the Hamiltonian.






    
    <code># legendre transformation to hamiltonian
    p = symbols( "p" )
    H_ = p * v - L # hamiltonian but we haven't solved out v yet
    v_of_pq = solve(diff(H_, v), v)[0] # set derivative to 0 to solve for v.
    H = simplify(H_.subs(v, v_of_pq )) # substitue back in. Here is the actual hamiltonian
    H</code>







#### Statistical Mechanics







Sympy can do Gaussian integrals! How convenient. It can also do power series expansions. And differentiate. So it takes the drudgery out of some simple calculations






    
    <code># ideal gas partition function
    beta, m, V, N, kb, T  = symbols("beta m V N k_b T", real=True, positive=True)
    p = symbols("p", real=True)
    Z = integrate( exp( - beta * Rational(1,2) * p ** 2 / m ), (p,-oo,oo))**(3*N) * V**N #partition function
    def avg_energy(Z):
        return - diff(ln(Z), beta).subs(beta, 1/ kb / T)
    print(avg_energy(Z)) #
    F = (-ln(Z) / beta).subs(beta, 1 / kb / T) #helmholtz free energy
    S = diff(F , T) # sentropy is derivative of helmholtz wrt T
    S # the functional dependence on T and V I think is correct
    P = -diff(F , V) # pressure is - derivative of V
    P
    # Neato</code>






    
    <code># hamrmonic oscillator partition function
    beta, m, k = symbols("beta m k ", real=True, positive=True)
    p, x = symbols("p x", real=True)
    E = R(1,2) * p ** 2 / m  + R(1,2) * k * x ** 2
    Z = integrate( integrate( exp( - beta * E ), (p,-oo,oo)) , (x,-oo, oo))**N 
    diff(-ln(Z),beta)</code>







Perturbation theory of the partition function of an anharmonic oscillator. Pretty easy. It is interesting to note that this is the very simplest schematic of how perturbation theory can be approached for quantum field theory.






    
    <code># pertubration theory of anharmonic oscillator
    beta, m, k, g = symbols("beta m k g ", real=True, positive=True)
    p, x = symbols("p x", real=True)
    E = Rational(1,2) * ( p ** 2 / m  +  k * x ** 2) + g * x ** 4
    series(exp( - beta * E ), g).removeO()
    Z = integrate( integrate( series(exp( - beta * E ), g, n=2).removeO(), (p,-oo,oo)) , (x,-oo, oo))
    simplify(diff(-ln(Z),beta)) #E
    simplify(diff(-ln(Z),k)/beta) #<x**> </code>







Other things that might be interesing : 2 oscillators, A chain of oscillators, virial expansion







#### Thermo and Legendre Tranformations







Thermodynamics is a poorly communicated topic. Which variables remain in expressions and what things are held constant when differentiating are crucial and yet poorly communicated and the notation is trash. Sympy helps make some things explicit. It's fun.  






    
    <code>u,s,t,p,v,n,r = symbols("u s t p v n r")
    
    du,ds,dt,dp,dv = symbols("du ds dt dp dv")
    # taylor series in stuff?
    
    e1 = p * v - n * r * t
    e2 = u - Rational(3 , 2) * n * r * t
    
    state = [  (u,du), (s,ds), (t,dt) , (p,dp) , (v,dv) ]
    
    def differential(e):
        return sum( [ diff(e,x) * dx  for x,dx in state]   )
    
    
    de1 = differential(e1 )
    de2 = differential(e2 )
    
    e3 = du - (t * ds - p * dv)
    
    eqs = [e1,e2,de1,de2,e3]
    print(eqs)
    G = groebner( eqs, u , du,  t, dt, p, dp, v, dv,  ds )
    for e in G:
        print(e)</code>






    
    <code>R = Rational
    U,S,T,P,V,N, k = symbols("U S T P V N k")
    
    cv = R(3,2) * N * k
    e1 = U - cv * T
    e2 = P * V - N * k * T
    e3 = S - cv * ln(T) + N * k * ln(V)
    
    elim = [P,T]
    Ps = solve([e1,e2,e3], P)
    Ps
    es = [ e.subs(Ps) for e in [e1,e2,e3] ]
    Ts = solve(e3, T)[0]
    es = [  e.subs(T,Ts) for e in es ]
    Usv = solve(es[0],U)[0]
    psv = diff(Usv,V)
    tsv = diff( Usv , S )
    
    #solve(es[0], V)
    
    Hsv = Usv + P * V  # enthalpy and legendre trnasformation
    Vps = solve(diff(Hsv, V) , V) 
    H =  Hsv.subs(V, Vps[0]) 
    simplify(H)</code>







There are so many other things!







What about a Van Der Waals equation? Optics (geometrical and wave, paraxial ~ Schrodinger, fourier optics), GR (exterior derivatives ) , Quantum (wave matching problems. What can we do about hydrogen? WKB, QHE) rutherford scattering, Weiss mean field, canonical transformations,  Rotations. Clebsh-Gordon coefficients



