---
author: philzook58
comments: true
date: 2016-01-10 18:54:44+00:00
layout: post
link: https://www.philipzucker.com/?p=367
published: false
slug: Python Relativity
title: Python Relativity
wordpress_id: 367
---

Sometimes you have x(t) and want to convert to using proper time. It's easy, except that you have to do an integral.

$latex d\tau/dt = \sqrt{1- (dx/dt)^2}$

Used some nice built-ins of scipy

    
    import numpy as np
    from scipy import integrate
    from scipy import interpolate
    from scipy.interpolate import UnivariateSpline
    import matplotlib.pyplot as plt
    
    
    N=100
    v = .5
    
    t = np.linspace(0,50,N)
    x = t * v
    y = np.zeros(N)
    z = np.zeros(N)
    
    #find splines
    xs = UnivariateSpline(t, x, s=1)
    ys = UnivariateSpline(t, y, s=1)
    zs = UnivariateSpline(t, z, s=1)
    
    dxdt = xs.derivative()(t)
    dydt = ys.derivative()(t)
    dzdt = zs.derivative()(t)
    
    gamma = np.sqrt(1 - dxdt**2 - dydt**2 - dzdt**2)
    
    tau = integrate.cumtrapz(gamma, t)
    tau = np.insert(tau,0,0.)
    
    plt.figure()
    plt.plot(t,tau)
    plt.figure()
    plt.plot(t,x)
    plt.show()
    


The splines let us interpolate between values. Also hypothetically, maybe computing better finite differences than the naive approach.




