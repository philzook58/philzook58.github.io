---
author: philzook58
comments: true
date: 2018-04-09 02:37:52+00:00
layout: post
link: https://www.philipzucker.com/cartpole-workin-boyeee/
slug: cartpole-workin-boyeee
title: CartPole WORKIN' BOYEEE
wordpress_id: 1035
tags:
- cartpole
- control
- lqr
---

We have been fighting a problem for weeks. The Serial port was just not reliable, it had sporadic. The problem ended up being a surprising thing, we were using threading to receive the messages nd checking for limit switches. It is not entirely clear why but this was totally screwing up the serial port update in an unpredictable manner. Yikes. What a disaster.

After that though smoooooooth sailing.

With a slight adaptation of the previous Openai gym LQR cartpole code and a little fiddling with parameters we have a VERY stable balancer. We removed the back reaction of the pole dynamics on the cart itself for simplicity. This should be accurate when the pole vastly.

We did find that the motor is exactly velocity control in steady state with a linear response. There is a zero point offset (you need to ask for 100 out of 2046 before you get any movement at all).

We'll see where we can get with the Lyapunov control next time.



[https://github.com/philzook58/cart_pole/commit/ca4aabb86eca54c5a9c7884ad25fafdec4d545ce](https://github.com/philzook58/cart_pole/commit/ca4aabb86eca54c5a9c7884ad25fafdec4d545ce)

[https://github.com/philzook58/cart_pole/blob/master/lqr_controller.py](https://github.com/philzook58/cart_pole/blob/master/lqr_controller.py)

    
    from sabretooth_command import CartCommand
    from cart_controller import CartController
    from encoder_analyzer import EncoderAnalyzer
    import time
    import numpy as np
    import serial.tools.list_ports
    import scipy.linalg as linalg
    lqr = linalg.solve_continuous_are
    
    
    ports = list(serial.tools.list_ports.comports())
    print(dir(ports))
    for p in ports:
        print(dir(p))
        print(p.device)
        if "Sabertooth" in p.description:
           sabreport = p.device
        else:
           ardPort = p.device
    
    print("Initilizing Commander")
    comm = CartCommand(port= sabreport) #"/dev/ttyACM1")
    print("Initilizing Analyzer")
    analyzer = EncoderAnalyzer(port=ardPort) #"/dev/ttyACM0")
    print("Initializing Controller.")
    cart = CartController(comm, analyzer)
    print("Starting Zero Routine")
    cart.zeroAnalyzer()
    
    gravity = 9.8
    mass_pole = 0.1
    length = 0.5
    
    moment_of_inertia = (1./3.) * mass_pole * length**2
    print(moment_of_inertia)
    
    A = np.array([
        [0,1,0,0],
        [0,0,0,0],
        [0,0,0,1],
        [0,0,length * mass_pole * gravity / (2 * moment_of_inertia) ,0]
    	])
    B = np.array([0,1,0,length * mass_pole / (2 * moment_of_inertia)]).reshape((4,1))
    Q = np.diag([1.0, 1.0, 1.0, 0.01])
    R = np.array([[0.001]])
    
    P = lqr(A,B,Q,R)
    Rinv = np.linalg.inv(R)
    K = np.dot(Rinv,np.dot(B.T, P))
    print(K)
    def ulqr(x):
    	x1 = np.copy(x)
    	x1[2] = np.sin(x1[2] + np.pi)
    	return -np.dot(K, x1)
    
    cart.goTo(500)
    command_speed = 0
    last_time = time.time()
    while True:
    	observation = cart.analyzer.getState()
    	x,x_dot,theta,theta_dot = observation
    	a = ulqr(np.array([(x-500)/1000,x_dot/1000,theta-0.01,theta_dot]))
    	t = time.time() 
    	dt = t - last_time
    	last_time = t
    	command_speed += 1 * a[0] * dt
    	#command_speed -= (x - 500) * dt * 0.001 * 0.1
    	#command_speed -= x_dot * dt * 0.001 * 0.5
    	cart.setSpeedMmPerS(1000 *command_speed)
    	print("theta {}\ttheta_dot {}\taction {}\tspeed {}".format(theta, theta_dot, a, command_speed))




<iframe width="560" height="315" src="https://www.youtube.com/embed/c65y1GXsSw4" frameborder="0" allow="accelerometer; autoplay; clipboard-write; encrypted-media; gyroscope; picture-in-picture" allowfullscreen></iframe>


