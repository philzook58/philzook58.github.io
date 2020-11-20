---
author: philzook58
comments: true
date: 2020-08-01 15:06:58+00:00
layout: post
link: https://www.philipzucker.com/system-identification-of-a-pendulum-with-scikit-learn/
slug: system-identification-of-a-pendulum-with-scikit-learn
title: System Identification of a Pendulum with scikit-learn
wordpress_id: 2891
tags:
- control
- python
- scikit-learn
---




[System identification](https://en.wikipedia.org/wiki/System_identification) is the name of the problem of finding the dynamics of a physical system. It is an old topic. For some interesting material on system identification, check out Steve Brunton's video here [https://www.youtube.com/watch?v=6F2YVsT9dOs](https://www.youtube.com/watch?v=6F2YVsT9dOs)







We've been building a raspberry pi controlled pendulum to be controlled from the internet and the problem came up of trying to get a simulation to match the physical pendulum.







![](https://www.philipzucker.com/wp-content/uploads/2020/08/swingup.gif)Look at 'er go. [Energy shaping](https://www.control.utoronto.ca/~broucke/ece1653s/Intro/ast_fur96.pdf) for the win.







We weighed the pendulum and calculated the torque due to gravity $latex mg\frac{l}{2} \sin(\theta) $ (you can think of it as the full force of gravity acting on the level arm of the center of the pole $latex \frac{l}{2}\sin(\theta)$) and moment of inertia of a [rod about it's end](http://hyperphysics.phy-astr.gsu.edu/hbase/mi2.html) $latex \frac{1}{3}m L^2$.







However, It is difficult to estimate the torque supplied by the motor. Motors have surprisingly complicated behavior. It is also difficult from first principles to estimate damping or friction terms.







There are a couple different experimental stratagems for a pendulum. One thing we tried was setting the pendulum on it's side and setting the motor duty cycle to different values. From this you can fit a parabola to those curves and get a  acceleration constant for the different motor settings. Experimentally speaking, it seemed roughly linear acceleration to motor PWM duty cycle.







Another stratagem is to take resonance curves for the pendulum. Try exciting it with different sinusoidal torques at a sweep of frequencies. From this curve you can recover a resonance frequency and damping coefficients.







These all make sense as kind of ersatz methods. We're taking our intuitive understanding of the system and other results from simpler or related systems and combining them together.







An interesting alternative approach to the above is to drive the pendulum with a random torque and then fit a parameterized model of the equations of motion to the observed acceleration. The model should include at the least the gravity $latex \beta_1 sin(\theta)$ term, motor torque term $latex \beta_2 u$, and a damping terms $latex \beta_3 \dot{\theta}$. A simple start is $latex \alpha = \beta_1 sin(\theta) + \beta_2 u + \beta_3 \dot{\theta} $. This is a linear model with respect to the coefficients $latex \beta_i$ and can be solved by least squares.







I've come to appreciate sci-kit learn for fitting. It doesn't have the hottest most high falutin' fads, but it's got a lot of good algorithms in it that just work, are damn easy to use,  and are easy to swap different possibilities out of there. Even though I know how to more manually set up a least squares system or solve a LASSO problem via cvxpy, it makes it really easy and clean. I've started reaching for it for fast attacks on fitting problems. 







We mocked out our interface to behave similarly to an [OpenAI gym](https://github.com/openai/gym) interface. Because of this, the observations already have the cosine and sine terms that might be of interest and the angular velocity value that would be used for a simple damping term $latex \beta \dot{\theta}$. 






    
    <code>
    
    import gym
    import time
    import numpy as np
    env = gym.make('pendulum-v0')
    observation = env.reset()
    
    action = 0
    dt = 0.05
    obs = []
    rews = []
    actions = []
    for i in range(1000):
    
        # A random walk for actions.
        # we need the actions to be slow changing enough to see trends
        # but fast enough to see interesting behavior
        # tune this by hand 
        action += np.random.randn() * dt
        action = max( min(action, 2 ), -2) 
        observation, reward, done, info = env.step([action])
        obs.append(observation)
        actions.append(action)
        rews.append(reward)
        time.sleep(0.05)
    
    
    obs = np.array(obs) # obs includes thetadot, cos(theta), sin(theta). A good start.
    actions = np.array(actions) # the pwm value used
    
    # data to predict alpha from. Each row is a data point from one time step.
    X = np.hstack( (obs[:-1, :] , actions[:-1].reshape(-1,1)) ) 
    
    alphas = (obs[1:,2] - obs[:-1,2]  ) / dt  #angular acceleration
    
    # feel free to swap in LASSO or other regressors
    from sklearn.linear_model import LinearRegression 
    
    
    # fit the observed angular acceleration as a function of X
    reg = LinearRegression().fit(X, alphas)
    print(f"intercept : {reg.intercept_},  coeffs : {reg.coef_} ")</code>







The number that came out for gravity term matched the number calculated from first principles by within 10%. Not bad!







A thing that is nice about this approach is that one is able to add terms into the dynamics for which we don't have good intuitive models to compare to like your good ole Physics I [Coulombic friction term](https://en.wikipedia.org/wiki/Friction#Dry_friction) $latex F \propto -sign(v)  $ or nonlinearities. 



