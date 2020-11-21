---
author: philzook58
comments: true
date: 2019-10-06 20:26:07+00:00
layout: post
link: https://www.philipzucker.com/flappy-bird-as-a-mixed-integer-program/
slug: flappy-bird-as-a-mixed-integer-program
title: Flappy Bird as a Mixed Integer Program
wordpress_id: 2345
categories:
- Optimization
- Robots
tags:
- control
- cvxpy
- MIP
- python
---

<video controls>
  <source  type="video/mp4" src="/assets/flappy_bird.mp4"></source>
  Your browser does not support the video tag.
</video>


[My birds.](https://www.youtube.com/embed/rdhRf0OCx5c?start=70)





Mixed Integer Programming is a methodology where you can specify convex (usually linear) optimization problems that include integer/boolean variables.







[Flappy Bird](https://flappybird.io/) is a game about a bird avoiding pipes.







We can use mixed integer programming to make a controller for Flappy Bird. Feel free to put this as a real-world application in your grant proposals, people.







While thinking about writing a MIP for controlling a lunar lander game, I realized how amenable to mixed integer modeling flappy bird is. Ben and I put together the demo on Saturday. You can find his sister blog post [here](http://blog.benwiener.com/programming/2019/10/06/flappy-bird-mpc.html).







The bird is mostly in free fall, on parabolic trajectories. This is a linear dynamic, so it can directly be expressed as a linear constraint.  It can discretely flap to give itself an upward impulse. This is a boolean force variable at every time step. Avoiding the ground and sky is a simple linear constraint. The bird has no control over its x motion, so that can be rolled out as concrete values. Because of this, we can check what pipes are relevant at time points in the future and putting the bird in the gap is also a simple linear constraint.







There are several different objectives one might want to consider and weight. Perhaps you want to save the poor birds energy and minimize the sum of all flaps `cvx.sum(flap)`. Or perhaps you want to really be sure it doesn't hit any pipes by maximizing the minimum distance from any pipe. Or perhaps minimize the absolute value of the y velocity, which is a reasonable heuristic for staying in control. All are expressible as linear constraints. Perhaps you might want a weighted combo of these. All things to fiddle with.







There is a [pygame flappy bird clone](https://github.com/sourabhv/FlapPyBird) which made this all the much more slick. It is well written and easy to understand and modify. Actually figuring out the appropriate bounding boxes for pipe avoidance was finicky. Figuring out the right combo of bird size and pipe size is hard, combined with computer graphics and their goddamn upside down coordinate system.







We run our solver in a model predictive control configuration. Model predictive control is where you roll out a trajectory as an optimization problem and resolve it at every action step. This turns an open loop trajectory solve into a closed loop control, at the expense of needing to solve a perhaps very complicated problem in real time. This is not always feasible.







My favorite mip modeling tool is [cvxpy](https://www.cvxpy.org/). It gives you vectorized constraints and slicing, which I love. More tools should aspire to achieve numpy-like interfaces. I've got lots of other blog posts using this package which you can find in[ my big post list](http://www.philipzucker.com/archive-3/) the side-bar  👀.







The github repo for the entire code is here:[](https://github.com/philzook58/FlapPyBird-MPC) [https://github.com/philzook58/FlapPyBird-MPC](https://github.com/philzook58/FlapPyBird-MPC)







And here's the guts of the controller:






    
    
```python

import cvxpy as cvx
import numpy as np
import matplotlib.pyplot as plt


N = 20 # time steps to look ahead
path = cvx.Variable((N, 2)) # y pos and vel
flap = cvx.Variable(N-1, boolean=True) # whether or not the bird should flap in each step
last_solution = [False, False, False]
last_path = [(0,0),(0,0)]

PIPEGAPSIZE  = 100
PIPEWIDTH = 52
BIRDWIDTH = 34
BIRDHEIGHT = 24
BIRDDIAMETER = np.sqrt(BIRDHEIGHT**2 + BIRDWIDTH**2)
SKY = 0
GROUND = (512*0.79)-1
PLAYERX = 57


def getPipeConstraints(x, y, lowerPipes):
    constraints = []
    for pipe in lowerPipes:
        dist_from_front = pipe['x'] - x - BIRDDIAMETER
        dist_from_back = pipe['x'] - x + PIPEWIDTH
        if (dist_from_front < 0) and (dist_from_back > 0):
            #print(pipe['y'] + BIRDDIAMETER,  pipe['y'] + PIPEGAPSIZE)
            constraints += [y <= (pipe['y'] - BIRDDIAMETER)] # y above lower pipe
            constraints += [y >= (pipe['y'] - PIPEGAPSIZE)] # y below upper pipe
    #if len(constraints) > 0:
        #print(constraints)
    return constraints

def solve(playery, playerVelY, lowerPipes):
    global last_path, last_solution

    print(last_path)
    pipeVelX = -4
    playerAccY    =   1   # players downward accleration
    playerFlapAcc =  -14   # players speed on flapping

    # unpack variables
    y = path[:,0]

    vy = path[:,1]

    c = [] #constraints
    c += [y <= GROUND, y >= SKY]
    c += [y[0] == playery, vy[0] == playerVelY]

    x = PLAYERX
    xs = [x]
    for t in range(N-1):
        dt = t//10 + 1
        #dt = 1
        x -= dt * pipeVelX
        xs += [x]
        c += [vy[t + 1] ==  vy[t] + playerAccY * dt + playerFlapAcc * flap[t] ]
        c += [y[t + 1] ==  y[t] + vy[t + 1]*dt ]
        c += getPipeConstraints(x, y[t+1], lowerPipes)


    #objective = cvx.Minimize(cvx.sum(flap)) # minimize total fuel use
    objective = cvx.Minimize(cvx.sum(flap) + 10* cvx.sum(cvx.abs(vy))) # minimize total fuel use

    prob = cvx.Problem(objective, c)
    try:
        prob.solve(verbose = False, solver="GUROBI")
        #print(np.round(flap.value).astype(bool))
        #plt.plot(y.value)
        #plt.show()
        last_path = list(zip(xs, y.value))
        last_solution = np.round(flap.value).astype(bool)
        return last_solution[0], last_path
    except:
        last_solution = last_solution[1:]
        last_path = [((x-4), y) for (x,y) in last_path[1:]]
        return last_solution[0], last_path



```








I think it is largely self explanatory but here are some notes. The `dt = t//10 + 1` thing is about decreasing our time resolution the further out from the current time step. This increases the time horizon without the extra computation cost. Intuitively modeling accuracy further out in time should matter less. The `last_solution` stuff is for in case the optimization solver fails for whatever reason, in which case it'll follow open-loop the last trajectory it got.







### Bits and Bobbles







  * We changed the dynamics slightly from the python original to make it easier to model. We found this did not change the feel of the game. The old dynamics were piecewise affine though, so are also modelable using mixed integer programming. [http://groups.csail.mit.edu/robotics-center/public_papers/Marcucci18.pdf](http://groups.csail.mit.edu/robotics-center/public_papers/Marcucci18.pdf) . Generally check out the papers coming out of the [Tedrake group](http://groups.csail.mit.edu/locomotion/pubs.shtml). They are sweet. Total fanboy over here.
  * The controller as is is not perfect. It fails eventually, and it probably shouldn't. A bug? Numerical problems? Bad modeling of the pipe collision? A run tends to get through about a hundred pipes before something gets goofy.
  * Since we had access to the source code, we could mimic the dynamics very well.  How robust is flappy bird to noise and bad modeling? We could add wind, or inaccurate pipe data.
  * Unions of Convex Region. Giving the flappy bird some x position control would change the nature of the problem. We could easily cut up the allowable regions of the bird into rectangles, and represent the total space as a union of convex regions, which is also MIP representable.
  * Verification - The finite difference scheme used is crude. It is conceivable for the bird to clip a pipe. Since basically we know the closed form of the trajectories, we could verify that the parabolas do not intersect the regions. For funzies, maybe use sum of squares optimization?
  * Realtime MIP. Our solver isn't quite realtime. Maybe half real time. One might pursue methods to make the mixed integer program faster. This might involve custom branching heuristics, or early stopping. If one can get the solver fast enough, you might run the solver in parallel and only query a new path plan every so often.
  * 3d flappy bird? Let the bird rotate? What about a platformer (Mario) or lunar lander? All are pretty interesting piecewise affine systems.
  * Is this the best way to do this? Yes and no. Other ways to do this might involve doing some machine learning, or hardcoding a controller that monitors the pipe locations and has some simple feedback. You can find some among the [forks of FlapPyBird](https://github.com/sourabhv/FlapPyBird/network/members). I have no doubt that you could write these quickly, fiddle with them and get them to work better and faster than this MIP controller. However, for me there is a difference between _could _work and _should _work. You can come up with a thousand bizarre schemes that could work. RL algorithms fall in this camp. But I have every reason to believe the MIP controller _should _ work, which makes it easier to troubleshoot.


