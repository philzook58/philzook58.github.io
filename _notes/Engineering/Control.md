---
layout: post
title: Control
---
- [PID](#pid)
- [Kalman Filters](#kalman-filters)
- [Particle Filters](#particle-filters)
- [System Identification](#system-identification)
- [Feedback](#feedback)
- [Linear Control](#linear-control)
- [Nonlinear control](#nonlinear-control)
- [Robust Control](#robust-control)
- [Optimal Control](#optimal-control)
  - [Model Predictive Control](#model-predictive-control)
- [Kinematics](#kinematics)
- [Systems](#systems)
  - [Drones](#drones)
  - [Arms](#arms)
  - [Cars](#cars)
  - [Walking](#walking)
  - [spacecraft https://www.coursera.org/learn/nonlinear-spacecraft-attitude-control](#spacecraft-httpswwwcourseraorglearnnonlinear-spacecraft-attitude-control)
  - [Balancing](#balancing)
- [Misc](#misc)

See also:

- Differential Equations
- Machine Learning (Reinforcement learning)

<https://en.wikipedia.org/wiki/Control_theory>
<https://en.wikipedia.org/wiki/Category:Control_theory>

# PID

Integral windup
anti reset windup
gain scheduling <https://en.wikipedia.org/wiki/Gain_scheduling>
deadband compensation
derviative kick
setpoint weighting <https://jckantor.github.io/CBE30338/04.02-PID_Control_with_Setpoint_Weighting.html>

<https://jckantor.github.io/CBE30338/04.00-PID_Control.html>

bumpless transfer

root locus, bode, nyquist
Phase plane
transfer function

# Kalman Filters

EKF
UKF

# Particle Filters

# System Identification

<https://en.wikipedia.org/wiki/System_identification>
model order reduction <https://en.wikipedia.org/wiki/Model_order_reduction>
<https://www.philipzucker.com/system-identification-of-a-pendulum-with-scikit-learn/>
<https://github.com/dynamicslab/pysindy>

# Feedback

op amps
negative and positive
This is such a generic concept.

# Linear Control

Steven course
Linear matrix systems
controllability and observaibility - nullspaces of matrices

# Nonlinear control

sliding mode control
Energy Shaping
Lyapunov Functions

[Slotine Lectures on Nonlinear Systems](https://web.mit.edu/nsl/www/videos/lectures.html)
tedrake underactuated control

# Robust Control

# Optimal Control

<https://en.wikipedia.org/wiki/Optimal_control>
 Dynamic Programming
bellman hamilton jacobi
bang bang
pontraygin

## Model Predictive Control

<https://en.wikipedia.org/wiki/Model_predictive_control>
<https://en.wikipedia.org/wiki/Trajectory_optimization>
LQR
explicit mpc
<https://www.philipzucker.com/categorical-combinators-for-convex-optimization-and-model-predictive-control-using-cvxpy/>
<https://www.philipzucker.com/categorical-lqr-control-with-linear-relations/>
<https://www.philipzucker.com/model-predictive-control-of-cartpole-in-openai-gym-using-osqp/>
<https://www.philipzucker.com/osqp-sparsegrad-fast-model-predictive-control-python-inverted-pendulum/>
<https://www.philipzucker.com/LQR/>

# Kinematics

<https://www.philipzucker.com/some-notes-on-drake-a-robotic-control-toolbox/>
Polynomial equations

tedrake robot arm

# Systems

## Drones

## Arms

## Cars

## Walking

## spacecraft <https://www.coursera.org/learn/nonlinear-spacecraft-attitude-control>

## Balancing

cartpole
acrobat
cube balancing
robot wheel balance
pendulum

# Misc

[A nearest negighbor imitation leaning approach to manipulation](https://twitter.com/LerrelPinto/status/1507342646427144199?s=20&t=y2AWW1GNA8vyxsWqTXmKPQ)
[urdf from video](https://twitter.com/erwincoumans/status/1506758358971260931?s=20&t=y2AWW1GNA8vyxsWqTXmKPQ)

[Linear time-variant model predictive control in Python.](https://github.com/tasts-robots/ltv-mpc)

[Steve brunton](https://www.youtube.com/@Eigensteve)
hinfinity control

compressed sensing
bayesian
stochastic control

duality of control and filtering. If you had a system where your goal was to match the observations, that's basically a control problem
