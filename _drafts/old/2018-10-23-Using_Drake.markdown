---
author: philzook58
comments: true
date: 2018-10-23 21:44:43+00:00
layout: post
link: https://www.philipzucker.com/?p=1347
published: false
slug: Using Drake
title: Using Drake
wordpress_id: 1347
---

The underactuated robotics books examples are a good reference

The RigidBodyTree

The plant paradigm. The abstraction is that everything is a box with inpout and output ports

Typically the state is a position stacked with a velocity

There are two persepctives on dynamics at play here, There is the Newtonian persepctive hwich talks in terms of forces and torques.



Tasks:

Get Jaco stuff in there

Talk about frames rotations. Hmongenous coordinates?

Wrenches

Rigidboyd tree

Crumpling Jaco

InverseKineamtics

Describe Kinova ROS - maybe out of scope?











#What is Drake?

From the Drake Website (https://drake.mit.edu/):

Drake (“dragon” in Middle English) is a C++ toolbox started by the Robot Locomotion Group at the MIT Computer Science and Artificial Intelligence Lab (CSAIL). The development team has now grown significantly, with core development led by the Toyota Research Institute. It is a collection of tools for analyzing the dynamics of our robots and building control systems for them, with a heavy emphasis on optimization-based design/analysis.

While there are an increasing number of simulation tools available for robotics, most of them function like a black box: commands go in, sensors come out. Drake aims to simulate even very complex dynamics of robots (e.g. including friction, contact, aerodynamics, …), but always with an emphasis on exposing the structure in the governing equations (sparsity, analytical gradients, polynomial structure, uncertainty quantification, …) and making this information available for advanced planning, control, and analysis algorithms. Drake provides interfaces to high-level languages (MATLAB, Python, …) to enable rapid-prototyping of new algorithms, and also aims to provide solid open-source implementations for many state-of-the-art algorithms. Finally, we hope Drake provides many compelling examples that can help people get started and provide much needed benchmarks. We are excited to accept user contributions to improve the coverage.

#Getting Drake

Binaries may be gotten here.

<https://drake.mit.edu/installation.html>

There is some difficulty getting the external dependencies of Drake through the Lincoln lab proxy
Lincoln Lab specific instructions here

<https://llcad-github.llan.ll.mit.edu/VIVAS/VIVAS_/wiki/DRAKE-Install-and-Build-with-Bazel>

I did a couple things. I'm not sure which worked

I editted the dreal repository.bzl file to rpelace mark's username with mine
I also editted the path of the libibex to use the actual verison number instead of the {} pattern
I also set http_proxy and https_proxy.

There are a number of useful aliases setup by the setup_drake.bash script.

#Using Bazel

Drake uses Bazel as a build tool. Bazel is an open-source build and test tool similar to Make, Maven, and Gradle.

// is the build's main directory. This corresponds to the drake folder.
```...``` is the notation for everything in the subdirectory

```bazel build //...``` will build everything in the project
to query all the binaries avaiable for tools run ```bazel query //tools/...```

```bazel build```

```bazel run```

```bazel query```. Query is very useful for investiagting avaiable binaries within the examples folder

#Using Pydrake

By default pydrake will not be in the path. You can put pydrake into the path after building by running the following line or adding it to your .bashr

```
export PYTHONPATH=~/drake/drake-build/install/lib/python2.7/site-packages:${PYTHONPATH}
```

Drake is only compatible with python 2.7. If your default system install is python 3, you may need to explicitly run the python2.
The following message may be thrown if you inadvertently use python3.

```
Traceback (most recent call last):
File "inverse_kinematics.py", line 2, in <module>
from pydrake.all import *
File "/home/ph27868/drake/drake-build/install/lib/python2.7/site-packages/pydrake/__init__.py", line 25, in <module>
from . import common
File "/home/ph27868/drake/drake-build/install/lib/python2.7/site-packages/pydrake/common.py", line 3, in <module>
from ._common_py import *
ImportError: dynamic module does not define module export function (PyInit__common_py)
```

To import everything in Drake into the python namespace, the following line will work

```
from pydrake.all import *
```

Pydrake itself has generated documentation available here

<http://drake.mit.edu/pydrake/index.html>

A very useful tool for exploring and confirming the Drake functionality and syntax is the python REPL. From the python REPL or within your code, it is useful to inspect an object using either ```help(obj)``` or ```print(dir(obj))``` which will print a list of all the properties available on your object.

Any Eigen object in the C++ code gets bound to a numpy object via pybind https://pybind11.readthedocs.io/en/stable/advanced/cast/eigen.html
This is usually transparent and unsurprising.

#Drake resources

https://llcad-github.llan.ll.mit.edu/VIVAS/VIVAS_/wiki/DRAKE-Modeling-Guide

## Underactuated Robotics textbook and examples (They are not in the textbook)

Drake has a textbook being built alongside it by Russ Tedrake.

http://underactuated.mit.edu/underactuated.html

In particular the python source used to generate some of the exmaples in the book is worth examining.

https://github.com/RussTedrake/underactuated/tree/master/src

The full course is available online both on Edx and more recent versions on Youtube.

## Periscope Tutorials

https://github.com/gizatt/drake_periscope_tutorial

## Examples directory.

A useful source of use cases for drake can be found in the examples directory within the drake project. As of October 2018 the contents include:

* Acrobot - The Acrobot

* Cartpole - The cartpole is a classic control system consisting of a pendulum attached to a linearly actuated cart. In this directory you can find examples

* Pendulum

* Double Pendulum

* Kinova Jaco Arm

* Kuka Iiwa Arm

* Particles

* Bouncing Ball

* Contact Model - Contains bowling pins, a gripper, and sliding bricks demonstrating Drakes ability to simulate contact dynamics

* Compass Gait

* Rimless Wheel

* Atlas

* zmp

* quadcopter

## Doxygen
https://drake.mit.edu/doxygen_cxx/index.html
Besides the source code itself, the most accurate and up to date information is available in searchable form on the doxygen page

#Directory structure

#Optimization Solvers

Drake provides a common interface to many optimization solvers. Because of the tight integration, Drake has the capability to directly build the equations of motion for a system into a form the solver can comprehend.

The Mathematical Program class provides a high level interface to the different solvers. This class can be constructed as an object on it's own or as returned by other helper classes such as trajectory optimization builders.

Drake provides a symbolic expression modelling language in which to describe constraints and costs.

```python
from pydrake.all import *
import numpy as np

c = np.array([-1,-1])

#print(dir(LinearCost))
#print(LinearCost.a())
#LinearCost(c, 10) # linear cost cx + b

#print(MathematicalProgram())

m = MathematicalProgram()
print(dir(m))

'''
['AddBoundingBoxConstraint', 'AddConstraint', 'AddCost', 'AddL2NormCost', 'AddLinearComplementarityConstraint', 'AddLinearConstraint', 'AddLinearCost', 'AddLorentzConeConstraint', 'AddPositiveSemidefiniteConstraint', 'AddQuadraticCost', 'AddQuadraticErrorCost', 'AddSosConstraint', 'AddVisualizationCallback', 'EvalBindingAtSolution', 'FindDecisionVariableIndex', 'GetInitialGuess', 'GetSolution', 'GetSolverId', 'NewBinaryVariables', 'NewContinuousVariables', 'NewFreePolynomial', 'NewIndeterminates', 'NewSosPolynomial', 'NewSymmetricContinuousVariables', 'SetInitialGuess', 'SetInitialGuessForAllVariables', 'SetSolverOption', 'Solve', 'SubstituteSolution', '__class__', '__del__', '__delattr__', '__doc__', '__format__', '__getattribute__', '__hash__', '__init__', '__module__', '__new__', '__qualname__', '__reduce__', '__reduce_ex__', '__repr__', '__setattr__', '__sizeof__', '__str__', '__subclasshook__', '_pybind11_del_orig', 'bounding_box_constraints', 'linear_constraints', 'linear_costs', 'linear_equality_constraints', 'num_vars', 'quadratic_costs']
'''
xs = m.NewContinuousVariables(2, 'x')
print(xs)

#m.AddLinearCost( c[0]*xs[0] + c[1]*xs[1] )
m.AddCost( c[0]*xs[0] + c[1]*xs[1] )

#m.AddLinearConstraint(xs[0] == 0)
#print(dirm.Add)
#m.AddLinearConstraint(xs[0] <= 0)
m.AddLinearConstraint(xs[0] == 0)
m.AddLinearConstraint(3*xs[1] + xs[0] <= -1)
#m.AddLinearConstraint(xs[1] <= 0)
print(dir(m.linear_constraints()[0])) # constraint', 'evaluator', 'variables'
print(m.linear_equality_constraints())
print(m.bounding_box_constraints())
print(m.linear_costs()[0])
print(m.Solve())
print(m.GetSolverId().name())
# m.SetSolverOptions
print(m.GetSolution(xs))
```

There are a large variety of solvers out there for problems of different structure.

A Mathemtical Program is generally of the form

min f(x) s.t.
g(x) \\ge 0
h(x) = 0

One of the oldest and most studied class of these programs are known as Linear Programs which has linear cost and constraints. This mathemtical program has very efficient solvers available for it.

A large class of optimization problems that are tractable are known as Convex Optimization. The cost functions must be bowl shaped (convex), the inequality constraints must defined convex regions and the eqaulity constraints must be affine (linear + offset). For this class, gradient descent roughly works and refinements of gradient descent like Newton's method work even better. Essentially greedy local moves are also acceptable gloabl moves and there are no local minima or tendril regions to get cuaght in.

Quadratic Programming - OSQP

Second Order Cone Programming

Semidefinite Programming

Sum of Squares

Many problems cannot be put into this form. If the inherent nature of the porblme at hand requires it, you may choose to use a nonlinear programming solver of Mixed Integer Programming Solver.

The solvers Ipopt and Snopt are nonlinear programming solvers. Ipopt is an open source solver and Snopt is proprietary. These solvers use local convex approximations to the problem to heuristically drive the solution to a local minimum.

Mixed Integer Linear Programming is Linear Programming with additional ability to require variables to take on integer values. This additional constraint type takes the problem from polynomial time solvable to NP-complete. A surprisingly large number of discrete and continuous optimization problems can be encoded into this framework. Internally, these solvers use linear programming solvers to guide the discrete search.

Part of the art and fun of the subject comes from manipulating your problem into a form amenable to powerful available solvers and theory.

Combinatorial Solvers - SAT, SMT

Available Solvers

Mosek

Gurobi

Snopt

Ipopt

OSQP

ik

LCP

#Drake Concepts

#Simulation

For dynamic simulation, Drake exposes a Lego block interface for building complex systems out of smaller pieces, a paradigm similiar to Simulink and other medlling software.
Objects possess with input and output ports. One wires up input ports to output ports.

For simple forward simulation

Construct a builder object

One cause of crashes may be leaving ports unconnected.

The builder object exposes the following functions.

Simulator has different

Context holds state information

There following excerpt from https://github.com/RussTedrake/underactuated/tree/master/src/simple shows how to define a simple system and simulate it.

```python
from pydrake.systems.framework import VectorSystem

# Define the system.
class SimpleContinuousTimeSystem(VectorSystem):
def __init__(self):
VectorSystem.__init__(self,
0, # Zero inputs.
1) # One output.
self._DeclareContinuousState(1) # One state variable.

# xdot(t) = -x(t) + x^3(t)
def _DoCalcVectorTimeDerivatives(self, context, u, x, xdot):
xdot[:] = -x + x**3

# y(t) = x(t)
def _DoCalcVectorOutput(self, context, u, x, y):
y[:] = x
```

```python
import matplotlib.pyplot as plt
from pydrake.all import (DiagramBuilder, SignalLogger, Simulator)
from continuous_time_system import *

# Create a simple block diagram containing our system.
builder = DiagramBuilder()
system = builder.AddSystem(SimpleContinuousTimeSystem())
logger = builder.AddSystem(SignalLogger(1))
builder.Connect(system.get_output_port(0), logger.get_input_port(0))
diagram = builder.Build()

# Create the simulator.
simulator = Simulator(diagram)

# Set the initial conditions, x(0).
state = simulator.get_mutable_context().get_mutable_continuous_state_vector()
state.SetFromVector([0.9])

# Simulate for 10 seconds.
simulator.StepTo(10)

# Plot the results.
plt.plot(logger.sample_times(), logger.data().transpose())
plt.xlabel('t')
plt.ylabel('x(t)')
plt.show()
```

Refs:

http://underactuated.mit.edu/underactuated.html?chapter=systems

#Rigid Body Trees

Drake uses the URDF (Universal Robot Description Format) format, whihci s described in greaer detail in the modelling documents. This is a common robot format originating in the ROS community for which you can find models of many commercial robots online. It is an xml based format with visualization, intertial, and collision tags.

RigidBodyTrees may be built from a urdf file, some of which are packaged inside of Drake

There are two views to take of a robot. The intrinsic coordaintes has one variable per degree of freedom of the robot. The extrinisc coordinates specify the spatial locations and orientation. These are called frames. These spatial coordinates may be constrained to relationship by a rigid mounting or gearing for example.

Drake describes the dynamics in terms of the intrinsic coordinates. The robot has equations of motion in the common form "" (See underactuated robotics textbook)

$$ X_i = f_i(x_j)$$

Drake provides a couple of useful mappings between the intrinsic and extrinsic coordinates.
First, given a set of internal coordinates, Drake transforms these into frames, which may be expressed in yet another cooridnate system.

Secondly, the Jacobian of the transformation

$$ J_{ij} = \frac{\partial f_i}{\partial x_j} $$

This Jacobian is useful for translating externallly described small displacements, velocities, forces, and torques, into the equivalent temrs for the internal coordinates.

For example, translating a force on the end effector.

RigidBodyTree exposes the following functions

cache

##Example: Crumpling Jaco

#Automatic Differentiation

Automatic Differentiation is the capability to have derivbatives computed alongside code that computes the values. It is largely based upon application of the chain rule. There are two modes, forward and reverse mode.

Drake exposes automatic differentiation capability for manual use

```python
from pydrake.all import *
import numpy as np

v = AutoDiffXd(2)

print(v)

print(v.cos())
f = v * v
print(f.derivatives())

v = AutoDiffXd(2.0, np.array([3,4,5]))

# second prameter initializes forward mode derivative information
v = AutoDiffXd(4.0, np.array([1,1]))

print(v)
print(v * v)
f = v * v * v
print(f.derivatives())
```
More importantly Drake uses automatic differentiation internally to marshal symbolic problems into forms acceptable to external solvers and to calculate Jacobians.

#Trajectory Optimization

Trajectory optimization is a framework in which one uses Mathemtical programming to solve optimal trajectory problems. The input to the system
is considered to be a decision variable in a Mathemtical programming problem.

Direct Collocation - Both the path

One way of performing directo collocation is to take the path position at a dscrte number of time points and make a decision variable for each. The discretized equations of motion become constraints that neighboring time points have to obey. One may then inject any other desired requirements (staying inside some safe region for example) as additional constraints.

Shooting Methods - The path is not considered to be a decision variable

The combination of dyanmical system modelling, automatic differentiation, and bindings to mathemtical prgramming solvers makes Drake an excellent platform for trajectory optimization.

http://underactuated.mit.edu/underactuated.html?chapter=trajopt

#Visualization

The Drake visualizer may be found in the tools folder

Also get the drake visualizer running from the drake directory
bazel run //tools:drake_visualizer

May need to run commands here to make LCM work and visualizer not crash immediately
http://lcm-proj.github.io/multicast_setup.html
sudo ifconfig lo multicast
sudo route add -net 224.0.0.0 netmask 240.0.0.0 dev lo

#Controllers

Drake comes built in with some useful controllers. PID, LQR, InverseKinematics

The InverseKinematics controller uses differential information about the system to find velcoty commands to make a chosen frame move in the desired direction. The planner exposes the additional ability to add constraints.

For more examples, see the underactuated robotics notes

## Example Application: Estimating end-effector force from motor torques

## Example Application: Inverse Kinematic planning with Balance Constraint

## Example Application

# Kinova ROS package

The Kinova Jaco arm is easily communicated to through the Kinova ROS package

https://github.com/Kinovarobotics/kinova-ros

The package as of October 2018 supports Ubuntu 14.04 and ROS _

To update functionality to

The Gazebo simulator seems to have a great deal of trouble.
One suggestion is that you have to add a small nonzero size parameter to your urdf files.

The messages posted by the ROS Package are

```python
from std_msgs.msg import String
from sensor_msgs.msg import JointState
from control_msgs.msg import JointControllerState
import rospy
#from pydrake.all import *
import numpy as np
from geometry_msgs.msg import WrenchStamped
def callback(data):
print(data.name) # ['j2n6s300_joint_1', 'j2n6s300_joint_2', 'j2n6s300_joint_3', 'j2n6s300_joint_4', 'j2n6s300_joint_5', 'j2n6s300_joint_6', 'j2n6s300_joint_finger_1', 'j2n6s300_joint_finger_2', 'j2n6s300_joint_finger_3']

print(data.position)
print(data.velocity)
print(data.effort)

rospy.init_node('listener', anonymous=True)

#rospy.Subscriber("/j2n7s300/joint_4_position_controller/state", JointControllerState, callback)

def wrenchcallback(data):
print(data.wrench.force.x) # ['j2n6s300_joint_1', 'j2n6s300_joint_2', 'j2n6s300_joint_3', 'j2n6s300_joint_4', 'j2n6s300_joint_5', 'j2n6s300_joint_6', 'j2n6s300_joint_finger_1', 'j2n6s300_joint_finger_2', 'j2n6s300_joint_finger_3']
print(data.wrench.torque)
#print(data)

'''
header:
seq: 16944
stamp:
secs: 1538592724
nsecs: 238304938
frame_id: "j2n6s300_link_base"
wrench:
force:
x: 0.503400802612
y: 1.23997282982
z: -1.95140719414
torque:
x: -0.0169065663541
y: 0.000999942868142
z: -0.00571718788351

'''

#rospy.Subscriber("/j2n6s300_driver/out/joint_state", JointState, callback)

rospy.Subscriber("/j2n6s300_driver/out/tool_wrench", WrenchStamped, wrenchcallback)

rospy.spin()
```

## ROS Intercommunication
The commununcation stack used by Drake is Lightweight Communications and Marshalling (LCM). For interconnection to the rest of the ROS ecosystem, this adds a layer of friction.

One option is to use the lcm_to_ros project https://github.com/nrjl/lcm_to_ros
This is a generator for building republishers of messages going between ROS and LCM

Another option is to build custom republishers.

'''

Get drake in the path
```
export PYTHONPATH=~/Documents/underactuated/src:$PYTHONPATH
export PYTHONPATH=~/drake/drake-build/install/lib/python2.7/site-packages:${PYTHONPATH}
```
In another terminal turn on the jaco driver
roslaunch kinova_bringup kinova_robot.launch kinova_robotType:=j2n6s300

Also get the drake visualizer running from the drake directory
bazel run //tools:drake_visualizer

May need to run commands here to make LCM work and visualizer not crash immediately
http://lcm-proj.github.io/multicast_setup.html
sudo ifconfig lo multicast
sudo route add -net 224.0.0.0 netmask 240.0.0.0 dev lo

```python
import rospy
from pydrake.all import *
import numpy as np
from sensor_msgs.msg import JointState
from geometry_msgs.msg import WrenchStamped
tree = RigidBodyTree( FindResourceOrThrow( "drake/manipulation/models/jaco_description/urdf/j2n6s300.urdf"),
FloatingBaseType.kFixed)
bodies = [tree.get_body(j) for j in range(tree.get_num_bodies())]
no_wrench = { body : np.zeros(6) for body in bodies}

builder = DiagramBuilder()

lc = DrakeLcm()
vis = DrakeVisualizer(tree, lc)
robot = builder.AddSystem(RigidBodyPlant(tree))
#controller = builder.AddSystem(BalancingLQR(robot))
publisher = builder.AddSystem(vis)
builder.Connect(robot.get_output_port(0), publisher.get_input_port(0))

diagram = builder.Build()
simulator = Simulator(diagram)
simulator.set_target_realtime_rate(1.0)
simulator.set_publish_every_time_step(False)
context = simulator.get_mutable_context()
state = context.get_mutable_continuous_state_vector()
state.SetFromVector(np.zeros(9*2))
#print(dir(simulator))
#rint(dir(context))
print("here")
simulator.Initialize()
#simulator.StepTo(0.1)
#Initialize

q = None
v = None
f = None

def callback(data):
global q, v, f

q = np.array(data.position)
v = np.array(data.velocity)
f = np.array(data.effort)
q[0] = q[0]
q[1] = np.pi + q[1]
q[2] = np.pi + q[2]
q[3] = q[3]

rospy.init_node('listener', anonymous=True)

rospy.Subscriber("/j2n6s300_driver/out/joint_state", JointState, callback)

rate = rospy.Rate(4)
rate.sleep()
while not rospy.is_shutdown():
print("Setting State")
state = context.get_mutable_continuous_state_vector()
#q[1] = -q[1] + np.pi

state.SetFromVector(np.append(q,v))
simulator.Initialize()
rate.sleep()
```








