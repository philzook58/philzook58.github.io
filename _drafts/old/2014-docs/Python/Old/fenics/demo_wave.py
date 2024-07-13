"""This demo program solves Poisson's equation

    - div grad u(x, y) = f(x, y)

on the unit square with source f given by

    f(x, y) = 10*exp(-((x - 0.5)^2 + (y - 0.5)^2) / 0.02)

and boundary conditions given by

    u(x, y) = 0        for x = 0 or x = 1
du/dn(x, y) = sin(5*x) for y = 0 or y = 1
"""

# Copyright (C) 2007-2011 Anders Logg
#
# This file is part of DOLFIN.
#
# DOLFIN is free software: you can redistribute it and/or modify
# it under the terms of the GNU Lesser General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# DOLFIN is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
# GNU Lesser General Public License for more details.
#
# You should have received a copy of the GNU Lesser General Public License
# along with DOLFIN. If not, see <http://www.gnu.org/licenses/>.
#
# First added:  2007-08-16
# Last changed: 2011-06-28

# Begin demo

from dolfin import *
#import matplotlib.pyplot as plt
#from mpl_toolkits.mplot3d import Axes3D

# Create mesh and define function space
mesh = UnitCircle(30)
V = FunctionSpace(mesh, "CG", 1)

# Inittial conditions
alpha = 500

uinit = Expression('exp(alpha*(-x[0]*x[0] - x[1]*x[1]))',
                alpha=alpha)
ut_init = Constant(0)

u0 = Constant(0)
# Define Dirichlet boundary (x = 0 or x = 1)
def u0_boundary(x,on_boundary):
    return on_boundary

c = 1

# Define boundary condition
#u0 = Expression('1+ x[0]*x[0] + 2*x[1]*x[1]')

bc = DirichletBC(V, u0, u0_boundary)

#Creates function from expression
u_1 = project(uinit, V)
u_2 = project(uinit, V)

dt = 0.05 # timestep
# Define variational problem
u = TrialFunction(V)
v = TestFunction(V)
f = Constant(0)
a = u*v*dx + c**2*dt**2*inner(nabla_grad(u), nabla_grad(v))*dx
L = (2*u_2 - u_1 + dt**2*f)*v*dx


# Compute solution
u = Function(V)
A = assemble(a)

T = .5 # ending time
t = 2*dt # current time
while t<=T:
    print "got this far"
    b = assemble(L)
    #u0.t = t
    bc.apply(A,b)
    solve(A,u.vector(), b)
    t+=dt
    #save_plot(u,filename= "pics/graph" + str(int(t/dt)).zfill(2)+".png")
    u_1.assign(u_2)
    u_2.assign(u)
    

# Save solution in VTK format
file = File("poisson.pvd")
file << u

# Plot solution
#interactive()
#plot_surface(mesh.coordinates()[:][0], mesh.coordinates()[:][1],u.vector().array())
plot(u)
plot(mesh, interactive=True)
