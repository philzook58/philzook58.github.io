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

# Create mesh and define function space
mesh = UnitSquare(20, 20)
V = FunctionSpace(mesh, "CG", 1)

# Inittial conditions
alpha = 3
beta = 1.2
u0 = Expression('1 + x[0]*x[0] + alpha*x[1]*x[1] + beta*t',
                alpha=alpha, beta=beta, t=0)


# Define Dirichlet boundary (x = 0 or x = 1)
def u0_boundary(x,on_boundary):
    return on_boundary



# Define boundary condition
#u0 = Expression('1+ x[0]*x[0] + 2*x[1]*x[1]')

bc = DirichletBC(V, u0, u0_boundary)

#Creates function from expression
u_1 = project(u0, V)

dt = 0.3 # timestep
# Define variational problem
u = TrialFunction(V)
v = TestFunction(V)
f = Constant(beta - 2 - 2 *alpha)
a = u*v*dx + dt*inner(nabla_grad(u), nabla_grad(v))*dx
L = (u_1 + dt*f)*v*dx


# Compute solution
u = Function(V)
A = assemble(a)

T = 2 # ending time
t = dt # current time
while t<=T:
    print "got this far"
    b = assemble(L)
    u0.t = t
    bc.apply(A,b)
    solve(A,u.vector(), b)
    t+=dt
    plot(u)
    u_1.assign(u)

# Save solution in VTK format
file = File("poisson.pvd")
file << u

# Plot solution
#interactive()
plot(u)
plot(mesh, interactive=True)
