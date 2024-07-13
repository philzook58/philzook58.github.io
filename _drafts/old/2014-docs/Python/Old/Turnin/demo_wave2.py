#Based on FEniCS Poisson Demo by Anders Logg by Philip Zucker 2011


from dolfin import *

# Create mesh and define function space
mesh = UnitSquare(30,30)
V = FunctionSpace(mesh, "CG", 1)

# Initial conditions Normal Mode
uinit = Expression('sin(alpha*2*x[0])*sin(alpha*x[1])',alpha=3.1459)
u2init = Expression('0.9*sin(alpha*2*x[0])*sin(alpha*x[1])',alpha=3.1459)

#Homogenous Dirichlet Boundary conditions
u0 = Constant(0)
# Define Dirichlet boundary (x = 0 or x = 1)
def u0_boundary(x,on_boundary):
    return on_boundary

c = 1 #Speed of Wave

bc = DirichletBC(V, u0, u0_boundary)

#Creates function from expression
u_1 = project(uinit, V)
u_2 = project(u2init, V)

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
    b = assemble(L)
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
plot(u)
plot(mesh, interactive=True)
