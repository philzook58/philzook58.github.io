---
author: philzook58
comments: true
date: 2019-08-19 02:56:36+00:00
layout: post
link: https://www.philipzucker.com/?p=2252
published: false
slug: Ising Landau Ginzburg notes
title: Ising Landau Ginzburg notes
wordpress_id: 2252
---




### Very Old Notes. Pay No Heed.







It is interesting that the coulomb gas in statistical mechanics/quantum mechanics is a dual model to the XY model, which I've played with previously. See 














    
    using JuMP
    using Cbc
    using ImageView
    N = 10
    B = randn(N,N)
    m = Model(solver=CbcSolver())
    @variable(m, x[1:N,1:N], Bin)
    @variable(m, sx[1:N-1,1:N], Bin)
    @variable(m, sy[1:N,1:N-1], Bin)
    
    @constraint(m, sx[:, :] .>= x[1:N-1, :] + x[2:N,:] - 1)
    @constraint(m, sx[:, :] .<= x[1:N-1, :])
    @constraint(m, sx[:, :] .<=  x[2:N,:])
    
    @constraint(m, sy[:, :] .>= x[:, 1:N-1] + x[:, 2:N] - 1)
    @constraint(m, sy[:, :] .<= x[:, 1:N-1])
    @constraint(m, sy[:, :] .<= x[:, 2:N])
    J = 1.0
    
    @objective(m, Max, sum(B .* x) + J * sum(sx) + J * sum(sy))
    solve(m)
    
    println(x)
    println(getvalue(x))
    
    imshow(getvalue(x))







In this chapter they basically do what I've done here




https://onlinelibrary.wiley.com/doi/10.1002/3527603794.ch4




They claim the Ising model IS max-cut. Shouldn't we use the SDP aproximation then?




This whole book is fascinating







There is a theme that it can be useful to think of SAT solvers, CP solvers, and other such things as smart loops. The naive way to solve these problems is to just loop over all the variable values brute force. The clever techniques DPLL and cutting plane solvers let us zoom in surprising quickly on the actual best answer. We can then continue to search through the space, with an additional constraint that I don't want to see my previous solution again.




Gurobi has a feature of lazy constraint addition. Given




How do we do this? We'll need to generate out own cuts basically.




This will order our summation of the partition function in order of relative probability.







We can aid the solver by removing all the symmetries we can think of.







All of this is appropriate for a low temperature expansion, but what about a high temperature expansion?







Comparison to monte carlo method - Monte Carlo feels extremely reasonable at high temperature, perhaps less so at low. At high temperature, finding the true minima becomes less important, you want to just sample a wide swath







One can also consider suing a #SAT solver. Stat mech has a very combinatorial feel, especially for the microcanonical ensemble. We could encode an energy restriction, and then use a #SAT solver to count the number of states. This has a lot of advantages over the IP formulation.




What we need is a #IP solver, one that counts the number of feasible solutions to an IP. Maybe we could add in a slight random variable to the objective and cut on that?




Duality? Relaxing the constraint between the edge variables and the vertex variables is very reminiscent of duality calculations. This relaxation would also occur in a Lagrange dual problem.




One can sweep the energies. It would be convenient if each energy would have a unique confgiuration , but this will really never be the case.




Can I add a tie breaker constraint to gurobi? I think I can. Then we have a tie breaker constraint of an ordering to the spins. Multiple Objective http://www.gurobi.com/documentation/8.0/refman/specifying_multiple_object.html.




Do I need a ton of secondary objectives in order to make sure I'm at a true corner?




Then I can make a lazy constraint that is a combination of energy and the secondary objective to have the thing iterate over the biggest values.







Quantum = Stat Mech + 1 Dim







No Here we go. Set the pool search mode to opmtial, the poll size to a ton, set the optimality gap to the known gap the the next solution. Boom.




We can use a checkerboard. and relax every other one of the constraints to remove the 0.5 (one per edge). This might be preferable because one wants the linear relaxation of the problem to be as close to the integer problem as possible. We could think of this as checkerboarding the vertex variables, or orient all the edges.




The cluster cut method is independent of the iteration method.




Build monte carlo iterators (could return at some estimate), complete iteration iterators.







Transfer matrix method







A very interesting paper. Wittek and others on SDP




https://arxiv.org/pdf/1808.01275







An argument could be made for LRS being using for the ising model. Enumerates vertices of a polytope. (Hopefully has the ability to start at a low energy?)




https://github.com/JuliaPolyhedra/LRSLib.jl







More infromation - Model Counters




http://beyondnp.org/pages/solvers/model-counters-exact/




The WISH algorithm sort of talks about doing Ising sums.




But I feel like you really need MILP in order to do nonuniform B field sums.







Duality - Loops and boundaries are the same. The loops product is always 1.




You can do some exponential tricks to make




$latex e^{\beta \sigma \sigma} = 1 + b \sigma \sigma$




This is actually a definition of b, not a truncated Taylor expansion.







Nested Dissection






    
    # using JuMP
    using LinearAlgebra
    using Memoize
    print(zeros(3,3) + I)
    
    print(Matrix(I, 3, 3))
    
    
    
    for i in 1:5
    	println(i)
    end
    
    # should do epsilon memoization. Descretize the input field
    
    @memoize function sumising(n, m)
    	if n <= 0 || m <= 0
    		return 0
    	elseif n==1 && m == 1
    		return 1
    	elseif n < m
    		subfact = div(m,2)
    		sumising(n, subfact) + sumising(n, 1)  + sumising(n, m-subfact-1) 
    	else
    		subfact = div(n,2)
    		sumising(subfact, m) + sumising(1, m)  + sumising(n-subfact-1, m) 
    	end
    
    end
    
    println(2^25)
    println(@time sumising(100000,10000000))
    # def isingSum(  ):
    







A start for the coulomb gas.



    
    using LinearAlgebra
    using JuMP
    #using Cbc
    using Ipopt
    #using OSQP
    using TensorOperations
    #using ImageView
    N = 10
    m = Model(solver=IpoptSolver())
    @variable(m, q[1:N,1:N]) # , Bin
    
    x1 =  reshape(range(0,stop=1,length=N), (:,1,1,1))
    y1 =  reshape(range(0,stop=1,length=N), (1,:,1,1))
    x2 =  reshape(range(0,stop=1,length=N), (1,1,:,1))
    y2 =  reshape(range(0,stop=1,length=N), (1,1,1,:))
    
    r2 = (x1 .- x2).^2 .+ (y1 .- y2).^2
    r = sqrt.(r2)
    reps = r .+ I #regularized on the diagonal
    coul = 1. ./ reps
    
    println(coul)
    
    
    E = transpose(reshape(q, :)) * reshape(coul, (N*N, N*N)) * reshape(q, :) + q[1,1]
    
    @objective(m, Min, E)
    
    solve(m)
    
    println(q)
    println(getvalue(q))
    #@tensor begin
    #   E = q[i,j]*coul[i,j,k,l]*q[k,l]
    #end
    
    
    #for x in 1:N
    #	for y in 1:N
    #    	@objective(m, Max, #
    #	end
    #end
    




placing the fast multipole method internal to the model may help it significantly (in terms of sparsity). Memoization is discretized according to some error bound.







LattE. I one of the few #P solvers I know of. There are some others over at Beyond NP. There are ZDD counters. There are Sharp SAT solvers. I think Sharp SAT is hard because SAT is hard, not really because there can be a ton of solutions. Generating function based. One monomial per lattice point. If you have such an expansion, replacing every variable with 1 will add up all the lattice points. Largest monomial can be used to find integer maximization.




Generating function is already what we're trying to do though? z -> e^-betaJ. Ising generating function. If we use energy bounds to discretize into T/10 segments for given interaction boundary. We are using our (hopefully) ability to describe weird linear regions.









## # Convex Landau Ginzburg







x = np.linspace(0,1,100).reshape((-1,1))  
y = np.linspace(0,1,100).reshape((1,-1))







row = np.zeros(100)  
row[0] = -2  
row[1] = 1  
col = row  
K = np.toeplitz(row, col)  
K2 = np.kron(np.eye(100), K) + np.kron(K, np.eye(100))







def V(phi):  
a = 1 # The setpoint of the field  
V1 = (phi[:,0] - a) #(phi - a)**2  
V2 = -(phi[:,0] + a)  
V3 = (phi[:,1] - a) #(phi - a)**2  
V4 = -(phi[:,1] + a)  
V5 = 0 # give slight slope for degenracy breaking  
return np.max(V1, V2, V3, V4, V5)







min (del phi**2 + V)  
V > V1  
V > V2  
.. etc







It is a QP.







Because we do not penalize the hump in the middle, it may spend more time in there than necessary, vortices will tend to delocalize. But sharps corners tend to collect solutions.







Using abs(del phi) it is an lp







min K x + Ky + V







s.t.







del phi < K







del phi > -K







Can either use linear approximations or ... Maybe you can't use LP for norm? It is convex though. Or tesselated norm approximating circles (polygons). Or l1, which does break rotational symmetry.







nonlinear sigma model -> Quadratic constraint QP. if we relax the equality to inequality. It is a reasonable heurstic.







Nonlinear permittivty model -- applications to magnetic problems? two options, f(del phi) where f is convex or del phi dot eps(del phi) which is more correct I believe? (Energy is actually H dot B when you get down to it.. or is it \int H dB). Similarly I think that a diode network is convex.







So there are options. What about Chern-Simons, Yang Mills? Do these have an interesting convex relaxation?  
Navier Stokes?  
Other nonlinear field theories?







XY model. The cuteness of the XY model lies in the MANY minima. That leads me to think there isn't much hope there. One could restrict to 0 to 2 pi. But the potential ias still almost maximally nonconvex. Ok. But again, relaxing the xy model to enclose the bulk of the circle rather than just the rim gives you the lndau-gnizburg equation with infinite walls. QCQP







Approximation of electron specturm with abs. Useful in bosonization. Or the 2d wedge cone in the 2d extensions.







Quantization: Maybe this is useful. However quantum must consider ALL minima, not just the global minima, Hence the convex relaxation is taking the approximation that the other minima are dominated. Quantum is forall (exhaustive search, universal), classical is exists (existential, search).







H = (H0, V)







An extension to a larger class of lie groups







Udag U - I = 0







Relax to Udag U - I < 0







Also may want U > 0 as an approximation of the S part of SU(N).







This is either a matrix inequality or an elementwise inequality.







This is an extension of the idea of taking e^itheta to the filled in unit circle. And of taking the unit ball for the nonlinzar sigma.







Consider Lattice Yang Mills. The Hamiltonian consists of loop terms for every face $latex trUUUU$. This might be a posynomial under sufficient restrictions which would suggest the methods of geometric programming. This is a stretch. The basic trick of geometric programming is to rewrite variables as exponential of new variables, which does feel physicsy, converting from the U form to the A (vector potential) form of the problem. It would be nice to come up with some convex relaxation that is useful.







Consider Chern Simons (Not really very good lattice versions).







Supposing that a LP ends up on a corner, We can write down the steepest descent approximation to the problem.







Ax >= b will have exactly N constraints satisfied. Use this subset as a basis trasnfomation







s = Ax-b







e^(-cs)dx, s>0







The solution is







e^{-cA^{-1}b}/ (detA)/\prod_i (A^{-1}c)_i







Maybe using ordinary steepest descent with gaussians on Barrier method will work.







Summarize all the inequality constraints into a single barrier function $latex B = \sum_i \ln (\phi_i) $. Perform optimization of H +tB. The parameter t is sort of a smoothing parameter. Once you find the optimumm, use the smooth constraint steepest descent method. Put only the linear approximation of H in the exponent and use the hessian of the Barrier function to compute the appropriate volume. But this is under the assumption that we really are smashing into the barrier?







Now if there is a degeneracy, we need to count that separate. And degeneracy is exactly the special case we will shoot for since it is closest to the nonconvex problem.







In a degenerate situation, we need to compute the volume of the object that is degenerate. This is apparently a hard problem (if one assumes an oracle model for set membership, which is questionable we do have the choice of introspective power)? Does this suggest a quantum computer would be good at this problem? Maybe it isn't as bad as I fear, since the kinetic energy term could break degeneracies.







For a smooth constraint getting saturated, we need to transform the coordinates perpendicular to the normal and integrate the spheres surroundign the gradient of the constraint.







Another thought: rho_2 is low rank for superconductor or low rank plus diagonal (correspond to free electrons). Perhaps using the l1 heurstic might make this problem more tractable. Standard Trace and positive semidefintie constraint hold since a density matrix. Antisymmettry is treatable as a linear constraint. There is something off here. I can't remeber what the problem is with this approach.







Another interesting theory is |phi_i - phi_{i+1}| < eps. Sort of like a rope of chain links that are free to move until they contact their neighbor. Should act approximately like the more ordinary |\grad\phi|^2







Why does physics use so many quadratic forms?







  1. They are solvable and manipulable. We choose to use easy to use models.
  2. We choose to look at cases where physics is smooth and continuous, therefore we can approximate functions locally to quadratic forms. Local approximations might be very good to across huge scales.
  3. God prefers them.






But there is a saying by Rockefellar that the big barrier between solubility and insolubility is not linear to nonlinear, but from convex to non-convex.







So what pieces of physics could benefit from this?







Already contact physics uses convex optimization type things. The ability to add inequality constraints is useful to avoid going into walls. It is one perspective on how collision in physics engines is treated.







But we can also consider convex Hamiltonians and Lagrangians.







For classical nonlinear field theory, there are a couple of interesting examples. Permittivity is fairly nonlinear in physically reasonable situations. The Landau-Ginzburg equation can be relaxed to use the convex hull of the quartic potential and that may give some interesting results. This might reflect the situation at the critical point, where the bottom of the well is about to invert into the Mexican hat. What it does is allows the field to be happy at the zero value so it can't get all tangled up. (The tangling is part of what makes it all interesting though. The inability of the field to go to zero because of the energetic barrier is what makes supercurrents persist.)







I conjecture that for statistical physics and maybe quantum physics, convex Lagrangian are basically ones where steepest descent should work pretty well. There are no local minima. The quantum case is more questionable, since now we're really talking stationary phase, and maxima and stationary points also exist. It might all still be ok. Convex functions can't have stationary points I don.t think.







Here's another interesting example. The classical Ising model can be formulated as a mixed integer linear program. Define $latex q_{ij} = s_i \and s_j$ where all variables are binary. Then add constraints .







The XOR that appears from spin alignment (aligned is a different energy than unaligned) can be done with $latex x_i + x_j - 2 x_i \cdot x_j$ .







Similarly, the coulomb gas is a natural mixed integer program. Imagine a network of charges that are constrained to be integers $latex \in {-100,100}$.







There will be an interaction energy = $latex \sum V(x_i-x_j) Q_i Q_j$ and an external potential $latex \sum U(x_i)Q_i $







Then again using this squaring trick you can replace the whole thing with a linear program.







Wait. No you can't. Not exactly the same anyhow. Maybe you could introduce a binary exapnsion for Q and a binary expansions for QQ?







The integer constraint is sufficiently nonlinear that you can simulate squares, or really you don't actually need squares.







One wonders how much it hurts to remove the integer constraint?







During a branch and bound or cutting plane algorithm, instead of selecting the best branch, one should sum the result of both branches.







How well does this work for 1D and 2D ising models, for which we have exact solutions?







How much does removing the integer restriction hurt?







One wonders, the coulomb gas is intimately connected to the XY-model. Does this give a leg into that?







## Wavelet and multipole







The coulomb field is not good for observing things. It tends to hide the details. Once way to see this is that the Fourier transform is $latex \frac{1}{k^2}$. This means that the high wavelength detail in the charge density gets suppressed by a polynomial factor in the field. This is similar to a similar property of the Helmholtz equations $latex \frac{1}{k^2-\k_0^2}$. If the detail k is below the wavelength this is dominated by the $latex k_0$ term.







The fast multipole method uses the fact that the coulomb field obscures things by allowing you to make a hierarchical summation of the .







The wavelet transform also makes a hierarchical summation of a vector, by separating into a hierarchy of localized details. The wavelet transform is also fast, $latex n \ln (n)$ like the FFT.







The discretized Laplace equation is already solvable by FFT. However, we already know the answer. Also we don't







So it's not crazy that we should. be able to use the wavelet transform. Usually we don't because the fast multipole method is used on a collection of particles that we store with an array of their positions. We don't discretize the domain.







The secret purpose of this is to understand OPE and to evaluate coulomb integrals fast in annihilation and creation operator formalism.



