---
author: philzook58
comments: true
date: 2019-12-02 15:44:11+00:00
layout: post
link: https://www.philipzucker.com/?p=1723
published: false
slug: 'Lens as Bidirectional Control Flow : Dynamics Programming, Games, and Gauss-Seidel'
title: 'Lens as Bidirectional Control Flow : Dynamics Programming, Games, and Gauss-Seidel'
wordpress_id: 1723
---




  * Jules Hedges Thesis [http://www.cs.ox.ac.uk/people/julian.hedges/papers/Thesis.pdf](http://www.cs.ox.ac.uk/people/julian.hedges/papers/Thesis.pdf)
  * [https://www.cs.cmu.edu/~sandholm/cs15-892F13/algorithmic-game-theory.pdf](https://www.cs.cmu.edu/~sandholm/cs15-892F13/algorithmic-game-theory.pdf) vazirani algorithmic game theory






algorithmc game theory. Lemke Howson algorithm







extensive form games. Normal form games. mixed strategies.







Pursuit evasion games. Differential games. Missiles chasing planes. Mice escaping cats.







multi agent control







distribruted control







[https://en.wikipedia.org/wiki/Winning_Ways_for_your_Mathematical_Plays](https://en.wikipedia.org/wiki/Winning_Ways_for_your_Mathematical_Plays)







Mathematical games. combinatorial games. The game of Nim has something to do with surreal numbers and the terminatiion of grobner bases?







[https://www.math.usm.edu/perry/old_classes/mat423fa16/Notes1.pdf](https://www.math.usm.edu/perry/old_classes/mat423fa16/Notes1.pdf)







[https://www.math.usm.edu/perry/](https://www.math.usm.edu/perry/) Really interesting guy. Lots of cool stuff on games and grobner bases







[https://www.coursera.org/learn/game-theory-1/home/info](https://www.coursera.org/learn/game-theory-1/home/info) game theory course







Tim roughgarden - algorithmic game theory. Algorithmic desgin













Class PPAD - kind of like NP where you know there has to be a solution.







Tirole book and Vazirani book and  Shoham book







Surreal Numbers. John Conway







Robust optimization - Boyd's website. Convex Concave optimization - Guarantees a single saddle point basically. So it probably is just convex optimization in disguise [https://web.stanford.edu/class/ee364b/lectures/robust_slides.pdf](https://web.stanford.edu/class/ee364b/lectures/robust_slides.pdf)  [https://web.stanford.edu/class/ee392o/cvxccv.pdf](https://web.stanford.edu/class/ee392o/cvxccv.pdf)   







convex-concave problems. min-max theorems that order of min max doesn't matter. (strong duality?) saddle point problems. [http://citeseerx.ist.psu.edu/viewdoc/download;jsessionid=4AD7D17C892756BF7832C6B0D9910D21?doi=10.1.1.178.3064&rep=rep1&type=pdf](http://citeseerx.ist.psu.edu/viewdoc/download;jsessionid=4AD7D17C892756BF7832C6B0D9910D21?doi=10.1.1.178.3064&rep=rep1&type=pdf)







The lagrangian itself is a saddle point problem.







[http://www.iasi.cnr.it/aussois/web/home/program/year/2017](http://www.iasi.cnr.it/aussois/web/home/program/year/2017) aussois combinatorial optimization workshop. Interesting













Bilevel optimization - [https://arxiv.org/pdf/1705.06270.pdf](https://arxiv.org/pdf/1705.06270.pdf) review. Interesting.







Minimax dynamic programming. Interesting. I don't see people talking about this in RL much. "Competing" neural networks. Like alpha go in some respects. What about a finite horizon rollout of a known system.







Monte carlo MPC. Just use random rollouts







Stochastic Optimization - stochasitc programming. Online algorithms [https://www.youtube.com/watch?v=yTvNMeTcK4c](https://www.youtube.com/watch?v=yTvNMeTcK4c) The difference between the feedback form of kalman and unrolling it. [https://www.youtube.com/watch?v=p8Y0J4_15Qg](https://www.youtube.com/watch?v=p8Y0J4_15Qg)







Online algorithms give strategies. But we aren't optimizing over strategeies persay.







Linear Complementarity problems. Not clear there are solvers? You can. KKT conditions with inequality constraints often have two variables suppress each otehr. Linear complementarity constraints allow us to turn optimization problems into feasibility problems. The geometrical look is the positive x and y axis only. Yeah, not a convex set. The big M method will allow the fillin of the quadrant. Would a conic formulation. LCP has some discrete combinatoric flavor to it. So does LP. Conic Complementarity problem seems like a natural approximation of MIP. Not sure if less powerful. But it does turn a optimization problem into a a feasibility problem. One could do combinatorial search on which of the pairs to turn on. Complementarity problems are naturally expressed as products. Grobner or SOS technqiues? division might correspond to changing... We can do Foureir motzkin elimination, while reducing with respect to xy. 







skolemizing queries is pretty similar to normalizing games.







Differential Linear games. Non-zero sum. Consider for example two opoonents trying to drive to different locations. They will end up 







parametrized optimization problems







tube mpc https://www.youtube.com/watch?v=iVjuzfP3Jk0








https://www.youtube.com/watch?v=K4w3vHV7CLY&t=1898s








[https://isr.umd.edu/sites/isr.umd.edu/files/slides/Rakovic_Robust.pdf](https://isr.umd.edu/sites/isr.umd.edu/files/slides/Rakovic_Robust.pdf)







The KKT conditions are a form of quantifier elimination forall exists vs min max







tube mpckerrigan. David Mayne. benders decomp?  
zero sum bimatrix games are lp. min max y A x s.t. sum y = 1 sum x = 1. Mixed strategies. Inner guy can be dualized out.







Robust MPC is a similar beast. These thing are very sensitive to the structure of the constraints. Seperable constraints







Linear Complementarity problems ~ MIP?







[https://epubs.siam.org/doi/abs/10.1137/1.9780898719000](https://epubs.siam.org/doi/abs/10.1137/1.9780898719000) book on LCP. LCP seems to be pretty tough







Lemke and Lemke-Howson. Two names for 1 thing or different things? Support enumeration. Oppenent indifference pricniple. Nashpy







[http://www.cs.cmu.edu/~arielpro/15896/schedule.html](http://www.cs.cmu.edu/~arielpro/15896/schedule.html) games and algorithms course. Papadimitrou algo book has chapter on games.







Non-zero sum bimatrix games are not LPs.







LCP let's you directly express KKT conditions  
robust optimization appears to be relatedThere are some extensions there.https://web.stanford.edu/class/ee392o/cvxccv.pdfthis is linked off of boyd semester 2A small slight of hand is trading a forall for a max on the uncertianty  
Interesting. Noise does seem natural to model as a zero sum gameBut the dynamic constraint seems off.maybe one wouldn't care unless you were gonna hit stuff  
https://www2.isye.gatech.edu/~nemirovs/FullBookDec11.pdf







There was some weird stuff saying that using Couenne, a general purpose MINLP solver was working better for LCP? It used a McCormick relaxation of xy = 0.







Nash's theorem - equilibria have to exist. based on Brouwer fixed point somehow







The price of anarchy. 4/3 ratio? Anarachic choosing of something? Flow?







convex concave gamesf(v,u) convex and concave seperately from each others valuesseperable inequality constraints







0 / 1  
u vz  
Bada bing bada boom  
LCPHuh. I could use a MILP solver for QP? That's funny. You can directly express the KKT conditions of u <= Mzv <= M(1-z)







I suppose you could make finding the best vertex into a MIP Ax >= b turn into slack equality we just converted an LP into a MIP Ax + t = b     t <= M(1-z)        sum z = d  
https://support.gurobi.com/hc/en-us/community/posts/360043212072-Can-I-solve-bilevel-optimization-problems-in-Gurobi-







okso MIP => LCP and maybe vice versaLCP is very natural for contact force problems. The contact force and the distance to a constraint are complementary variables







going from KKT conditions back to the optimization problem is a kind ofintegration procedure. Not all vector fields are solvable in this way. "convexifying" a problem. Could such a thing be made automatic? 



















* * *







What an optic is is well characterized by the following box







If you have control flow that has a forward pass and a backward pass, something like a lens might be an interesting conceptual fit.







The simplest optic is the isomorphism. It is the un tangled combination of a forward and backward function. It has a kind of simplicity to it.







One example is that of reverse mode differentiation. Reverse mode differentiation makes a forward pass to the end and then traverse back through the computation graph. 







iterative LQR is a combination of a kind of triangular solve on the backward pass and a reverse mode differentiation computation.













Traversals allow game tree search?







The lens type allows for sharing.







The different vaireties of lens







Iterative LQR







Block Gauss-Seidel with lensy combinators Dynamic Programming, Lenses, Open games













In order to eventually get access to the solutions, we need to include pieces of literal lens combinators.







Lens (V2 D, (V2 D, a)) (V2 D, a)







We could do evertything in an ST monad also







Lens give the canonical example of a bidirectional computation. The general pattern is to package up mutiple functions into a single data wrapper. Then some get composed in one direction and some in the opposite. This has a categorical or point-free flavor. You can emulate this behavior playing with things that feel more like values than functions via continuation passing transformation. But there is still this spooky polymorphic r connecting the two sides, and you do lose something thinking about just (x, x-> r) in isloation from the rest of the function







You can't really split id :: forall a. a -> a into just looking at `a`.  








Lens = x -> (y, y ->x) = (x -> (y, (x -> r) -> y -> r) = forall r. (x, x -> r) -> (y, y -> r) 







There are a number of places where a forward backwards kind of iteration scheme occurs. One, it is just kind of plausible.







CEGAR







iLQR







Gauss-Seidel







ADMM







Games







Value iteration







par is a place for genuine parallelism







Imperative programming is desgined to mimic the machine. Functional programming reflects mathemtics and logic more. This goes all the way back to the Turing Machine programming language and the Lambda Calculus of Church.







The good place to insert abstraction is at the block level. At this level, you find ways to compose highly optimized kernels or subroutines.







ADMM works like this. Coarse grain of parallelism works like this too. Fine grained parallism probably requires lower level code.







A gauss-Seidel solve requires a forward and backward pass







Relations do not have an inherent directionality to them. If there are transitive and reflecixive they do form a category. But it feels weird to put a directionality on the morphism. I suppose that is fine.







However, the Gauss-Seidel solve does put a directionality into all variables. Those that appear earlier in the matrix and those that appear later. This order matters.







Jacobi iteration takes as it's initial assumption that all subproblems are disconnected







Gauss-Seidel takes the approximation that there is a functional relationship of the solutions. This is not much harder to solve than the independent problems, with good dividends







A more symmetric form of the either is Successive over-relaxation













I have at least two forms now







It's not insane to structure the thing using streaming either though. It does make sense to stream the results around until convergence.







Two style. 







  1. Type index the interfaces as small subsets of the entire blob. Then use monadic store the get the result out and store intermediate stuff. Or have a type index tracking internal state
  2. Have the types be the entirety of the vector space and then there is a lens like operation of zooming in. Questions: Prisms. Traversals?






What makes a Lens different from a category? Well, 4 type parameters. Streams can also be bidirectional but are not lenses? 







The 4 type parameters again have some meaning here. x y dx dy for AD lens. In this case is is fullspace subspace next_fulspace next_subspace. They separate out iteration. 







----







I was reading through some of the work of Jules Hedges because it seemed neat.  https://julesh.com/  https://julesh.com/publications/







I don't really understand what he is talking about (I don't have much background in game theory, and only a street-fighting amount of category theory), but in broad strokes it smells to me like the principles of dynamic programming.







Dynamic programming is a term to describe two very different feeling things.







In an algorithms course, dynamics programming is a method of algorithm design that combines recursion with memoization. Problems can be divided into simpler sub problems, but too many sub problems to be solvable by divide and conquer. However, if you remember the results of a previous problem.







The other arena that has something called dynamic programming is the field of optimal control. Reinforcement learning is roughly the same as approximate dynamic programming / neuro dynamic programming. Reinforcement learning has the connotation of being mostly sample driven, whereas optimal control has the connotation of having a system described by mathematical laws and using them. This isn't a hard and fast distinction though.







The thing that makes an optimal control problem hard is that it can be good to do something bad now to get dividends later. You don't always want to take greedy moves, you may want strategic moves.







The value function $latex V(s)$ is an abstract interface between the future and the past and to conceive of it is a stroke of genius. You don't need to know anything about the future dynamics or rewards except for how that function evaluates. 







In typical application I am used to seeing a time-invariant problems. The type/size of the state space and action space stay consistent through the entire process. There is no need for this though. The shape of the state space can wildy vary.







Two control processes can occur entirely in parallel. This is a monoidal product for control processes. Monoidal products often has some flavor of parallelism. The tensor product of two linear maps can be done on seperate processors and then recombined afterwards. In quantum mechanics, the tensor product of the two physical processes means that the two systems are entirely non interacting. In Haskell the `(***)` operator is a location where the left and right side of the tuple could be computed in parallel. 







I think the packaging of . The strategy profiles $latex \Sigma$ are the space of possible controllers. This may be linear feedback, in which case the space is the coefficients of the feedback matrix $latex u = K x$. Or it may be a neural network, in which case the space is the possible value of weights of the network.







Game theory is connected to these topics. To talk of literal games, the Alpha zero algorithm uses dynamic programming principles to improve it's tree search of moves and appears to be competitive/state of the art for several games. 







[https://en.wikipedia.org/wiki/Game_theory](https://en.wikipedia.org/wiki/Game_theory)







A control problem can have multiple players. There can be literally different controllers working to achieve the same goals or contradictory goals. The environment itself / perturbations of the equations of motion can be usefully viewed adversarily. If you want to phrase the robustness problem of optimal control, it takes the form of a long sequence of alternating existential and universal quantifiers. Does there exist a command now such that for all perturbations there will exist a move the next time step such that forall perturbations then there will exist a move in the subsequent timestep ... and so on.







$latex \exists u_t \forall p_t \exists u_{t+1} \forall p_{t+1} ...S({x_t}, u_{t}) $







The proposition S could correspond to being in the goal at the final time, or that no bad condition like tipping over can happen, etc.







I am a little unconvinced that we should call anything with a backwards and forward sense to it a lens.







Continuations give the control flow the ability to teleport. The Lens-like construction of backwards and forwards passes requires all information to be backpropagated the way it came. In a sense, it is more point-free. The continuation gives a name to that point of the control flow, like how a variable name gives a name to that piece of data that you can refer to non locally. The point-free/category style requires explicit piping and duplication of anything you need to get somewhere. 







There is a simple algorithm for computing the optimal control of a system with linear dynamics $latex x_{t+1}=Ax_{t}+Bu{t}$ and quadratic reward function called the LQR controller. Optimizing this system reduces to a problem of linear algebra. The dynamic nature of the problem means the matrices involved are block tridiagonal.







I am going to work with the LQR system because it is the simplest one and I don't yet know exactly how to generalize. This doesn't quite match Jules' picture of open games because it is passing back both values and strategies themselves, whereas he left strategies outside the fray.







In this specialized case, parallel systems are given by adding their cost functions and taking the direct sum $latex \oplus$ of their dynamics matrices $latex \begin{bmatrix} A_1 & 0 \\ 0 \\ A_2 \end{bmatrix}$. The unit for this operation is a zero dimensional system (one that doesn't exist at all).







type Agent o a v v' = Lens o a v v'







If we just wanted to compute the action and the subsequent reward, there is no need for the backwards pass lens-like structure. We can compose functions like







type Controller = (o, r) -> (a,r')







type Dynamics = (o,a) -> o'







There is a question of whether it is more sensible to ascribe the reward to the agent or the environment. Does the world have intrinsic reward or is something good only because of how an agent feels about it? Kind of philosophical no? For consistency, we can just carry the reward along







This forward form vs backward form feels to me similar to forward mode vs reverse mode automatic differentiation, but my mind is rotten with that, so I am not to be trusted.







It is not difficult to see that this structure can be extended slightly to the nonlinear case to create an iterative LR controller. By making the dynamics automatically differentiable, and sharing that information to the backwards pass, we extend the controller to something that could plausibly work in the nonlinear setting. 







This is a little unsatisfying to me because I am a collocation man, not a shooting method man. 













In order to build a tree search in this way, we may need to insert a nondeterminism monad somewhere. How does that work?. List of all choices. and backwards pass converts lsit to single one by taking the min or max. aybe. Could you implement alpha beta pruning this way?







Since I've already been discussing how you can work automatic differentiation into a Lens-y structure and how to organize fynamic programming in a Len-y structure a natural question to ask is can we build a reinforcement learning system by combining these somehow?







Another thing that may be interesting to explore from this direction is the duality of controllers and filters. For every filter algorithm, there is a strongly similar controller algorithm.







Kalman = LQR







Particle filter = Monte Carlo Tree Search







Viterbi = Tabular Dynamic Programming







? = Neural Reinforcement Learning  




