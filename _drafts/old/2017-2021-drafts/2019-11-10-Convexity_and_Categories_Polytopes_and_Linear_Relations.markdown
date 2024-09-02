---
author: philzook58
comments: true
date: 2019-11-10 17:56:56+00:00
layout: post
link: https://www.philipzucker.com/?p=1596
published: false
slug: Convexity and Categories. Polytopes and Linear Relations
title: Convexity and Categories. Polytopes and Linear Relations
wordpress_id: 1596
---




###

*

Rust? FPGA? MLTon? Feldspar? Copilot?

Just as finite relations can be thought of as a set of pairs, linear relations can be though of as a linear subspace of the "input" and "output" thought of as a single vector (their direct sum).

In particular if we stack the vectors like $latex [x y]$, the subspace is the null space of the rectangular matrix $latex [A B] $. The null space is the subspace that gets mapped to 0 by a matrix. Sometimes it is called the kernel.

They can be converted to each other via

One really nice thing is now we always can invert matrices. That's the beauty of going from functions to relations. If a matrix isn't full rank, no biggy.

The VRep is great for projecting out coordinates. We just slice out those pieces of the generators.

Ok, How can we map this back to a problem of interest.

Writing $latex Ax=b$ as a linear relation. This is the canonical problem.

A lot of these are actually affine systems

The SVD is a big hammer and can solve most problems. I suspect there are more specialized routines one could use. The SVD actually makes a lot of sense from a numerical perspective. Numerically, you might want a softer cutoff for what you want to be in the nullspace vs not. A hard 0 is difficult to come by.

[https://github.com/scipy/scipy/blob/v1.3.1/scipy/linalg/decomp_svd.py#L333-L391](https://github.com/scipy/scipy/blob/v1.3.1/scipy/linalg/decomp_svd.py#L333-L391)

scipy has some functions for computing nullspaces and ranges, but they are thin wrappers over the SVD.

    <code>    u, s, vh = svd(A, full_matrices=True)
        M, N = u.shape[0], vh.shape[1]
        if rcond is None:
            rcond = numpy.finfo(s.dtype).eps * max(M, N)
        tol = numpy.amax(s) * rcond
        num = numpy.sum(s > tol, dtype=int)
        Q = vh[num:,:].T.conj()
        return Q</code>

So we could also just store the SVD.

Maybe I should just do this in Haskell. They'll be more receptive.

Linear relations and quadratic optimization / least squares

One of the main reasons least squares is good is because solving least squares lead to linear equations which we know how to handle at scale. The other reason is that it is good for gaussian noise.

We can homogenize a quadratic optimization problem to

One problem with the iterative schur complement technique is that the sub blocks may not be full rank.

The value function is a quadratic form. type V s = [(s,s, Double)]

type Bellman s s' = V s' -> V s

compose

V () -> V s can cap the process.

For iterative LQR, we want to  have a current control input we want to maintain. This was the same issue with neural network too. What I did was build the state to be carried along. Hmm. And the fuel depends on the innards. It isn't composable.

So for a fixed controller.

Quadratic Optimization

Quadratic optimization forms a category very similar to linear relations. When you need to optimize a quadratic form $latex \frac{1}{2}x^t Q x + c x$, you do so by setting the gradient to zero $latex Q x + c = 0$. So optimizing quadratic forms leads to linear relations.

However, the natural definition of composition is slightly different. The way you compose quadratic optimization problems is by adding together their objective functions and minimizing out the interior variables.

$latex (P \cdot Q)(x,z) = \min_y P(x,y) + Q(y,z)$

This operation is performed via a block matrix solve, aka the Schur complement, my favorite thing in all of mathematics. [https://en.wikipedia.org/wiki/Schur_complement](https://en.wikipedia.org/wiki/Schur_complement)

The Schur complement arises when you perform gaussian elimination of a block matrix.

$latex \begin{bmatrix} a & b \\ c & d \end{bmatrix} = LU = $

We only have to be careful of the ordering of our division and multiplication, as matrices famously do not commute.

The Schur complement is the canonical example of building effective systems. Eliminating variables? But it's more than that?

We do not require the matrix be full rank in the schur complement, we only need a least squares solution?

Actually working out the specifics of this gave me a very unpleasant dehydrated train ride. I had no paper.

This minimization is part of a general pattern of composition, where interior variables are destroyed by the application of some binding form. For linear relations, it was the existential quantifier $latex \exists $. For matrices, you destroy the interior indices by summing over them $(AB)_{ik}=\sum_j A_{ij}B_{jk}$ or equivalently $latex \int dy A(x,y)B(y,z)$ for continuous linear operators. $latex min_y$ has a similar character. So does $latex \lambda y$ but I have never seen a composition that works like that? A curious thought.

Because of this addition in the definition of quadratic forms, the overall scaling of a quadratic form matters, whereas it did not for linear relations. $latex Ax=b$ is the same relation as $latex \lambda A x = \lambda b$, but the quadratic form $latex \frac{1}{2}x^t Q x + c x$ is not the same as $latex \frac{1}{2}\lambda x^t Q x + \lambda c x$. It represents their relative weighting.

Quadratic optimization and linear relations can also be combined and still maintain their closed form solutions. This can be achieved by a number of ways. One sort of silly way is to add an infinite penalty to (Ax-b)^2. Another way is the method of lagrange multipliers. A third way is to explicitly project the quadratic form onto the allowable subspace as parametrized by the V-Rep.

I'm still chewing on this one

Other ideas:

Explicit lagrange multiplier inclusion

Cost vectors

### Kalman Filters and LQR controllers Applications

What the hell is the stuff above for? Well, basically it's a curious linear algebra DSL. And linear algebra has a ton of uses

* Least Squares Fitting
* Solving discretized PDEs
* Quantum Mechanics (I guess that's part of the above)
* Geometry stuff
* Analysis of Linear Dynamical Systems
* Transition Matrices
* Circuits
* Signal Processing

In principle, I think all of these could be manipulated in the language of linear relation algebra.

A linear dynamical system is a linear function $latex x_{t+1} = Ax_t+b$, but it can also be extended with an unknown input u. Then this relation becomes the reachability/controllability relation of the system.[https://en.wikipedia.org/wiki/Controllability](https://en.wikipedia.org/wiki/Controllability) . The above form brings linear controllability analysis feel quite similar to polyhedral reachability analysis.

My original motivation for linear relations was as a simplification of convex polyhedral relations. I then remember the work on categorical linear relations

See Baez and _, and Baez and Fong for some interesting usage for linear control and circuits. Are circuits best served by the linear relation or the quadratic optimization standpoint?

Feedback diagrams profit from the non-directionality of relations.

To me the above proceedings are the essence of linear Kalman filters and LQR controllers. These are controllers and estimators for linear dynamical systems (so they have linear relational constraints on the dynamics) with quadratic cost functions corresponding to some control objective, or some observation fitting metric.

To my mind these are essentially the same problem (via duality) so I'll just refer to the LQR controller. Are they though?

Now, the Kalman filter as usually presented is a 1-step update equation.

Infinite time horizon.

The finite window Kalman filter can be profitably considered

Look at the wikipedia page. Look at that sludge.

Circuits as string diagrams. I should do a simple circuit.

wittington? bridge.

Network circuits are a particular style of circuit that is very compositional. There are alternative representations for different purposes. Some compose via matrix composition.

Linear signal Diagrams

Kalman Filters

#### Relation Algebra for mixed integer programming

Logical relations over linear inequalities is a problem domain that is decidable. It has long known algorithms to solve queries, it just can be rather inefficient.

Polytopes are sets. They are sets over multiple variables, so you can also consider them as relations is you partition the variables.

The graphs of convex optimization problems are convex sets. The two are equivalent languages.

Likewise convex sets can be thought of as a slice of convex cones. This is the standard correspondence between homogenous coordinates and regular coordinates.

The composition of two relations is an implied existential operator. When you run a linear program it proves an existential by finding a solution that actually demonstrates the existential.

Relations are a category. Convex Relations are a subcategory of that with excellent computational properties.

Like so many things, polytopes can be thought of as a category.

So the meet /\ and composition operator are easy enough

The intersection of convex shapes is convex and the convex hull of convex shapes is convex, but the union may not be. Howver, the union is reprsentable in the framework of mixed integer programming. YOu can use a discrete variable to control which region you're in. The branch and bound solution process then uses convex relaxations to help find a solution.

Actually formulating depends on your representation of the convex sets. The H-representation describes your set via inequalities. The V-Rep describes your set as a convex combination of the corners. The v rep makes it easy.

Conversion from H-Rep to V-Rep and vice versa is actually a very difficult problem in high dimensions.

This gives a join operator that actually represents union.

We're in a cartesian category. There are natural polytopes and polytopal combinators that represent par, dup, fst, snd, fan. Dually, we also have a force equality relation (a,a) -> a. It isn't clear to me that cocartesian makes much sense

We can also embed boolean relations

We can make relational queries like R <= Q. This requires forall x y. R x y -> Q x y. We can reduce the implication to the classical form not () /\ ()

Negation of a relation is taking the complement of that region. Integer variables remain integer variables, bools bool. This is a little troublesome, because the boundaries of the shapes are filled in. We want open sets instead of closed ones now. Perhaps there is a way around this. We can use an epsilon constant or perhaps variable to ask for a seperation.

I have a vague feeling that using homogenous coordinates can work.

[https://web.stanford.edu/class/ee364a/lectures/geom.pdf](https://web.stanford.edu/class/ee364a/lectures/geom.pdf) slide 8-8

[https://math.stackexchange.com/questions/2673917/can-a-linear-program-have-strict-inequalities/3392514#3392514](https://math.stackexchange.com/questions/2673917/can-a-linear-program-have-strict-inequalities/3392514#3392514)

f(x) < g(x) => exists eps > 0 s.t. f(x) <= g(x) + eps

We can recursively compile a relation expression into a mixed integer program. We can use relation algebra also to manipulate this expression at a high algebraic level.

Halfplanes are a base case that is most easily complementable. The opposite halfplane is just the other halfplane.

The Gunther Schmidt book made me realize how useful relation negation is. You can encode relational division, which holds a universal quantification. This makes sense because classically, forall x  P(x)= not (exists x (not P(x)). If you have a query with foralls, you can convert it into just using exists and negation.

Relational division is a way of formulating optimization problems. This is related perhaps to the fact that you can turn an optimization problem into a feasibility problem.

Mixed integer programming is a good paradigm because it meets halfway both problem formulation and a decent algorithm to solve. The problem is defined in such a way that branch and bound is immediately applicable.

I probably need to convert h-rep to v-rep to do this.

Selector functions.

The ability to

argmax_{x \in S}

Is a representation of S. That is the Escardo olivera, Hedges philosophy.

(Ord r => x -> r) -> x

Under the assumption that x -> r has the convex property.

COuld replace with a differtntable function to boost. Or a hessianable functions. Or perhaps a proximal something?

Coordinate descent, Nelson Mead. Others are derivative free. Finite difference newton.

Binary search on coordinates. decreasing size. Internally we can even keep track of current step size.

combinators: Can we intersect? Union?

Can give the function a line (x -> R). will find location line kisses envelope.

Can iterate, giving distance to point in other set. (x-x_1)**2. Should find points closer and cloer together until they are the same or as disjoint. Then verify after the fact that both = 0.

Convexity is not closed under union, but could hand function off to both and take best one => Finite union is perfectly solvable.

Related ::

argmaxlinear :: (LinearFunc) -> x

argmax quadratic :: QuadFun -> x

argmaxdiffenretiable ::

argmaxhessianable ::

Seems like QuadFun could get you very far. Includes Lin fun as special case. Includes other functions as epigraphs.

in epigraph formulation, this might be all we need. Using linear cost in y gives the cost of the function.

(Line -> R) -> Line

Given line let's you find extremal point.

Given point, let's you find a line?

given cost of line, finds best line.

(X -> R) -> Line

HalfSpace convex set ~ Line.

Consider Argmax (Ax-b)^2

((a,a) -> Q () )-> Q a

dup :: a -> Q (a,a) -- self outer product

ContT () Q a. Double negation translation. Since ContT is a monad (Dag Dag)^2 = (Dag Dag)

Dag a = a -> Q ()

ContT () Q a = (a -> Q () ) -> Q ()

(a -> Q()) -> Q() can enclose a faster data strcutrem mapWithIndex omega

(a -> R) -> R

((a -> R) -> R) -> R as a dual? Basically ought to hand a (a -> R) function into the input. So this function contains (a -> R).

lift :: (a -> R) -> ((a -> R) -> R) -> R

lift f = \g -> (g f)

( ((a -> R) -> R) -> R) -> R) -> (a -> R) -> R

iso f = \g -> f (lift g)

deltafunction = Eq a => ((a,a) -> R) -> R

\(x,y) -> if x == y then 1 else 0 :: (a,a) -> R

fmap (f . dup) basis :: ((a,a) -> R) -> R

-- not that inefficient. Basically the basis thing in disguise though

lift deltafunction

dag = dot

The selection function method isn't really all that disimilar from the projector method. Maybe a superset. If you hand it a quadratic function that has .

Quadratic function over boht the primal and dual. Allows for linearly constrained maximization.

Quad (x,l) -> ((x, l1),l2)

Can also return l2 perhaps, although redudnant. You can get l2 by plugging in x solution to gradient of QaudFun, because gradients need to match.

Line coordinates

---

ADMM as gauss seidel

Part of the proximal method is adding in quadratic terms that don't matter because the variables in them are constrained to be equal to 0. However, upon loosening, they help. The also give you wiggle room to make the matrices well conditioned. For some \rho D+\rho becomes well conditioned.

$latex \begin{bmatrix}D+\rho&-\rho&I\\-\rho & A + \rho & -I \\ I & -I & \frac{1}{\rho} - \frac{1}{\rho} \end{bmatrix}$

$latex \begin{bmatrix}

D+\rho &-\rho & I \\

-\rho & A + \rho & -I \\

I & -I & \frac{1}{\rho} - \frac{1}{\rho}

\end{bmatrix}$

The diagonal term on the Lagrange was more surprising.

Gauss-Seidel splits the matrix into 3 parts. A diagonal, strictly upper triangular, and strictly low triangular

(L + D + U)x = b

(L+D)x = b - Ux

How to talk about iterative methods in the minimization language. We can replicate the system many times

$latex xQx \rightarrow \sum_n x_n Q x_n$

But we can also add non block diagonal terms, which hopefully correspond to . Also we may screw with the endpoints, maybe demanding that x_0 = an initial guess.

This doesn't seem to work. I'm not getting an iteration method out of this. x_n needs to not care about x_n+1, which by some kind of reciprocity is always the case in minimization.

It may be that it is an iterated game of maximizing lagrange multipliers and minimzation. Then the minimization/maximization can't be reordered in general. Although it can for convex problems?

Moreau decomposition - the connection of proximal to dual. A proximal operator of the dual function is connected to the primal. In the way that proximal operators extend projection, this extends the breaking up of a space into two disjoint subspaces.

Moreau envelopes - connection of proximal methods to gradient descent.

Seems to me you could also transmit the hessian between problems to get a higher order method (or approximation of the hessian). Corresponds to schur complement technique. (iterated)

* * *

Gauss Seidel iteration

Extremes are interesting things to examine. If we go all in on the lagrange mutiplier thing, we can use them to even form composition of two quadratic functions. Then each morphism becomes a diagonal block. And there are block identity matrix only on the off diagonals (neagtive and positive). We can prefactor the indivdual diagonal blocks (they can take care of their own mess. Hopefully this will extend to general convex functions). Then we can apply The L^-1 diagonal matrix. This will turn the off diagonal into L^-1 and the on diagonal to R. Then we can gauss seidel the thing splitting along the diagonal. The forward pass copies things along, and the backwards pass solves.

Sort of eta equivalence is there theorem the a constraint x = x' is the same diff as just replacing. beta? f . id = f

We make the interface between pieces more unifrom.

It is fruiful to consider the simpler case of quadratic problems, rather than the general setting. Tehre are more ideas floating around there.

Guass elimination ~ Grobner ~ Foureir Motzkin ~ . How does one formalize/get a handle on this? Is category theory the answer?

Gauss Seidel ~ ADMM ~ ? How does one formalize this?

Scans and folds and reduce of convex problems.

The langrange mutiplier boys are not explcitily resolvable. This is kind of weird. Why are lagrange mutipliers not totally symmetric with primal? They often have to come in linearly? Is the form g(y)f(x) acceptable?

Duality. We keep the lagrange multiplier hidden in the interior. Can we expose them?

dual :: QuadCat a b -> DQuadCat a' b'

adds on the single identity matrix?

Can I make legit parallelism part of the semantics. every application of par calls into some haskell parallelism construct

( ) === (ident n ||| 0) === A

fromBlocks [[A,]

<https://en.wikipedia.org/wiki/Symmetric_successive_over-relaxation>

<https://en.wikipedia.org/wiki/Successive_over-relaxation>

related to rhicardson extrapolation?

Where is sharing in forward and backward pass? May be needed by a shared hessian on backward pass.

stationary and non stationary

compositional iterative methods.

rachford-clenshaw splitting. In ADMM slides he talks about how operator splitting comes from matrix solves

<https://www-users.cs.umn.edu/~saad/IterMethBook_2ndEd.pdf>

Once again, all kinds of goodies in the matrix world

Krylov? Not sure how to work with that

Chapter on parallel iterative methods seems peritent. They start working at the block level, which is one level closer to black box

Block Jacob.

Graph coloring of matrix to find colorability. That's interesting.

Frontal methods?

In a finite element graph, our catgoery is kind of describing the mesh itself.

This is a traced mondoial category. We can induce an eqaulity row that will trace out the front and back!

V cool.

(a,b) (a,c) -> b c

This is true feedback like an op-amp

(a,b) -> (c,d)

We can work in a way such that we carry along the entire matrix wer'e building, or a recording dsl, or we can work with a direct functional representation of the iteration process. If we do the last one, it has the flavor of a lens or iso. Something bidirectional. Similar to how functional reseptnations of matrix application, there are efficient versions of some imoportant functions, like id.

You can't invert or even transpose easily linear maps.

The lens pattern is a way to generically have forward and backward passes. It is a control structure rather than getters and setters.

Getters and setters fall into this class of control structures.

The standard functional way of achieving weird program flow is conitnuations.

  1. we can convert a lens into a continuation form. See my comment on my first lens post, morel ike what Conal Elliott was thinking. It may be that this is the better form of an AD-Lens.

  2. Continuations are fishy. I think General continuations are more powerful than what we want here.

Yoneda lemma says that (a -> b) = forall r. (a -> r) -> (b -> r)

natural transformation between Reader and Identity.

LiquidHaskell annotations proving monotonicity of the operators? That'd be a hell of a thing.

The Lens could hold morphisms from arbitrary category rather than just ->.

Then the lens compostional structur is describing what it means to be gauss seidel.

There is something still wonky in regards to duality

We need to pass around an effective linear compoennt of the objective if we want to . This coukd make sense from a duality persepctive. The linear terms can come from constants in objective, or from langrange multipliers.

So we could consider the lft and right hand size as variables.

Inject literals with L () a.

We need literals

2x2 matrices = QuadCat Double Double

\x -> (w - d * y / c, \y -> ). Maybe we could do a damped averaging.

Successive over relaxation.

Sometiems I have wanted the ability to swap the left and right hand side.

The matrix data structure and how to embed into that is important to undersatdn what we're doing.

But we're suggesting an algoirthmic / functional form of a matrix.

x -> (x,x)

(x,x) -> x -- x + y == z constraint

If we add inifnity into our matirces, we get equality constraints. One way to think about it

We have a natrual trace. x == x

Do we have a natural way to flip stuff into the input and output. They aren't really that different from the matrix perspective.

I think we might be able to do it with trace and dup?

From a guass seidel perspective, We are chaning the dpendence ordering.

Currying?

There are some natural L a (), L (a,a) (), L () a. L () (a,a). Cups caps and endings. similae to trace. Equality.

Domain Decomposition.

What we're doing is actually kind of a cool way to build problems.

Red Black coloring

We're living in schur land kind of. At a level of abstraction where you can kind of see how different domains are connected. Parallel convex programming and parallel linear problem solves.

The monodal par exposes possible paralleliism pretty directly

Try to work with a laplcian example. ;) It's my favorite boy

Consider a morphism that is a single layer of the laplacian grid.

We're building up meshes catgoerically.

We could reinteret the same thing into building the laplacian matrix or into building the graph.

Lanczos. The duals really do start to feel like the linear duals. Current and voltage.

Baez has been talking circuits

stiff circuits are often thought of with an input output realtion, even though it is bidriectional

Fong and baez compositional circuits

<https://arxiv.org/abs/1504.05625>

Baez and Erbele <https://arxiv.org/abs/1405.6881>

categoures for control. FinRel.

QuadMin. A lsightly different perspective on FinRel. Maybe same diff though? Maybe... looking at the minimzation problem is typically more elegant.

What makes my perspective different:

  1. I know way less about catgoeries

  2. way more applicatipn focused. Like I actually care what is underneath the string diagrams. I care about constructivity and algorithms

  3. needs to be Haskell implementation.

  4. I'm starting from convex control not linear control. I might know more about actual engineering concerns.

---

Jules Hedges <https://arxiv.org/pdf/1711.07059.pdf>

Games as categories

Open Games

Convex programming is a game in a way between the primal and dual player. (Right?) The lagrangian forms a saddle point

play and coplay. Observation -> Action is play = policy

Action x reward -> Value of observation. Bellman update?

Or is this just the passback of the reward?

Coninutations are arbitrarily powerful. You can backjump to anywhere

The lens structure means you need to traverse back the way you came.

argmax and max of both binding forms. Jules seems to suggest there is a way of thinking about them in which they are unified

The daulity of observation and control of brain beckman

In dynamic programming /RL/ Hamilont Jacobi, there are the notions of finding optimal value functions, but also just evaluating the current vlaue function according to some policy.

One can consider a monoidal product of indendpent dynamic programming systems. That makes some sense.

The composition of convex programs is less clear. min min min? argmin? Proximal .

Bilevel optimization or whatecver is nasty world to be in. But games are nasty.

Given a y vector, the proxmial algorithm picks the best x vector. given two x vectors, the y player picks the worst y?

Is the dual player on the backwards pass? Or is the dual player another composed morphism

A function that returns a list is a relation.

The level that things make sense is that you want biedrectional pipes sometimes. So pack together functions that are going to compsoe in opposite ways. Sometimes there is a noticeable forward. You want that input for both sides of the pipe.

Pipes, conduit, machines

For iteration, I feel like I want a stateful lens.

QuadFun (a,(x,x')) where tuple implies direct sum spaces.

QaudFun x x' where we aribtrarily put half of the variables in the left and right

Clearly we can flip these morphisms and we can reassociate Q x (a,b) = Q (x,a) b.

There is the duality of negating the objective and chanigng min to max.

min becomes function compositon. min :: (b -> c) -> (a -> b) -> (a -> c)

For cvxpy, I've been tempted to use a context monad, that holds all the constraints alongisde an exposed variable. Z2 Int, Cvx Int. Cvx Bool etc.

This is similar to John Wielgey's category of Z3. It might be a kliesli category for this monad.

We could choose to not actually do the minimzation ourselves, but just propgate a record of the program through and pass it off to a solver.

Then compiosition is given by partial minimization. min min min min = min over all. This fits with the stationary phase of linear operations, and with the action principle.

The schur complement when it isn't doable (A is not invertible) results in an equality constrained minimization problem. We can't solve equality constrained minization via unpacking lagrange multipliers. We need to divide the equality constraint alongside thew quadratic cost. Allowing infinity dual numbers is another way of discussing this that might be elegant. In principle, putting inifinites in the matrix allows to make constraints happen, but it would be highly ill conditioned if we did it literally.

data DSum a b =

newtype QuadFun a b = QuadFun HMatrix

QuadFun a b = QuadFun { mat :: , vec ::, constant ::, constMat ::, constraintVec :: }

QuadFun a b ~ BlockMat. Then the operations don't feel as trivial, flipping actually will trasnpose and swap matrices.

QuadFun a b = aa :: bb :: ab :: ba ::, b :: , a::, scalar :: cb :: ca :: Matrix c :: Vector

BlockMatrix = aa bb

$latex xQx + bx + c s.t. Ax=d $

Using sharing between the foreward pass and the backward pass, we could share the differential dynamics to the backward pass.

data BMatrix where

BMatrix :: BMatrix x x -> BMatrix x y -> BMatrix y x -> BMatrix y y -> Bmatrix (x,y) (x,y)

VStack :: BMatrix x y -> BMatrix z y -> BMatrix (x,z) y

HStack :: BMatrix x y -> Bamtrix x z -> BMatrix x (y,z)

LitMatirx :: HMatrix -> BMatrix a b

Zero

Id

par

dup = Vstack

avg

if we had the inversion process output also the nearly/completely non invertible subspace, I think we could extend the schular complement with that. We could also parallelize via interting that subpiece first and then doing a low rank update on the unsolvable bit

Instead of having

What is the version of this that works with convex sets? This would be a convex cone that ... A projection out of a dimension via a

prximal operators are kind of

f(y) + |x-y| + g(x) ~ USV ?

a delta function can be a convex operator. Total

If there is no duality gap, we can commute min and max of primal and dual. We could make composition the min max of the interior.

min_x max_y

g(x,x') if convex in both

g(x,x',y,y') if duality gap 0 in both. min and max commute

This catgoery is monoidal. That's a good start

f(a,b) + g(c, d) = h( (a,c) , (b,d) )

()

In terms of convex sets, this seems like a bianry ste operation followed by projection of thje innter variables. Also needs to lift each one so they are in the same space. lift by combing with unit of binary operation. Proj is a binding form for the inner variable, just like min and max

dialectica. forall exists. That we can commute forall exists / min max is the remakrable property of convexity.

Some kind of game? Given a point I can give a halfspace that constains it

hyperplane seperation theorem? Winner of game isn't always one or the other. Is there an interesection? If so, give point. If not give hyperplane

There are many choices for how to represent the data of a convex function or convex set or hyperlane set. Is there a uniform interface between them?

The certificate property.

Farkas Lemma, either ap roblem is solvable, or there is a proof it is not. Completeness of the convex proof system. Law of excluded middle?

Maybe this is why it isn't meshing well with the inuitionism of type theory functional programming

(cone, dcone) -> Either s, ds

what is a cone though? cone = egenralized inequality which is a catgoey.

Ineq a b => b -a \in cone

Monotonic Functors. Cone a -> Cone b

It would be cool to have OSQP available.

It would almost be more fun (and easier) to reimplement the OSQP algorithm?

They ues inline-c in the recent sundials project. maybe that is the way to go

<https://github.com/haskell-numerics/hmatrix-sundials>

Doesn't seem so bad in principle.

Hmatrix already has some CSC support

<https://hackage.haskell.org/package/hmatrix-0.19.0.0/docs/Numeric-LinearAlgebra-Data.html>

<http://ucsd-progsys.github.io/liquidhaskell-tutorial/11-case-study-pointers.html>

[http://book.realworldhaskell.org/read/interfacing-with-c-the-ffi.html](http://book.realworldhaskell.org/read/interfacing-with-c-the-ffi.html)

[https://github.com/fpco/inline-c-nag/tree/master/src/Language/C/Inline](https://github.com/fpco/inline-c-nag/tree/master/src/Language/C/Inline)

Here they are just making storable instances

<https://www.fpcomplete.com/blog/2015/05/inline-c>

<http://hackage.haskell.org/package/derive-storable>

<https://wiki.haskell.org/Foreign_Function_Interface>

I needed to add extra-libraries to my package.yaml file with osqp correpsonding to an -losqp flag to gcc

LogicT is a backtracking search monad. What if instead of monads, we work with categories. LogicC a b is the kliesli arrow of LogicT. But allowing dependce on the input may pay dividends.

Selection functions - argmax are very similar to proximal operators. They take in perhaps a hessianable convex function and output the proximal value.

We are using Lens as an exmaple of a structure which has sharing and an eventual backwards pass. Continuation passing allows arbitrary teleporting, Ordinary function calls allow the return of values, but we need things to stay open ended. It's sort of like how fixable functions need to stay open ended.

I actually mentioned the callback form in my comments on the orginal post.

(x, dx -> r) -> (y, dy -> r)

(x, dx) -> (y, dy) is forward mode. We can't talk about (x, dx -> r) in isolation because the r connects the fprward and back.

Still. What about making Num r => Num RDual (x, dx -> r) a number? For the purposes of programming. ((x, dx -> r), (z, dz -> r? r'?)) Do they eventually merge?

forall r. RDual r x -> RDual r y ~ Lens x y. Pretty similar. to Lens s x -> Lens s y. Well it's more like we went halfways on it. Lens s x dualizes both compute and reverse path. RDual cps only the reverse path.

This form doesn't seem to have as much unnecessary zeros.

We have had shared environment before.

tup (x, dx -> r) (z, dz -> r)) = ((x,z), \(dx, dz) -> (f dx) + (g dz)

As Kmett, said, The Lens style is nice because it shows that y can't depend on dx/dy.

I think I could build LQR controllers out of these pieces reagrdless of any connection to Jules work or actual Lens analogies.

For reinforcement learning, it seems like the coplay parameters and the play parameters could be different. Weights for V function vs weights for policy function. Weights can be shared between pieces. We sort of have two categories playing, AD and DP. Maybe two directions of

Understanding this would be useful for compiling to Convex Programs. Disciplined Convex Programming should be expressible in these terms

The Convex Hull is a monad.

Conv Conv = Conv

S -> Conv S

And it is a functor with resepct to inclusion

Convex-inclusion may be considered it's own category. Convex-Hull mayb be considered to be the Adjoint of Forget from Convex to Set. This is another way to see that Conv = Forget R is a monad.

Minkowski Sum is a natural monoidal product. No? It doesn't have an identity object. Oh wait. never mind. Minkwoski sum is convex closure plus offset

Generalized cone inequaltities. They do have a composition which is more interesting than a partial ordering. x <=K y says that y-x \in K. So i believe that two different K can be compose using minkowski sum of the cones, implies that x <=(K+K') z.

Individual K composes because K is closed under addition. x in K and y in K implies x+y in K. Any positive combination is closed. x in K implies lam x in K if lam >0.

Hmm. Perhaps a linear Objective could be specified by the set of inequalities <=K ,where K is the half plane of the objective. Minimal means finding some kind of limit. We select this set of inequalities via a Functor (endofunctor)? Or we could just work in that category.

multivariable Convex "functions" => Functors between generalized ineqaulity categories. Gets composition by default.

Natural transformations. <=K is indexed by an element K. Some kind of natural transfromation from a catgory of cones?

Products, limits, etc. Finds maximum and minimal elements.

Can use elements for comparsion or sets. Or convex sets. Can make inequality forall points of if only exists a point

category can include all K or juts a single K

Maybe be important to consider cost function modulo monotonic function post application.

cone = R+ x convex set

Dual cone and dual space. Linear functionals on . Convex duality.

Galois connection between discrete optimization problems and continuous ones. Gomory cuts might be some kind of Kan thing?

|R <= is a category. The min f over a set is a functor from Set-inclusion to R<=. max f is a contravariant functor. These are functors indexed by morphism in Set-function. In general a functor from Set to R<= is something of interest.

Contraction Maps seem like they would form a category. They are a very computable aspect of convex sets. They are a contravariint endofunctor in Set-inclusion.

Submodular functions are "discrete convex functions" perhaps a guinding light should be do that which unifies the concepts

Convex functions have non trivial composition rules. You need non decreasing conditions, which is odd. This makes it not obvious how to form a category.

Non-decreasing vs Monotonic. In either case. The derivative always stays >= 0 and derivatives follow chain rule.

Monotone functions could also be considered a functor from R<= to R<=.

Non decreasing functions form a category. They are closed under composition and the identity function.

The Epigraph has the flavor of an exponential. It somehow turns a convex function into a convex set.

R-inclusion vs R-<= . Convex R inclusion are intervals. Intervals have a tempting mapping to morphisms in R-<=. This is strange. It does not appear to be a very lawful mapping.

n category cafe discussion. The Giry monad? Which is the convex combination monad? [( \lam , a)]. Free convex point is convex combination of basis points (corners of polygon).

<https://golem.ph.utexas.edu/category/2009/04/convex_spaces.html>

<https://ncatlab.org/nlab/show/convex+space>

Another possibility. A convex optimization problem is a function from parameter space to solution space. Makes it more like a regular function.

Convex functions and convex sets. Epigraph.

Legendre transformation is the steepest descent version of Foureir. S(x,x') vs U(x,x'). for classical vs quantum. This is one analogy between linear and maximal mappings.

If we pack otgether the optimization problem, with input and output, we can use the ADMM technique to merge together stuff. Projection. The kernel.

The dup function will require compromise. What happens when two conditions conflict? BiApp paper worries about this significantly with the tagging system. Our tags will be... derivatives?

Forward function, and then the backward function is an ad function.

x -> (y, ADLens y x)

Categorical compositon. x -> (y, k y x) is what Conal Elliott talks about in his AD paper. I guess there is a functor? that loses.. the outer stuff?

How do we handle asking for an output value that can't be had. I guess the backwards direction is also a projection?

The recrusive type.

data PseudoInv = P (x -> (y, PseudoInt y x))

Then The input is actually (x, Bool) -> (y, Bool)

first bool is if y is in the domain, scond bool is if x is in the domain. The pseudoInverse of -inifty might be the minimum. We need to fix out the bools.

data Set = (x -> (Bool, Bool -> x) .. Is refactorable a number of ways. But it packs together a indicator and projector function. There is a category here. we have composition and identity...?

Convex cones generalized inequalities are a binary operator that becomes

(x,y) -> Bool. It is the same thing as y -x being in K. which is a set op (<=K) = inK . subC

hmm Proximal operators and subgradients. I hadn't yet considered those really. Subgradient is the set of all underlying derivatives.

What is Min? Requires derivatives too? Requires duality realized (dual certificates)?

Even though ADMM is talked about in the context of proximal operators, I didn't make the connection really.

Proximal ops might really be the right ticket. It almost feels trivial.(unless it doesn't work)

Proximal operators are x -> x functions

Well, one could imagine have a projective proximal op

They are parametrized by functions f. So we could imagine builders of these functions. Something that takes a gradientable function and outputs the prox operator

prox of seperable functions in a Par rule

Automatic subdifferentiation

generalized inequalities

Ok. Monotone operators are also v cool.

Generalized Equations

Relations.

<https://en.wikipedia.org/wiki/Monotonic_function>

Monotone in the context of A*search. Huh. Branch and Bound may be some kind of A*...?

There is a lot of stuff out there about monotone operators.

I did say monotone functions are the ones that actually compose.

Monotone functions are functors on <=

Fixed point theorems and monotone operators. Something to do with lattice theory

If our abstraction can handle continuum and discret case that would be nice

<https://en.wikipedia.org/wiki/Submodular_set_function>

<https://en.wikipedia.org/wiki/Bregman_divergence> - cool

<https://en.wikipedia.org/wiki/Proximal_gradient_methods_for_learning>

<http://proximity-operator.net/index.html>

Proximal operators are a generalized gradient descent step

Spivak's category of deep learning thing spoke in terms of update functions didn't it

<https://arxiv.org/abs/1711.10455>

Hmm. In terms of a learning problem, we kind of want to feed examples in to the function and update it. This is rather lens like.

Categroies:

Set with inlcussion

ConvSet with inclusion.

Cone with cone inequaltites

R with <=

Monotone Operators / Proximal Operators?

Rockafeller's Action-like operators? Sum = max

Pseudo invertible functions

Functors:

Minkwoski Sum is monoidal. In both Cone and Conv inclusion?

Convex Hull takes Set to ConvSet

Forget takes ConvSet to Set. This is an adjunction leading to a Convex Hull Monad.

Monotone functions are functors on inequality categories

The maximal elements are initial and final object in Cone.

There is a qeustion of what quantifiers to use in cone. Is a set greater than another if there exists an elemt which is less than all the elements, if all the elements are less than all the elements? There are 4 options here naively. I don't know that esists exists is very interesting. Or actually composable.

<https://en.wikipedia.org/wiki/Traced_monoidal_category>

The projector/idicator function pair for convex sets gives us an operation for intersection. We repeatedly project until we get a fixed point. Also for union. Run both,if both are false use one of the projectors. Complement? I don't know that we can build a projector for the complement from the original projector.

The dual space of lines. Should we pack in the dual set of lines that do not intersect/ interesect in at most one point. Or is it the set of lines that do interesect? Yes. I think the second one is convex. Affine functionals that evaluate positive on the entire set (which are in correspondence with hyperplanes using phi=0, and overall positive scaling soesn't matter)? Convex sets come equipped with indiactor functions, projection functions, global linear tests. Seperating hyperplanes.

By duality, we;d want to be able to project a given hyperplane in addition to it's indicator function. We could then find a seperating hyperplane via iterated projection of hyperplanes.

A convex mapping preserves convex sets. ConvSet -> ConvSet

ConvSet a = {ind :: a -> Bool , proj :: a -> a, lintest :: (a -> R) -> Bool, dualproj :: (a-> R) -> (a -> R) }

or DualAble = {primal :: ConvSet, dual :: ConvSet} with ConvSet only have ind and proj.

This is a big collection of functions. Feels more like a typeclass. I suppose a lens could be a typeclass too

class ConvSet s a | s -> a where

data Circle =

data Ellipse =

data AABB =

data Cylinder =

data HRep = -- polytope Ax<= b

data VRep =

data HalfSpace

data Intersect a b = Intersect a b

data Epigraph

There is the linear subspace in R^n but there is also R^m and actual prohection maps between R^n and R^m. Slightrly different thingts

exteneded Reals

data Ext a = Inf | NInf | Fin a

subdifferential is quite similar to convex set of lines. Except extra condition that it has to touch function point.

A Convex projection probably has to obey some rules. i.e. is a proximal operator. minimiizes (x-x')^2+ind where the indicator function gives inifnite cost to outside the region. Is one exmaple. but don't have touse squared distance. Any "convex" distance is fine. Bregman?

Minkowski sum with just proj and inc. Can't do it. That is suspicious. Can project. Project into them indivudally then add. Will this projection preserve position if in it? Can't test inclusion. Need to solve for the right combo.

Simple epigraph projection. evaluate f(x). Then take max(y, f(x)).

Convex hull. convex hull of union. How do we do that?

Does duality help? Linear functionals.

actual duality conversion. given indicator and proj can I build the dual ind and proj?

orietned hyperplanes also correspond to half-spaces. This may be a more symmettrical version of duality.

Half spaces with non empty intersection.

dual ~ intersect

Dual ~ ConvSet (HalfSpace)

dinj :: HalfSpace -> True = { }

dproj :: HalfSpace -> HalfSpace

dual :: ConvSet -> HalfSpace ->

dualinc

dualproj

HalfSpace has a set complement that is convex. So finding the nearest halfspace that cpntains no poitns of S or all points of S.

Halfspaces that contain all of S. S = intersection of all these half spaces.

Point a & Halfspace a are dual.

ConvSet (Point a) vs ConvSet (Halfspace a)

doublefix f = helper loop

class Fixable a where

fix :: (a -> a) -> a

class Trace a

Helly's Theorem

Minkowski Theorem

proj proj = proj. Has some of the character of a monad. Circle a, Circle a. Compose Circle Circle. Product Circle Circle. Sum Circle Circle.

(Conv a) monad. After every operation, re project back into the set. That is the pipework.

<https://en.wikipedia.org/wiki/Projections_onto_convex_sets>

averaged projection works better

Dijkstra's method seems like ADMM. Seems like it has some extra guarantees of being a closest point.

inclusion as question?

I feel like we could use some sequence acceleration. We're definitely discovering higher order info as we go along.

Intersection of two planes ought to converge finitely. One would hope.

<https://en.wikipedia.org/wiki/Dykstra%27s_projection_algorithm>

type family RN where

RN 0 = ()

RN n = (Double, RN (n-1))

ADMM/ prioximal / first order is flexible. Never as fast as specialized method. Similar to functional programming vs low level stuff.

Projection(y) = min {d(x,y} s.t. x \in S}

Proximal operator is quite similar.

Maybe we don't want the test function. Maybe proj x = x is sufficient. We should just be working with projection functions.

Category Proj

sphere :: Rn -> Double -> Proj n n

Rn -> Rn

Rn -> Rm

Rm -> Rn

Includes actual dimension changing projections and dimension changing inclusions? {proj :: Rn -> a , inc :: a -> Rn}. If you compose them, you get the projection Rn -> Rn.

A proximal operator {Rn -> (~a,~a -> Rn }? That doesn't fully project...

inc will often be a newtype unwrapping. This pair does give it a lens flavor. We don't really need the original point through. Maybe mixed with a notion of linearity. Rn -> (a, b -> Rn) gives a as a projection of Rn. Then adds in b to a, and injects it back.

get ~ proj. set ~ include.

a is a piece of

proj . inc = id

inc . proj = something. It's also identity kind of. but only if an object was already in a.

idProj = {proj = id, inc = id}.

Adjunction? That obeys K<= or Set inclusion? It does make sense to talk about projection inclusion as functors that are preserving something.

Project feels like Forget, Inj feels like Free.

Circle (R2 a) actual adjunction?

R2 (R3 a) = 6 coordinates?

Adjunction page talks about optimization and "best"

<https://en.wikipedia.org/wiki/Adjoint_functors>

What about a proj, pseudo inverse pair. Rn -> (a, a -> Rn). psuedo projection? Rn -> Rn -> a. Rn -> (a, a -> Rn -> Rn). a pesudo injection Rn -> a -> Rn. That's kind of like a proimal operator.

Should we be working in homogenous coordinates?

class Projective a b where

incidence :: a -> b -> Bool

-- an overlapping instance

Projective a b => Projective (Dual b) (Dual a) where

incidence = flip incidence -- and newtype unwrap/rewrap

class Join a b | a -> b where

line :: (a,a) -> b

instance Join (R n) (R (n +1))

class Meet a b | b -> a

intersect (b,b) -> a

instance Meet (R n) (R n +1)

intersect :: -> b

This isn't right. Only in 2d. the line connecting two points adds one dimension. The intersetc removes one. They are different than the dual relation.

data HomPoint

data HomLine

Exterior Algebra

maintain Fixable for later

wheels within wheels.

Or fix is in composition

The splitting of proximal operators into having a seperate domain and range is important?

Should the dual become a jacobian, a matrix for Rn -> Rm projections?

Proximal operator with precomposition of f. + some kind of pseudo inverse.

ADMM has some kind of backprop of duals.

Interesting spin on duality

Instead of using explicit Double as scalar. Use typeclass. Then make a faker scalar

forall s. VecScalar v s => (v -> s) -> (v -> s)

LinearFunctional l v s where

 apply :: l -> v -> s

data FreeDot v = FreeDot v

VecScalar v (FreeDot v) -where
