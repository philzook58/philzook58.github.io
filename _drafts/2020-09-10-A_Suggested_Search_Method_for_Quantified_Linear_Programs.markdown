---
author: philzook58
comments: true
date: 2020-09-10 13:46:32+00:00
layout: post
link: https://www.philipzucker.com/?p=1064
published: false
slug: A Suggested Search Method for Quantified Linear Programs
title: A Suggested Search Method for Quantified Linear Programs
wordpress_id: 1064
---

1/21
http://www.sc-square.org/CSA/school/lectures/SCSC-Brown.pdf

Interesnotes on the cylindircal decompositions.

The logic - egeometry dictionary
and intersection, or union, not complemente

exsietntical eleminiation - projection

converting forall to exists = complement + projection
skolemization - finding 

https://twitter.com/jjcarett2/status/1355555191500779522

ISSAC conferencwe


9/20

I think that quantified linear programs might be the same or related to presburger arithmetic http://www.lsv.fr/~haase/documents/h18.pdf

Quantification over boolean variables is in principle not difficult. Maybe a good example. 1. We can skolemize, 2. We can convert forall to exists via negation 3.

05/18

Quantification is adding forall and exists to logic questions.

Quantified Boolean formula are a class of problems that is harder than SAT. A SAT solver can tell you if no solution exists by returning UNSAT or tell you one does and return the example.

Alternating quantifiers have usefulness in describing games (there exists a winning strategy that works regardless of whatever moves the other guy plays) or in Control (forall reasonable errors and perturbations, I have an action set (there exists) that achieves my goal). In both cases, you can have knowledge of the past but not the future and make decisions according to what you've observed.

Stochastic Programming

Another example the coin game question. How many weighings do you need to figure out fake coins? You may make different choices based on the result of previous weighings. How do you PROVE no strategy exists for n weighings? It is not clear to me how to ask a computer this question using the tools I know of.

Alternating quantifiers take us into something called the polynomial hierarchy, a hierarchy of complexity classes that are probably harder than NP (since P is probably not NP).

Exists feels easier to prove, you just have to provide an example that satisfies the required property. You can get lucky in your search of use some heuristic but that doesn't matter once you've got it in hand.

Forall is harder. You have to rule out something can happen for all the possibilities. You can prove forall by a failure to find a counterexample. Or by finding some kind of explicit proof object that has data telling you how to derive the conclusion.

There is a duality between between these two things.

Linear programs can be thought of as a conjunction of linear equalities with an implicit Exists out from on all the variables (This is ignoring the ability of LP to also perform optimization and instead focusing on their feasible/infeasible abilities). Dual linear programs are explicit proofs on how to combine the inequalities to generate a desired inequality, so they are kind of instructions on how to manipulate.

Given the constraints on the domain, can some value of the objective be achieved is a feasibility problem. In logical terms this looks like an implication from the conjunction of domain constraints to the objective constraint. $latex \and (Ax \le b)\implies (c^T x \le b) $

Feasiblity ~ SAT ~ Exists.

Infeasiblity ~ UNSAT ~ Forall.

Skolemization is a process that you can use to commute Exists outside a Forall. It turns the variable in a function of the variable you commuted through. This has the sense of a strategy given the current information.

We commute all the exists variables to the left. This makes a sequence of skjolem functions with increasing dependence on the universalized variables

I think that piece-wise linear functions are sufficient skolem functions for QLPs. This is because the solution to an LP is a piecewise linear function of the problem parameters.

If we have a correct linear skolem function in hand, we can use an LP to verify the Forall parts by substituting in the skolem function.

Now we can use a heuristic to find a skolem function. The heuristic doesn't really matter.

It seems to me that a very reasonable skolem function can be gotten from using the analytic center. The analytic center can be used to make a natural quadratic weighting function that captures approximately the various linear constraints.

Another reasonable one would be using $latex A^T A$ and using the pseudoinverse central position of the inequalities. On a qualitative level, this seems similar to analytic center, but easier to compute. SCRATCH that. Imagine an unusued constraint way off of the region. Could pull center away. Maybe if you use only activated constraints?

Another possiblilitie is a monte carlo sampling. For example one could use an LP with randomized objective functions. Then use the standard deviation of these as the matrix and the mean as the center.

These methods also generate an example solution (converting all forall to exists) demonstrating that it is possible.

On can use any heuristic method to find this matrix one likes. If you have some intuition.

Then using a schur complement procedure one this form, we can derive reasonable linear feedback functions for the exists variables in terms of the forall variables. This is roughly the LQR procedure. Another way of thinking about it is Fourier-Moztkin would be a method to remove variables from the true equations. If we removed all the Exists variables, we'd then have an LP left. It is tough though and makes the problem size explode. Taking this heuristic is something like using solvable Gaussian elimination instead of true fourier-motzkin elimination.

An alternative is to use the example central solution to take away the future variables and the schur complement out only the current time step. This is easier. The recursive schur procedure feels better since it takes account of future variability, but recursive schur may be unstable.

Question: What if schur is impossible due to D being uninvertible. I would reccommend just setting the feedback to zero / inverting all eigenvalues except zero. Is this going to be rare? Does zero imply perhaps that variable is unbounded?

One can also avoid this generic Schur complement procedure again if you have some heuristic feedback form you think might work better. There is room for personal expression within this framework.

In the case that verification of the heuristic skolem function fails, we should cut the domain. We already will have the analytic center and a counterexample failure point in hand, so I think you could use that to make a reasonable cut and recurse.

Is there something unsound about the reasoning in the step?

There are two simple cases of the problem. A Forall implies that Exists is true. So we can ask the LP where all variables are Foralled. This is whether the domain is constrained enough that our choice within it doesn't matter, everything always works out.

The other thing we can do is turn all the Foralls into exists. If this statement is false, then we can't find a solution even assuming optimistic helpful perturbations.

The two moves can be used to prune early.

I think the entire procedure is more likely than not sound but not complete. I think that if the skolem function is VERY particular (has no wiggle room to it) You probably won't find it. This is unfortunate. You won't cut on the actual piecewise lines, and you won't get the right slopes. Maybe you will converge in some epsilon sense to this skolem function. As you tile the entire domain, you can achieve essentially arbitrary functions.

However, I find this unlikely for the applications I have in mind (maybe I'll be surprised). Exactly one skolem function means that it probably has a really high dependence on the problem parameters, which are probably not that well known.

Perhaps in a pure logic application this is more of a problem.

Extensions:

To take LP to Convex Programming is probably not a big deal. There is nothing really that depends on LP. You just need a correspond CP solver. The analytic center and heurisic linear feedback works just fine. The feasible/infeasible is also fine... ? Actually, it is useful that the negation of a linear inequality is a linear inequality? Strict ineqality (is strict inequality a problem? I feel like Boyd mentioned a way to deal with this. Also you could probably just expand the region a bit for my purposes.). This is for being able to check exists vs forall. Hmm.

Can one plugin a MILP solver to then do QMILP? Perhaps. The feedback form may need fractional rounding variables placed in them.

Replacing the LP with a SAT solver seems like a natural way to get a QBF solver. The heuristic feedback seems more problematic however. Could we use a clamped linear relation? XOR matrix? Small CNF connectors? What is a relaxed form? Perhaps monte carlo estimation combine with some kind of NumSAT to fit the feedback form (pick the parameters in the sat instance to maximize numSAT)? 2SAT, HORN SAT, and XOR SAT are reasonable easy similar problems to use as heuristics.

Given a proof in the form of cuts and feedback matrices, can one actually use these easily on line? You need to use the cuts to determine which matrix to use. Something feels wonky about this, but maybe it is fine.

The cuts need to occur at a layer of  forall quantifiers. The two branchs from the cut need to share skolem functions for variables before the cut but are allowed to differ after. This makes sense in terms of a decision tree. You need to pick which linear feedback to use with the information you have.

Where to place cut both interms of y space and in terms of temporal decision time. Analytic center may indeed work

$latex \forall y \in R = forall y R_1 \and \forall y \in R_2$

You can partially skolemize. Then cut regions, then finish the skolemization inside the branchs.

It is reasonable to keep around previous higher level feedback forms and reuse them for the shared feedback.

$\forall y \exists x \forall y \exists x = \exists f(y1) \forall y \forall y \exists x = \exists f(y1) \forall y1 y2 R1 \and \forall y1 y2 R2 \exists x = \exists f(y1) (\exists f_2 \forall y1 y2 \in R1) \and (\exists f'_2 \forall y1 y2 \in R2) $

Should put branches early? Put the split before the "failure branch". Failure time could be detect perhaps by using existance solution and plugging in to the front or back? Iterativey replace with the good path and ask if it works for all possible now.

Maybe think of this is terms of a recursive problem. Assuming we have a solution method for downstream, give one more layer of existtentials.


    
    #at top level let branchn increase expoentially for iterative deepening
    def qlp(A,b, Q, branchn):
        if branchn = 0: #Iterative deepening
            return False, 0
        if Q == []:
            return check_forall(A,b), branchn
        if check_forall(A, b): #maybe we don't need feedback for the rest. The end action values do not matter. if so quit early. Maybe not be worth it to do this check
            return True
        #check that it is even possible at this stage to get a solution: Convert all forall to exists
        # or perhaps the call to analytic center ought to do this?
        # or perhaps if we use the monte carlo method
        sol, found = check_exists()
        if not found:
            return False
        #Q is a list of indices that describe the transition from forall to exists. 0 is assumed as the start
        # Or should Q be an array of bools. True for forall and False for exists.
        xc = analytic_center(A,b)
        hess = analytic_center_hess(A,b)(xc) #Could include grad in expansion too.
        # alternative 
        #xc = np.linalg.pinv(A,b)#
        # hess = np.dot(A.T, A)
        # calculate only feedback for first exists
        K, f = calc_feedback(xc, hess, Q) # feedback matrix and offset 
        #use feedback to remove u from consideration
        Aprime, bprime = use_feedback(K, f, A, b, Q)
        #Remove delimiters for first exists
        popQ = copy()
        popQ.remove(0)
        popQ.remove(1)
    
        #if using the approximate feedback for this level, Aprime and bprime is good this will work
        if qlp(Aprime, bprime, popQ, branchn):
            return True
        # evidently feedback at this level isn't good enough if that returned false so instead we cut
        # we may want the counter example propogated upward so we can use it to select a good cut.
        cutA, cutb = select_cut(xc,Q, A , b) 
        found, remainingdepth = qlp(A ++ cutA, b ++ cutb, Q, branchn - 1)
        if remainingdepth > 0 and found:
            found, remainingdepth = qlp(A ++ -cutA, b ++ -cutb, Q, reminaingdepth ): # Take both sides of the cut without change Q structure
            if found:
                return True
            else:
                return False
        else:
            return False
    
    # This is getting structure more and more like traditional search.
    # I feel like the recursive nature is changing how I can think about things though.
    # maybe Alpha beta pruning is appropriate? Like it said in that paper.
    # I had the thinking that maybe one should try backjump pretty far back if it is clear somehow
    # that a previous feedback is a big problem. Infeasiblity should return some kind of slack thing. We should probably backjump up to the level where the
    # we are hurting the most.
    
    #Is there a way to determine K is there is literally a single K that will work without heursitcs?
    # This is necessary if we went to head towards completeness



Am I guaranteed that my feedback forms stay in bounds for exists variables? Maybe (assuming interior ellipse which we may need to reduce gain of feedback slightly), but also it is okay if it doesn't. It will be detected that it goes out of bounds. No... wait this might be important.

Right. The linear discriminator example in Boyd Geometric problems

https://web.stanford.edu/class/ee364a/lectures.html

shows that since the linear inequalities are homogenous in A and b,  can add a scale variable and just set it all to 1. Good. Uhhhh, but that is for x being fixed and A and b being the variables.

ok. We need to maximize epsilon added to each inequality. 0 <= epsilon =< 1 If we  all epsilon aren't strictly greater than zero, then the strict inequality problem is infeasible.  Or perhaps is might be okay to just add 1e-10 to each inequality.
