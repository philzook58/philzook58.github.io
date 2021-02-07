

Counter Example Guided Abstraction Refinement (CEGAR) is a search strategy for either making a solver more efficient or extending it's capabilities. One makes an abstracted problem (contains false solutions) of the problem at hand that a solver can handle more easily than the full problem. The solver returns a solution. Either this solution is a valid one with respect to the complete problem, or it falls in the gap of between the abstracted problem and actual problem. In which case, one uses the solution to tighten up the abstraction to outlaw that solution. Rinse and repeat.

SMT itself can be considered an example of CEGAR from  certain perspective. SMT solvers have sort of two layers: sort of a propositional layer and theory specific reaosning layer. One can abstract facts like $x \le 3$ as an opaque boolean variable $p$. Send it off to a SAT solver which only understand the logical propositional structure, it returns a solution. Either this solution is consistent with the actual interpretation of the propositional variables as linear inequalities or not. If not, there must be some subset of the inequalities that actually is not self consistent. This is a propositional cluase that you can assert to the SAT model to refine the model. Rinse and repeat.


Z3 is my favorite solver. It is very expressive, but it doesn't have everything. One omission that hurts for some applications is that Z3 does not understand transcendental functions that exp, sin, cos, etc. Other SMT solvers can handle these things, in particular dReal.

But it is interesting to build a CEGAR loop involving Z3 to extend it to support them. What we can do is mash together a solveing process ping ponging between Z3 and an interval arithmetic library.





 in which one uses posits a loosely built model of the problem to a solver. The solver returns