https://www.cs.utexas.edu/~isil/cs389L/houdini-6up.pdf

Constrained horn clauses

https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/MSR-TR-2013-6.pdf

https://chc-comp.github.io/

https://spacer.bitbucket.io/

https://seahorn.github.io/

https://theory.stanford.edu/~arbrad/papers/Understanding_IC3.pdf 


Programming Z3 tutorial
Spacer jupyter tutorial https://github.com/agurfinkel/spacer-on-jupyter/blob/master/Dagstuhl2019.ipynb
https://arieg.bitbucket.io/pdf/synasc2019.pdf

IC3 / PDR unbounded model checking

This is somehow more than a prolog. It's inferring _predicates_

https://people.eecs.berkeley.edu/~sseshia/219c/#books modelchecking course.


Subgoal induction. ??? Seems tailor fitted to CHC. From Mitchel Wand paper refernces to Morris paper
"inductionless induction / narrowing" are the things cody seemed to find this reminsent of 


Wait, so SAT is solving the problem, but unsat is a counterexample trace?

```python
from z3 import *
x = BitVec("x",16)
x1 = BitVec("x'",16)
s = SolverFor("HORN")
i16 = BitVecSort(16)
Inv = Function('mc', i16, BoolSort())

'''
x = 0
while(x < 10)
  x++
assert(x < 11)
'''
init = ForAll(x, Implies(x == 0, Inv(x)))
loop = ForAll([x,x1], Implies( And(x < 10, Inv(x), x1 == x + 1), Inv(x1) ) )
post = ForAll(x, Implies(Inv(x), x < 11)) #ForAll(x, Implies(And( x < 11 , Inv(x)), False)) 

s.add(init, loop, post)
s.check()
s.model().eval( Inv(x) )
```

You can use horn clauses to perform craig interpolation.
A => I
I /\ B => False
Hmmmmmm. But what do you use craig interpolation for?
IC3 I think. You can build over approximations of intermiedate sets.



Running a prolog query:

forall(x, plus(s(x), ) )
plus(x,y,z) => False
Or 
True => plus(x,y,z) ? with no quantification?



https://www.youtube.com/watch?v=-eH2t8G1ZkI&t=3413s
syntax guided synthesis
sygus-if https://sygus.org/
CVC4 supports it.
LoopInvGen, OASES, DryadSynth, CVC4

rahul sharma
polikarpova, peleg, isil dillig

https://www.youtube.com/watch?v=h2ZsstWit9E&ab_channel=SimonsInstitute - 
automated formal program reapir
"fault localization" 
https://github.com/eionblanc/mini-sygus