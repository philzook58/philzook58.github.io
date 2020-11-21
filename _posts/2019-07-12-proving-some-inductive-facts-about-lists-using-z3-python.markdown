---
author: philzook58
comments: true
date: 2019-07-12 14:03:11+00:00
layout: post
link: https://www.philipzucker.com/proving-some-inductive-facts-about-lists-using-z3-python/
slug: proving-some-inductive-facts-about-lists-using-z3-python
title: Proving some Inductive Facts about Lists using Z3 python
wordpress_id: 2172
categories:
- Formal Methods
tags:
- atp
- python
- z3
---




Z3 is an SMT solver which has a good rep. Here are some excellent tutorials.







[https://rise4fun.com/z3/tutorial](https://rise4fun.com/z3/tutorial)







[https://theory.stanford.edu/~nikolaj/programmingz3.html](https://theory.stanford.edu/~nikolaj/programmingz3.html)







[http://homepage.cs.uiowa.edu/~ajreynol/VTSA2017/](http://homepage.cs.uiowa.edu/~ajreynol/VTSA2017/)







SMT stands for satisfiability modulo theories.  The exact nature of power of these kinds of solvers has been and is still hazy to me. I have known for a long time that they can slam sudoku or picross or other puzzles, but what about more infinite or logic looking things? I think I may always be hazy, as one can learn and discover more and more encoding tricks to get problems and proofs that you previously thought weren't solvable into the system. It's very similar to learning how to encode to linear programming solvers in that respect.







SMT solvers combine a general smart search procedure with a ton of specialized solvers for particular domains, like linear algebra, polynomials, linear inequalities and more.







The search procedure goes by the name DPLL(T). It is an adjustment of the procedure of SAT solvers, which are very powerful and fast. SAT solvers find an assignment of boolean variables in order to make a complicated boolean expression true, or to eventually find that it can never be made true. SAT solvers work on the principle of guessing and deducing. If `a OR b` needs to be true and we already know `a` is false, we can deduce `b` must be true. When the deduction process stalls, we just guess and then backtrack if it doesn't work out. This is the same process you use manually in solving Sudoku.







The modern era of SAT solvers came when a couple new tricks vastly extended their power. In particular Conflict Driven Clause Learning (CDCL), where when the solver finds itself in a dead end, it figures out the choices it made that put it in the dead end and adds a clause to its formula so that it will never make those choices again. 







[https://sahandsaba.com/understanding-sat-by-implementing-a-simple-sat-solver-in-python.html](https://sahandsaba.com/understanding-sat-by-implementing-a-simple-sat-solver-in-python.html)







SMT works by now having the boolean variables of the SAT solver contain inner structure, like the boolean p actually represents the fact $ x + y < 5$. During the search process it can take the pile of booleans that have been set to true and ask a solver (maybe a linear programming solver in this case) whether those facts can all be made true in the underlying theory. This is an extra spice on top of the SAT search.







Something that wasn't apparent to me at first is how important the theory of uninterpreted formulas is to SMT solvers. It really is their bread and butter. This theory is basically solved by unification, which is the fairly intuitive process of finding assignments to variables to make a set of equations true. If I ask how to make $ fred(x,4) = fred(7,y)$, obviously the answer is $ y=4$, $ x=7$. That is unification. Unification is a completely syntax driven way to deduce facts. It starts to give you something quite similar to first order logic.







[https://eli.thegreenplace.net/2018/unification/](https://eli.thegreenplace.net/2018/unification/)







[https://cs.mtsu.edu/~rbutler/courses/sdd/automated_deduction/unification.pdf](https://cs.mtsu.edu/~rbutler/courses/sdd/automated_deduction/unification.pdf)







I was also under the impression that quantifiers $ \forall, \exists$ were available but heavily frowned upon. I don't think this is quite true. I think they are sort of a part of the entire point of the SMT solver now, although yes, they are rather flaky. There are a number of methods to deal with the quantifier, but one common one is to look for a pattern or parts of the subformula, and instantiate a new set of free variables for all of the quantified ones and add the theorem every time the patterns match. This is called E-matching. 







Here are a couple tutorials on proving inductive facts in SMT solvers. You kind of have to hold their hand a bit.







[http://lara.epfl.ch/~reynolds/vmcai15.pdf](http://lara.epfl.ch/~reynolds/vmcai15.pdf)







[http://homepage.divms.uiowa.edu/~ajreynol/pres-ind15.pdf](http://homepage.divms.uiowa.edu/~ajreynol/pres-ind15.pdf)







SMT solvers queries usually have the flavor of finding something, in this case a counterexample.  The idea is that you try to ask for the first counterexample where induction failed. Assuming that proposition P was true for (n-1), find n such that P is not true. If you can't find it, then the induction has gone through. 







And here is some code where I believe I'm showing that some simple list functions like reverse, append, and length have some simple properties like $ \forall t. rev (rev(t)) == t $.






    
    
```python

from z3 import *

# Very useful reference
# https://theory.stanford.edu/~nikolaj/programmingz3.html

f = Function('f', IntSort(), IntSort())
s = Solver()
#s.add(f(True) == False, f(False) == True)
x = Int('x')
s.add(ForAll([x], f(x) >= x)) #> and < do not seem to be returning
print(s.sexpr())
s.check()
print(s.model())

# Rolling my own list data type
# Z3 has a built in which will probably be better?
s = Solver()

L = Datatype("MyList")
L.declare("Nil")
L.declare("Cons", ("hd", IntSort()), ("tail", L))
L = L.create()

t = Const('t', L)
u = Const('u', L)

y = Int('y')


rev = Function('reverse', L, L)
app = Function('append', L, L, L)
leng = Function('length', L, IntSort())

#defining my functions. Micro Haskell, BABY
#length
s.add( leng(L.Nil) == 0 )
s.add(  ForAll([u,y],  leng(L.Cons(y,u)) == 1 + leng(u))) #  patterns = [leng(L.Cons(y,u))] 

#append
s.add(  ForAll([u], app(L.Nil, u) == u)) 
s.add(  ForAll([t, u, y] , app(L.Cons(y,t), u)  ==  L.Cons(y, app(t, u ))))

#reverse
s.add( rev(L.Nil) == L.Nil)
s.add(  ForAll([y,t],  rev(L.Cons(y,t)) == app(rev(t), L.Cons(y, L.Nil))))


s.push()
print("proving leng(t) >= 0")
#s.add( Or(And(t == L.Cons(y,u),  leng(u) >= 0 ), t == L.Nil))
s.add(  Not(leng(t) >= 0 ))
s.add( Implies(t == L.Cons(L.hd(t), L.tail(t)),  leng(L.tail(t)) >= 0 ))
print(s.check())

s.pop()
s.push()
#s.add( leng(app(L.Nil, u)) == leng(u) )

print("prove length is preserved under app.")
s.add( leng(app(t,u)) != leng(t) + leng(u))
s.add( Implies(t == L.Cons(L.hd(t), L.tail(t)),   leng(app(L.tail(t),u)) == leng(L.tail(t)) + leng(u)  ))
print(s.check())

s.pop()
s.push()

print("reverse preserves length")
#Lemma Could place in clause with the above proof of this theorem
s.add( ForAll([t,u], leng(app(t,u)) == leng(t) + leng(u)   )) #subgoal needed
s.add( leng(rev(t)) != leng(t))
s.add( Implies(t == L.Cons(L.hd(t), L.tail(t)),   leng(rev(L.tail(t))) == leng(L.tail(t)) ))


s.pop()
s.push()

print("reverse reverse = id")
s.add( ForAll( [t,u], rev(app(t,u)) ==  app(rev(u), rev(t)) ) ) #subgoal needed
s.add( rev(rev(t)) != t )
s.add( Implies(t == L.Cons(L.hd(t), L.tail(t)),   rev(rev(L.tail(t))) == L.tail(t) ))
print(s.check())


#junk

#s.add(t != L.Nil ) 
#s.add( ForAll([t], rev(L.Cons(y,t)) ==   ) , rev(L.Nil) == L.Nil)
#s.add( leng(L.Cons()) == 0 )
#s.add(  ForAll(y,  leng(L.Cons(y,L.Nil)) == 1 + leng(L.Nil)))
#s.add(  Not( leng(app(t,u))  == leng(t) + leng(u) )) 

# prove length of app + nil is same
#s.add( leng(app(t,L.Nil)) != leng(t))
#s.add( Implies(t == L.Cons(L.hd(t), L.tail(t)),   leng(app(L.tail(t),L.Nil)) == leng(L.tail(t))))

#s.add( app(L.Nil,L.Nil) == L.Nil)
#s.add( app(t,L.Nil) != t)
#s.add( Implies(t == L.Cons(L.hd(t), L.tail(t)),   app(L.tail(t),L.Nil) == L.tail(t)))


#s.add(Or(t == L.Nil , And( t == L.Cons(y, u),   app(u,L.Nil) == u)  ))
#s.add( Implies(t == L.Nil, leng(app(L.Nil, u)) == leng(u) ))
# all of these don't work
#s.add( Implies(u == L.tail(t),  leng(u) >= 0 ))
#s.add( ForAll(u, Implies(t == L.Cons(y,u),  leng(u) >= 0 )))
#print(s.sexpr())
#print(s.check())
#print(s.model())

#print(tactics())
'''
def induction(freevar, f, construtors?):
    x = Int('x')
    return And(Not(f(x)), 
'''

'''
# controller synthesis
pos = Array(Real, 10) 
for t in range(10):
    s.add(pos[t] == pos[t] +  v * dt)
    s.add(v[t] == v[t] + f(pos[t]) * dt)
    s.add(f(pos[t] <= 1)) # constraints on force
s.add(ForAll([init], Implies(And(init <= 1, pos[0] == init), pos[9] <= 0.1) ))

s.add(Forall[x], f(x) == a * x) # parametrizing. 
'''
#s.set("produce-proofs", True
#s.set("mbqi", False)
#s.set(mbqi=False)
#print(s.proof())
```




