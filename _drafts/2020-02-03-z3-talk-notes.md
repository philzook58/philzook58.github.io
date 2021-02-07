z3 talk notes

What are formal methods?



Talking about the disjoint set data structure?
The E-graph


quantifier instantiation



Bounded Model Checking (TLA+ ?) v Symbolic Execution

if x < y:


else



Name each variable once
Weakest preconditio


Klee

 Things may be written in not the most clear way for performance reasons or may be written in a language in which has lots of surprising tricky gotchas.
There may also be surprising unanticpated behaviors the emerge from a spec in regimes that may not have been considered when it was made.


Takeaways

What should you understand:
Z3 is kind of cool
Exhaustively failing counterexamples = Proof.
There is automation out there that can solve queries written in first order logic




I actually want us to take a moment to poke around in these 3 things.
Should I guide them?

Read the Docs, stupid



Algerbaic data types



functions vs values


zoom + slack
possibly gather

webinar vs interactive
coq helpers


update the smie.gtihub.com link

Takeaways
make separate reop

Make line about loading it. and reference reop
https://www.youtube.com/watch?v=nGwyNmsxX6I&ab_channel=StasFomin



Takeaways:
- Formal methods
- Z3 as a solver
- Proof = Not finding counterexamples


- What can't Z3 do
  - Complicated stuff
  - Extremely expressive mathemtics
  - Gracefully take hints / human guidance



Other things to look at
Hadrware verification
Distributed systems and concurrency
TLA+




#my_solution: leave blank

#More examples first
''' solution
x = Real("x")

solve(x**3 + 3*x**2 + 4*x + 2 == 0)
'''


# Solution : solver.add( [And(0 <= d, d <= 9) for d in digits]  )
# Solution: solver.add( [ d1 != d2 for d1 in digits for d2 in digits if not eq(d1,d2)]  ) # unique
# Solution : solver.add(send + more == money)

prove( And(p,q) == Not(Or(Not(p),Not(q)))) #De Morgan's Law

''' solution
prove(x + y == y + x) #Commutativity
prove(((x + y) + z) == ((x + (y + z)))) #associativity
prove(x + 0 == x) # 0 additive identity
prove(1 * x == x)
prove(Or(x > 0, x < 0, x == 0))
prove(x * (y + z) == x * y + x * z)
prove(x ** 2 >= 0)
'''

''' solution
prove(x + y == y + x)
prove((x + y) + z == x + (y + z))
'''


'''
x = BitVec("x", 64)
y = BitVec("y", 64)
z = BitVec("z", 64)
prove((x + y) + z == x + (y + z))
'''



''' solution
   Or(And(x < 0, y >= 0),
   And(x >= 0, y < 0))
'''


Opposite signs

You can also create algebraic data types and uninterpreted sorts. 
f = Function("f", IntSort(), BoolSort(), BoolSort()) # functions

x, y, temp, x2,y2 = Ints("x y temp x2 y2")
prog = [
    If(y < x,  
        And( [temp == x, x2 == y, y2 == x]  )     ,  
       And([x2 == x, y2 == x])   )
]

prove(Implies(And(prog), x2 < y2))


1. Have solutions ready
2. Screw weakest precondition. Eh maybe I'll do it
3. Trim test of RL section.
4. Uninterpeted functions and quantifiers.

Take out chbeyshev polynomials
# Constrain all digits constrained to be 0 through 9
# FILL IN
solver.add([  And( 0 <= d, d <= 9 )   for d in digits])
# Constrain all digits to be unique (Hint: Look at the 8-Queens constraints. Anything useful?)
# FILL IN
solver.add(Distinct(digits))
# Constrain send + more == money
# FILL IN
solver.add(send + more == money)


p, q = Bools("p q")
prove( And(p,q) ==  Not( Or(Not(p), Not(q))) )
prove( Implies( p, q ) == Or(Not(p), q))
prove(  Implies(Implies(Implies(p,q),p),p ))




prove( x + y == y + x)
prove( (x + y) + z == x + (y + z))
prove( x*x >= 0 )


x = BitVec('x', 32)
y = BitVec('y', 32)

# FILL IN
fast = x ^ y < 0
slow = Or( And( x < 0, y >= 0  ), And(y < 0, x >= 0))
slow2 = If(  And( x < 0, y >= 0  ) ,  True, If(  And(y < 0, x >= 0) , True, False) )
prove(fast == slow)
prove(slow == slow2)


x,y,x1,y1,temp = Ints("x y x1 y1 temp")
prog = [
        If(y < x, 
           And( temp == x,
                x1 == y,
                y1 == temp  ),
           And(x1 == x,
               y1 == y))
]
prove(Implies(And(prog), x1 <= y1 ))

x,y,x1,y1,temp = Ints("x y x1 y1 temp")
prog = [
        If(y < x, And(x1 == y, y1 == x  ),  And(x1 == x, y1 == y))
]
prove(Implies(And(prog), x1 <= y1 ))

