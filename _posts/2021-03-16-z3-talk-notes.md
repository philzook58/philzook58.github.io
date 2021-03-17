---
date: 2021-03-16 
layout: post
title: Z3 Tutorial For FMIE 2021

---

Well, I gave my tutorial on the Z3 SMT solver for FMIE 2021 <https://fmie2021.github.io/agenda.html>. That's a load off! I think it went very well. Thanks again to Gopal Sarma for really holding the thing together and Cody Roux for bringing me in!

Here's the Jupyter notebook

<https://github.com/philzook58/z3_tutorial>

and here's the video

<iframe width="560" height="315" src="https://www.youtube.com/embed/56IIrBZy9Rc" frameborder="0" allow="accelerometer; autoplay; clipboard-write; encrypted-media; gyroscope; picture-in-picture" allowfullscreen></iframe>


I translated some of these Z3 examples to Coq in a blog post here <https://www.philipzucker.com/translating-z3-to-coq/>

Some solutions to the exercises

```python
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
prove( (x + y) + z == x + (y + z))s
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

```




### Further topics that would be nice to get into
Not that I necessarily understand these things completely

- Really abusing uninterpreted functions
- Quantifier whispering
- Constrained Horn Clauses
- Datalog
- CEGAR loops
- Extracting proofs

Nikolaj Bjorner talk on SMT solving
https://www.youtube.com/watch?v=TgAVIqraCHo&ab_channel=SimonsInstitute

Interesting tidbits:

```python
def CDCL():
   while True:
      if [] in clauses: return UNSAT
      elif in_conflict(): learn(); backtrack()
      elif not free_vars return SAT
      elif should_propagate(): propagate()
      elif should_simplify(): simplify()

```

Armin Biere presented a similar looking loop
