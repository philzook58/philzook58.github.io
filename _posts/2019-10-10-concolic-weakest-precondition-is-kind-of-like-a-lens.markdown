---
author: philzook58
comments: true
date: 2019-10-10 03:54:18+00:00
layout: post
link: https://www.philipzucker.com/concolic-weakest-precondition-is-kind-of-like-a-lens/
slug: concolic-weakest-precondition-is-kind-of-like-a-lens
title: Concolic Weakest Precondition is Kind of Like a Lens
wordpress_id: 2361
categories:
- Formal Methods
- Haskell
tags:
- formal
- haskell
- lens
---




That's a mouthful.







Lens are described as[ functional getters and setters](http://hackage.haskell.org/package/lens-tutorial-1.0.4/docs/Control-Lens-Tutorial.html). The simple lens type is ``






    
    
```haskell

type Lens a b = a -> (b, b -> a)
```








. The setter is 






    
    
```haskell

a -> b
```








and the getter is 






    
    
```haskell

a -> b -> a
```








This type does not constrain lenses to obey the usual laws of getters and setters. So we can use/abuse lens structures for nontrivial computations that have forward and backwards passes that share information. [Jules Hedges](https://julesh.com/) is particular seems to be a proponent for this idea.







I've described before how to [encode reverse mode automatic differentiation](http://www.philipzucker.com/reverse-mode-differentiation-is-kind-of-like-a-lens-ii/) in this style. I have suspicions that you can make iterative LQR and guass-seidel iteration have this flavor too, but I'm not super sure. My attempts ended somewhat [unsatisfactorily](https://github.com/philzook58/ConvexCat/blob/master/src/Lib.hs) a whiles back but I think it's not hopeless. The trouble was that you usually want the whole vector back, not just its ends.







I've got another example in imperative program analysis that kind of makes sense and might be useful though. Toy repo here: [https://github.com/philzook58/wp-lens](https://github.com/philzook58/wp-lens)







In program analysis it sometimes helps to run a program both concretely and symbolically. [Concolic](https://en.wikipedia.org/wiki/Concolic_testing) = CONCrete / symbOLIC. Symbolic stuff can slowly find hard things and concrete execution just sprays super fast and can find the dumb things really quick.







We can use a lens structure to organize a DSL for describing a simple imperative language







The forward pass is for the concrete execution. The backward pass is for transforming the post condition to a pre condition in a [weakest precondition analysis](https://en.wikipedia.org/wiki/Predicate_transformer_semantics). Weakest precondition semantics is a way of specifying what is occurring in an imperative language. It tells how each statement transforms post conditions (predicates about the state after the execution) into pre conditions (predicates about before the execution). The concrete execution helps unroll loops and avoid branching if-then-else behavior that would make the symbolic stuff harder to process. I've been flipping through [Djikstra's book ](https://seriouscomputerist.atariverse.com/media/pdf/book/Discipline%20of%20Programming.pdf)on this. Interesting stuff, interesting man.







I often think of a state machine as a function taking `s -> s`. However, this is kind of restrictive. It is possible to have heterogenous transformations `s -> s'`. Why not? I think I am often thinking about finite state machines, which we really don't intend to have a changing state size. Perhaps we allocated new memory or something or brought something into or out of scope. We could model this by assuming the memory was always there, but it seems wasteful and perhaps confusing. We need to a priori know everything we will need, which seems like it might break compositionally.







We could [model our language](https://softwarefoundations.cis.upenn.edu/lf-current/Imp.html) making some data type like  
`data Imp = Skip | Print String | Assign String Expr | Seq Imp Imp | ...`  
and then build an interpreter 
    
    
```haskell

interp :: Imp -> s -> s'
```






![Imp.](/assets/Imp-01.jpg)





But we can also cut out the middle man and directly define our language using combinators. 
    
    
```haskell

type Stmt s s' = s ->s'
```








To me this has some flavor of a finally tagless style.







  
Likewise for expressions. Expressions evaluate to something in the context of the state (they can lookup variables), so let's just use  

    
    
```haskell

type Expr s a = s -> a
```








And, confusingly (sorry), I think it makes sense to use Lens in their original getter/setter intent for variables. So Lens structure is playing double duty.







`type Var s a = Lens' s a`







With that said, here we go. 






    
    
```haskell


type Stmt s s' = s -> s' 
type Lens' a b = a -> (b, b -> a)
set l s a = let (_, f) = l s in f a

type Expr s a = s -> a
type Var s a = Lens' s a

skip :: Stmt s s
skip = id

sequence :: Stmt s s' -> Stmt s' s'' -> Stmt s s''
sequence = flip (.)

assign :: Var s a -> Expr s a -> Stmt s s
assign v e = \s -> set v s (e s)

(===) :: Var s a -> Expr s a -> Stmt s s
v === e = assign v e

ite :: Expr s Bool -> Stmt s s' -> Stmt s s' -> Stmt s s'
ite e stmt1 stmt2 = \s -> if (e s) then stmt1 s else stmt2 s

while :: Expr s Bool -> Stmt s s -> Stmt s s
while e stmt = \s -> if (e s) then ((while e stmt) (stmt s)) else s

assert :: Expr s Bool -> Stmt s s  
assert e = \s -> if (e s) then s else undefined 

abort :: Stmt s s'  
abort = const undefined

```








Weakest precondition can be done similarly, instead we start from the end and work backwards







Predicates are roughly sets. A simple type for sets is  

    
    
```haskell

type Pred s = s -> Bool
```
 

Now, this doesn't have much deductive power, but I think it demonstrates the principles simply. We could replace `Pred` with perhaps an SMT solver expression, or some data type for predicates, for which we'll need to implement things like substitution. Let's not today. 







A function 
    
    
```haskell

a -> b
```
 

is equivalent to 
    
    
```haskell

forall c. (b -> c) -> (a -> c)
```


. This is some kind of CPS / Yoneda transformation thing. A state transformer 
    
    
```haskell

s -> s'
```


to predicate transformer 
    
    
```haskell

(s' -> Bool) -> (s -> Bool)
```


is somewhat evocative of that. I'm not being very precise here at all.







Without further ado, here's how I think a weakest precondition looks roughly.






    
    
```haskell


type Lens' a b = a -> (b, b -> a)
set l s a = let (_, f) = l s in f a

type Expr s a = s -> a
type Var s a = Lens' s a
type Pred s = s -> Bool
type Stmt s s' = Pred s' -> Pred s 

skip :: Stmt s s
skip = \post -> let pre = post in pre -- if

sequence :: Stmt s s' -> Stmt s' s'' -> Stmt s s''
sequence = (.)

assign :: Var s a -> Expr s a -> Stmt s s
assign v e = \post -> let pre s = post (set v s (e s)) in pre

(===) :: Var s a -> Expr s a -> Stmt s s
v === e = assign v e

ite :: Expr s Bool -> Stmt s s' -> Stmt s s' -> Stmt s s'
ite e stmt1 stmt2 = \post -> let pre s = if (e s) then (stmt1 post) s else (stmt2 post) s in pre

abort :: Stmt s s'  
abort = \post -> const False

assert :: Expr s Bool -> Stmt s s  
assert e = \post -> let pre s = (e s) && (post s) in pre

{-
-- tougher. Needs loop invariant
while :: Expr s Bool -> Stmt s s -> Stmt s s
while e stmt = \post -> let pre s = if (e s) then ((while e stmt) (stmt post)) s else  in pre
-}


```








Finally here is a combination of the two above that uses the branching structure of the concrete execution to aid construction of the precondition. Although I haven't expanded it out, we are using the full `s t a b` parametrization of lens in the sense that states go forward and predicates come back.






    
    
```haskell


type Lens' a b = a -> (b, b -> a)
set l s a = let (_, f) = l s in f a


type Expr s a = s -> a
type Var s a = Lens' s a
type Pred a = a -> Bool
type Stmt s s' = s -> (s', Pred s' -> Pred s) -- eh. Screw the newtype

skip :: Stmt s s
skip = \x -> (x, id)


sequence :: Stmt s s' -> Stmt s' s'' -> Stmt s s''
sequence f g =   \s -> let (s', j) = f s in
                       let (s'', j') = g s' in
                           (s'', j . j')
assign :: Var s a -> Expr s a -> Stmt s s
assign v e = \s -> (set v s (e s), \p -> \s -> p (set v s (e s)))

--if then else
ite :: Expr s Bool -> Stmt s s' -> Stmt s s' -> Stmt s s'
ite e stmt1 stmt2 = \s -> 
                    if (e s) 
                    then let (s', wp) = stmt1 s in
                         (s', \post -> \s -> (e s) && (wp post s))
                    else let (s', wp) = stmt2 s in
                            (s', \post -> \s -> (not (e s)) && (wp post s))

assert :: Pred s -> Stmt s s
assert p = \s -> (s, \post -> let pre s = (post s) && (p s) in pre)

while :: Expr s Bool -> Stmt s s -> Stmt s s
while e stmt = \s -> if e s then let (s' , wp) = (while e stmt) s in
                                 (s', \post -> let pre s'' = (post s'') && (wp post s'') in pre)   
                            else (s, \p -> p)

{-

-- declare and forget can change the size and shape of the state space.
-- These are heterogenous state commpands
declare :: Iso (s,Int) s' -> Int -> Stmt s s'   
declare iso defalt = (\s -> to iso (s, defalt), \p -> \s -> p $ to iso (s, defalt)) 

forget :: Lens' s s' -> Stmt s s' -- forgets a chunk of state

declare_bracket :: Iso (s,Int) s' -> Int ->  Stmt s' s' -> Stmt s s
declare_bracket iso defalt stmt = (declare iso default) . stmt . (forget (_1 . iso))

```








Neat. Useful? Me dunno.



