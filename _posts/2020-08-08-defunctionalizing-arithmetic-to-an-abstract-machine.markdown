---
author: philzook58
comments: true
date: 2020-08-08 18:31:45+00:00
layout: post
link: https://www.philipzucker.com/defunctionalizing-arithmetic-to-an-abstract-machine/
slug: defunctionalizing-arithmetic-to-an-abstract-machine
title: Defunctionalizing Arithmetic to an Abstract Machine
wordpress_id: 2914
categories:
- Formal Methods
- Haskell
tags:
- abstract machine
- compiler
---




There is great value in meditating upon the simplest possible example of a thing you can come up with. In this case one can apply defunctionalization techniques that are often applied to lambda calculus to simpler arithmetic calculations.







Functional programming is cool and useful, but it isn't clear how to implement the features they provide on hardware that is controlled by assembly code. Achieving this is a fairly large topic. One step on the way is the concept of an abstract machine.







Abstract machines make more explicit how to evaluate a program by defining a step relationship taking a state of the machine to another state. I think this may be closer to how hardware is built because hardware is physical system. Physical systems are often characterizable by their space of states and the transitions or time evolution of them. That's Newtonian mechanics in a nutshell.







There is a methodology by which to connect the definitions of abstract machines to interpreters of lambda calculus.







  * Convert to continuation passing style to make the evaluation order explicit
  * Defunctionalize these continuations






However, the lambda calculus is a non trivial beast and really only a member of a spectrum of different programming language features. Here is an incomplete set of features that you can mix and match:







  * Arithmetic expressions
  * Boolean expressions
  * let bindings
  * Printing/Output
  * Reading/Input
  * Mutation, References
  * For/While loops
  * Named Global Procedures
  * Recursion
  * Lambda terms / Higher Order Functions
  * Call/CC
  * error throw try catch
  * Algebraic Data Types
  * Pattern matching






In my opinion, the simplest of any of these is arithmetic expressions and with only this you can already meaningfully explore this evaluator to abstract machine translation.







First we need a data type for arithmetic






    
    
```

data AExpr = Lit Int | Add AExpr AExpr deriving (Eq, Show)
```








Pretty basic. We could easily add multiplication and other operators and it doesn't change much conceptually except make things larger. Then we can define a simple interpreter.






    
    
```

type Value = Int

eval :: AExpr -> Value
eval (Add x y) = (eval x) + (eval y)
eval (Lit i) = i
```








The first step of our transformation is to put everything in continuation passing style (cps). The way this is done is to add an extra parameter `k` to every function call.  When we want to return a result from a function, we now call `k` with that instead. You can kind of think of it as a goofy `return` statement. `eval'` is equivalent to `eval` above.






    
    
```

evalk :: AExpr -> (Value -> Value) -> Value
evalk (Add x y) k = evalk x (\vx -> (evalk y $ \vy -> k (vx + vy)))
evalk (Lit i) k = k i

eval' :: AExpr -> Value
eval' e = evalk e id
```








Now we defunctionalize this continuation. We note that higher order continuation parameters take only a finite number of possible shapes if `evalk` is only accessed via the above code. `k` can either be `id`, `(\vx -> (evalk y $ \vy -> k (vx + vy)))` , or `\vy -> k (vx + vy)`. We give each of these code shapes a constructor in a data type. The constructor needs to hold any values closed over (free variables in the expression). `id` needs to remember nothing, `\vx -> (evalk y $ \vy -> k (vx + vy))` needs to remember `y` and `k`, and `\vy -> k (vx + vy)` needs to remember `vx` and `k`.






    
    
```

data AHole = IdDone | AddL AExpr AHole | AddR Value AHole 
```








What functions _are_ is a thing that can be applied to it's arguments. We can use `AHole` exactly as before by defining an `apply` function.






    
    
```

apply :: AHole -> Value -> Value 
apply IdDone      v = v
apply (AddL e k)  v = evald e (AddR v k)
apply (AddR v' k) v = apply k (v' + v) 
```








And using this we can convert `evalk` into a new form by replacing the continuations with their defunctionalized data type.






    
    
```

evald :: AExpr -> AHole -> Value
evald (Add x y) k = evald x (AddL y k)
evald (Lit i) k = apply k i

eval'' e = evald e IdDone
```








We can make this into more of a machine by inlining `apply` into `evald` and breaking up the tail recursion into individual steps. Now we have a step relation on a state consisting of continuation data `AHole` and program information `AExpr`. Every step makes progress towards evaluating the expression. If you squint a little, this machine is basically an [RPN machine](http://learnyouahaskell.com/functionally-solving-problems) for evaluating arithmetic.






    
    
```

data Machine = Machine {  prog :: AExpr  , kont :: AHole}

step :: Machine -> Either Value Machine
step (Machine (Add x y) k) = Right $ Machine x (AddL y k)
step (Machine (Lit i) (AddL e k)) = Right $ Machine e (AddR i k)
step (Machine (Lit i) (AddR v k)) = Right $ Machine (Lit (i + v)) k
step (Machine (Lit i) (IdDone)) = Left i

init_machine e = Machine e IdDone

-- https://hackage.haskell.org/package/extra-1.7.4/docs/src/Control.Monad.Extra.html#loop
loop :: (a -> Either b a) -> a -> b
loop act x = case act x of
    Right x -> loop act x
    Left v -> v

eval'''' e = loop step (init_machine e)
```








Pretty neat right?





![](/assets/face.gif)Artwork Courtesy of [David](https://davidtersegno.wordpress.com/)





Now the next simplest steps in my opinion would be to add Booleans, Let expressions, and Print statements. Then after grokking that, I would attempt the CEK and Krivine Machines for lambda calculus.





![](/assets/ec171a6b-08ee-4000-8c74-11b658435937.png)Artwork Courtesy of [David](https://davidtersegno.wordpress.com/)





### Links







Defunctionalizing arithmetic can be found in [https://www.brics.dk/RS/01/23/BRICS-RS-01-23.pdf](https://www.brics.dk/RS/01/23/BRICS-RS-01-23.pdf) - Defunctionalization at Work - Danvy and Nielson







[https://homepages.inf.ed.ac.uk/wadler/papers/papers-we-love/reynolds-definitional-interpreters-1998.pdf](https://homepages.inf.ed.ac.uk/wadler/papers/papers-we-love/reynolds-definitional-interpreters-1998.pdf) Definitional Interpreters for Higher Order Programming Languages - Reynolds 1972. The grand daddy paper of defunctionalization







[https://tidsskrift.dk/brics/article/download/21784/19215](https://tidsskrift.dk/brics/article/download/21784/19215) - A Journey from Interpreters to Compilers and Virtual Machines - Mads Sig Ager, Dariusz Biernacki, Olivier Danvy,  
Jan Midtgaard







[http://www.pathsensitive.com/2019/07/the-best-refactoring-youve-never-heard.html](http://www.pathsensitive.com/2019/07/the-best-refactoring-youve-never-heard.html) Best Refactoring You've never Heard of by Jimmy Koppel.







Xavier Leroy abstract machine slides [https://xavierleroy.org/mpri/2-4/](https://xavierleroy.org/mpri/2-4/)







[https://caml.inria.fr/pub/papers/xleroy-zinc.pdf](https://caml.inria.fr/pub/papers/xleroy-zinc.pdf) - Leroy's description of the Zinc Machine







CEK machine - Matt Might [http://matt.might.net/articles/cek-machines/](http://matt.might.net/articles/cek-machines/)







[https://github.com/rain-1/continuations-study-group/wiki/Reading-List](https://github.com/rain-1/continuations-study-group/wiki/Reading-List)







[https://semantic-domain.blogspot.com/2020/02/thought-experiment-introductory.html](https://semantic-domain.blogspot.com/2020/02/thought-experiment-introductory.html) Neel Krishnaswami's hypothetical compiler course.







[http://www.cs.nott.ac.uk/~pszgmh/ccc.pdf](http://www.cs.nott.ac.uk/~pszgmh/ccc.pdf) Calculating Correct Compilers - Bahr and Hutton 















