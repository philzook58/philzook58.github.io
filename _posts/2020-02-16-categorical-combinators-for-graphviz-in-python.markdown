---
author: philzook58
comments: true
date: 2020-02-16 20:33:09+00:00
layout: post
link: https://www.philipzucker.com/categorical-combinators-for-graphviz-in-python/
slug: categorical-combinators-for-graphviz-in-python
title: Categorical Combinators for Graphviz in Python
wordpress_id: 2661
categories:
- Formal Methods
tags:
- categorytheory
- graphviz
- python
---




Graphviz is a graph visualization tool [https://www.graphviz.org/](https://www.graphviz.org/). In Conal Elliott's Compiling to categories [http://conal.net/papers/compiling-to-categories/](http://conal.net/papers/compiling-to-categories/), compiling code to its corresponding graphviz representation was one very compelling example. These graphs are very similar to the corresponding string diagram of the monoidal category expression, but they also look like boolean circuit diagrams. Besides in Conal Elliott's Haskell implementation, there is an implementation in the Julia Catlab.jl project [https://epatters.github.io/Catlab.jl/stable/](https://epatters.github.io/Catlab.jl/stable/)







I've basically implemented a toy version of a similar thing in python. It lets you do things like this





[gist https://gist.github.com/philzook58/50209a590fb294849699e034875fd762#file-adder-py]



![](http://philzucker2.nfshost.com/wp-content/uploads/2020/02/adders.png)





Why python?







  * Python is the lingua franca of computing these days. Many people encounter it, even people whose main thing isn't computers.
  * The python ecosystem is nutso good.
  * Julia is kind of an uphill battle for me. I'm fighting the battle ( [https://github.com/philzook58/Rel.jl](https://github.com/philzook58/Rel.jl) ) , but I already know python pretty well. I can rip this out and move on. 






What I did was implement some wrappers around the graphviz python package. It exposes a not very feature rich stateful interface. It is pretty nice that it prints the graphs inline in jupyter notebooks though.







The code is written in a style very similar (and hopefully overloadable with)  to that of z3py relation algebra. [http://www.philipzucker.com/a-sketch-of-categorical-relation-algebra-combinators-in-z3py/](http://www.philipzucker.com/a-sketch-of-categorical-relation-algebra-combinators-in-z3py/) . There is a fairly general cookbook method here for categorifying dsl.  Since graphviz does not directly expose fresh node creation as far as I can tell, I made my own using a random number generator. The actual combinators are graphviz object processors, so we build up a giant functional chain of processors and then actually execute it with `run`. The inputs and outputs are represented by lists of node names. The is some design space to consider here.







I also had to use class based wrappers Based on the precedent set by the python 3 matrix multiplication operator @, I think it is a requirement that this also be used for category composition. `id` is a keyword or something in python unfortunately. For monoidal product, I feel like overloading power ** looks nice even if it is a nonsensical analogy, * is also not too bad. I went with * for now.







The graphviz graphs aren't quite string diagrams. They make no promise to preserve the ordering of your operations, but they seem to tend to.





[gist https://gist.github.com/philzook58/50209a590fb294849699e034875fd762#file-graphcat-py]





Here's some example usage






    
    <code>cup = GraphCat.cup()
    cap = GraphCat.cap()
    d =  cap @ (I * I) @ cup  #(I * cap) @ (I * I * I) @ (cup * I) 
    d.run()</code>





![](http://philzucker2.nfshost.com/wp-content/uploads/2020/02/cupcap.png)




    
    <code>d = plus @ (GC.const(1) * GC.const(2))
    d = d.run()
    </code>





![](http://philzucker2.nfshost.com/wp-content/uploads/2020/02/adders-1.png)




    
    <code>GC = GraphCat
    f = GraphCat.named_simple("f")
    g = GraphCat.named_simple("g")
    I = GraphCat.idd()
    dump = GC.dump()
    dup = GC.dup()
    diagram = ((f * I) @ dup @ g @ (dump * I)  @ (I * f) @ (f * f)) * g
    diagram.run()</code>





![](http://philzucker2.nfshost.com/wp-content/uploads/2020/02/randomstuff.png)





Class based overloading is the main paradigm of overloading in python. You overload a program into different categories, by making a program take in the appropriate category class as a parameter. 






    
    <code># by passing in different category classes, we can make polymorphic functions
    # They have to have a uniform interface though, which is hard to constrain in python.
    def polymorphic_prog(M):
        idd = M.idd()
        dump = M.dump()
        dup = M.dup()
        return (idd * dump) @ dup
    polymorphic_prog(GraphCat).run()</code>







For example something like this ought to work. Then you can get the graph of some matrix computation to go along with it's numpy implementation






    
    <code>class FinVect(np.ndarray):
    
        def compose(f,g):
            return f @ g
        def idd(n):
            return np.eye(n)
        def par(f,g):
            return np.kron(f,g)
        def __mult__(self,rhs):
            return np.kron(f,g)
    # and so on. </code>







Maybe outputting tikz is promising? [https://github.com/negrinho/sane_tikz](https://github.com/negrinho/sane_tikz)



