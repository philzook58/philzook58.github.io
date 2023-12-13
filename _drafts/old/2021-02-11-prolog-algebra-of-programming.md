The algebra of programming has a couple main points

- Succintness is crucial for paper and pencil manipulation.
- Point free is good. Binding forms are hard to algebaically or computationally manipulate correctly. By excluding them, we get something closer to high school algebra.
- Extending functions to relations enriches algebraic manipulation and specification power. 

The goal to some degree is to specify as succintly and clearly as possible what the mathematically relationship you're trying to describe, and then through algebraic manipulation derive an efficiently executable form. Sound great.

You can make a nice naive model of relation algebra for finite relations (relations containing a finite number of elements but also defined over domains consisting of finite number of elements) using list comprehensions. Making this more efficient takes you into the field of database algorithms or relatedly datalog implementation. There is a lot of fat to trim.

The algebra of programming book emphasizes lattices of relations. Lattices in their usual examples form precision overapproximations of set operations. A polyhedron is a convex geometric object with flat sides. It can be represented concretely by listing the extremal vertices or by listing the linear inequalities for each flat face. The union of two polyhedra is not a polyhedra, but the convex hull of the union is. This convex hull is precise overapproximation of the union in the sense that it is the smallest polyhedra that contains both of the others. If we "tie our hands" and only allow ourselves the tool of polyhedra, it is the best we can do.
This tying of hands has extreme computational benefits though, and really it seems like we tie our hands to greater or less degree by choosing nearly any concrete representation of sets.

What we want is to include types that hold an infinite numbers of elements, like the integers, we might try to approach the problem in the same way as the finite case. We have to be careful though to use a fair interleaving search over lazy lists/generators.

An alternative presents itself with systems like prolog or minikanren. These languages are intrinsically more relational in flavor than others. They achieve this via being powered by unification, which is a kind of bidirectional pattern matching. Because they are intrinsically more relational it is easier to encode 

There is a very natural lattice for terms/trees/algebraic data types where you allow unification variable slots in the tree. This structure then represents the set of all terms that have any substitution into the variables. For example $foo(X, a)$ where $X$ is a variable represents the set $\{ f(a,a), foo(b,a), foo(bar(a), a), foo(baz(c,d),a)...   \}$. Intersection of these sets can be computed via the most general unifier, membership by pattern matching. This representing is not closed over union, just like polytopes. Instead the least general generalization https://en.wikipedia.org/wiki/Anti-unification_(computer_science) gives an overapproximation of the set. Just like polytopes, this representation has the ability to represent infinite sets via finite means.

Prolog and minikanren represent trees using this representation.

```scheme
(define (aopo prog a b)
  (conde
    ( (== prog 'id) (== a b) )

    ( (== prog  'fst ) (fresh (c) (== a (list 'tup b c)))  ) ; tup or no?
    ( (== prog  'snd ) (fresh (c) (== a (list 'tup c b)))  )

    ( (== prog  `(conv ,f)   (aopo f b a)  )     )
    ( (== prog  'inj1   )   (== b `(left ,a) ) )
    ( (== prog  'inj2   )   (== b `(right ,a) ) )
    ( (== prog  `(cata ,f )  (mapo f     )    ))
    (fresh (f g) 
      (conde 
         ((== prog  `(fan ,f ,g )          )
         ((== prog  `(comp ,f ,g) )  (aopo f a c) (aopo g c b) )
       )
       )
    )




  
  )


)


    car cdr projection. Lisp flavored aop should have lists as fundamental



(define (mapo f a b) 
   (conde
     (== a `(tup c d))  (aopo f c c2) (aopo f d d2)    )
     
   
   )

)


(define (functiono f)
   (conde
     ((== f 'id))
     ((== f 'fst))
     ((== f 'snd))
     ((== f 'inj1))
     ((== f 'inj2))
     ((== f `(comp ,f ,g)))
     ((== f 'id))

   )
)


(define (typo prog ta tb)

)

```



### Bits and Bobbles

Well typed haskell version
Template Haskell to turn relational programs to functional programs at compile time

prog = id . fst . (converse foo)

fastprog = Code (a -> b)
fastprog = search prog


https://free.cofree.io/2019/07/31/beautiful-bridges/ beautiful bridges algebra of programming blog post