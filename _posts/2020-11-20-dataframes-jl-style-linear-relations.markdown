---
author: philzook58
comments: true
date: 2020-11-20 01:05:56+00:00
layout: post
link: https://www.philipzucker.com/dataframes-jl-style-linear-relations/
slug: dataframes-jl-style-linear-relations
title: DataFrames.jl Style Linear Relations
wordpress_id: 3008
categories:
- Julia
- Physics
tags:
- dataframes
- julialang
- pandas
- relations
---




DataFrames.jl is a Julia library to store, retrieve and manipulate tabular data. It is the analog of Pandas for python or related tools in R.  It implements an interface that is a mish-mash of numpy-like slicing and SQL-like queries and can be used as  lightweight flexible relational database. It has proven to be a popular and intuitive interface.







[Relational Databases](https://en.wikipedia.org/wiki/Relational_database) are computer implementations of the mathematical concept of finite relations, but there are other classes of relations. This blog post is about using (abusing?)  the DataFrame.jl interface to implement linear relations. Linear relations are useful for describing physical systems whose behavior is constrained by linear equations, such as electrical circuits.







It all comes out quite cute.







### Databases and Relations







A [finite relation](https://en.wikipedia.org/wiki/Finitary_relation) over sets A,B,C,D is a subset of $ A\times B \times C \times D $ . In the database, each of these sets corresponds to a column of the database, and each element of the subset corresponds to a row of the database.







Much of the time, we think of storing discrete data in databases, things like names, ids, occupations, ages. However, DataFrame.jl is certainly also capable of storing floats. In this case, the DataFrame could be interpreted as storing a finite number of points in the continuous space $ R^n $, one dimension for each column, one point for each row.







In continuous space, it is desirable to not only describe discrete sets of points, but also blobs. Conceptually,  blobs are only a subset of $ R^n$, and are still a mathematical relation. In some sense a blob could be thought of as the contents of a database holding an uncountable number of rows, but then the enumerative storage schemes of an actual physical database doesn't cut it anymore. We need an extremely compressed storage scheme.







## Describing Linear Subspaces







Trying to store arbitrary blobs is a bit too unruly, but if we constrain ourselves to certain classes of blobs, we can still make headway. In this case, we are going to stick to linear blobs, i.e. hyperplanes.







One can concretely describe a hyperplane of $ R^n$ by two main representations. First one can list a set of vectors $ \{v_i \}$ that span the hyperplane. From this list, we are implicitly describing any linear combination of these vectors $ v = \sum \lambda_i v_i $. A second distinct representation is to list the coefficient vectors $ \{c_i^T \}$ of a set of linear equations $ \{ c_i^T v = 0 \}$ describing the hyperplane. I will call these the span and constraint representations.







An alternative name for these two representations might be the range and nullspace representation, the generator and equation representation, or by analogy to polyhedral computation, the v-rep and h-rep.







These two representations are dual in some sense. One way in which they feel dual is that adding a new non independent vector to the span increases the dimensionality of the linear subspace by 1. Adding a new independent linear equation to the constraint rep decreases the dimension of the subspace by 1. 







It is important to have both representations because different operations on linear subspaces are easy in each. The intersection of two subspaces is easy in the constraint representation. It corresponds to just concatenating two constraint sets. Projection is easy in the span representation where it corresponds to just taking a slice out of each individual generator vector.







As more evidence for the two representation's duality, two other important operations that are easy in a particular representation are the image and preimage operations under linear maps. The image is easy to compute in the span representation (matrix multiply $ {Av_i}$) and the preimage is easy in the constraint representation (matrix multiply maybe with a transpose thrown in there $ {c_i^T A}$).







## The Julia Implementation







The interface of DataFrames still makes sense for linear relations and we can slightly abuse its already existent machinery to make fast headway. 







First the constructors of the two representations. As a slight hack, to differentiate between the two representations, I will tag a special blank column to differentiate which representation we are in. Otherwise I forward all arguments to the ordinary DataFrames constructor so you can build these as you would any DataFrame. Each row of the dataframe is either one vector from the span set or one constraint from the constraint set. Column are components of these vectors






    
    
```julia

using DataFrames
using LinearAlgebra

function DataFrameSpan( x...; kwargs...)
    df = DataFrame(x...; kwargs...)
    df[:spanrep] = 0 # missing
    df
end

# representing linear relations via constraints
function DataFrameCons( x...; kwargs...)
    df = DataFrame(x...; kwargs...)
    df[:consrep] = 0 # missing
    df
end
```








Because each individual vector in the span obeys the constraint equations, we can numerically convert between them by calling the Julia function `[nullspace](https://docs.julialang.org/en/v1/stdlib/LinearAlgebra/#LinearAlgebra.nullspace)`. There is a pleasing symmetry between the two conversion directions.






    
    
```julia

# nullconvert turns span rep to constraint rep or vice versa
function nullconvert(df)
    cols = names(df)
    A = nullspace(Matrix(df))

    DataFrame(mapslices(x->[x], A, dims=2)[:] , cols ) 
end

#https://discourse.julialang.org/t/converting-a-matrix-into-an-array-of-arrays/17038/2


# We tag somewhat inelegantly whether we're inb the span rep or constrain rep via a column tag
isspanrep(x) = "spanrep" ∈ names(x)
isconsrep(x) = "consrep" ∈ names(x)


function spanrep(x) 
    if isspanrep(x)
        return x
    else
        df = select(x, Not(:consrep))
        df = nullconvert(df)
        df[:spanrep] = 0 #add tag
        return df
    end
end

function consrep(x) 
    if isconsrep(x)
        return x
    else
        df = select(x, Not(:spanrep)) #remove tag
        df = nullconvert(df)
        df[:consrep] = 0 #add tag 
        return df
     end
end


```








The ability to name columns and the analog of the join operation from database gives us a way to compositionally construct systems of linear equations. We also define a projection operations which in some sense solves these equations.






    
    
```julia

function linearjoin(df,dg)  #should we add makefresh flag?
        df = consrep(df)
        dg = consrep(dg)
        coalesce.(vcat(df,dg, cols=:union), 0)
end


function linearproject(df, cols)
        df = spanrep(df)
        df = df[ [cols ; :spanrep]]
end
```








And shockingly, that's about it. A very elegant implementation compared to my previous efforts.







Here as an example we join two resistors in series. We then project out the inner voltage, which returns a relation describing the 






    
    
```julia

resistor(R, i , v1, v2) = DataFrameCons( [i => [R], v1 => [1], v2 => [-1] ] )
vsource(V, v1, v2) =  DataFrameCons( [:one => [V], v1 => [1], v2 => [-1] ] )
isource(I, i) =  DataFrameCons( [:one => [I], i => [-1] ] )

r1 = resistor(10, :i1, :v1, :v2)
r2 = resistor(10, :i1, :v2, :v3)


sys = consrep(linearproject(linearjoin(r1,r2), [:i1, :v1, :v3]) ) 
```







    
    
```

1×4 DataFrame
│ Row │ i1       │ v1        │ v3         │ consrep │
│     │ Float64  │ Float64   │ Float64    │ Int64   │
├────┼──────────┼───────────┼────────────┼─────────┤
│ 1   │ 0.997509 │ 0.0498755 │ -0.0498755 │ 0       │

```








This solution is linear proportional to `[20,1,-1]`  hence representing the linear relation of a 20ohm resistor.







For more examples of usage of linear relations, check out these blog posts.







  * [https://www.philipzucker.com/linear-relation-algebra-of-circuits-with-hmatrix/](https://www.philipzucker.com/linear-relation-algebra-of-circuits-with-hmatrix/)
  * [https://www.philipzucker.com/checkpoint-implementing-linear-relations-for-linear-time-invariant-systems/](https://www.philipzucker.com/checkpoint-implementing-linear-relations-for-linear-time-invariant-systems/)
  * [https://www.philipzucker.com/solving-the-laplace-equations-with-linear-relations/](https://www.philipzucker.com/solving-the-laplace-equations-with-linear-relations/)
  * [https://www.philipzucker.com/categorical-lqr-control-with-linear-relations/](https://www.philipzucker.com/categorical-lqr-control-with-linear-relations/)






That one could use pandas or Dataframes.jl in this way is something I realized about a year ago when I was writing these posts, but I didn't realize how pleasantly it would all fall out when I actually sat down to do it.







### Bits and Bobbles







  * One often wants not only linear subspaces, but [affine subspaces](https://en.wikipedia.org/wiki/Affine_space#:~:text=first%20Weyl's%20axioms.-,Affine%20subspaces%20and%20parallelism,is%20a%20linear%20subspace%20of%20.). The convenient and standard trick to convert affine subspaces to linear subspaces is the method of [homogenous coordinates](https://en.wikipedia.org/wiki/Homogeneous_coordinates). We can increase our linear space with an extra dimension called `:one`. Whenever we need a scalar occurring in an equation, it now goes in front of this new variable. In the span representation, it is convenient to normalize this entry to 1 by scaling the each span vector. Then the span representation representing the affine subspace is $ \sum \lambda_i v_i$ with the constraint that $ \sum \lambda_i = 1$.





  * Linear relations are not the only sensible relations. Other classes of relations that have computational teeth include





  1. Polyhedral relations [https://github.com/JuliaPolyhedra/Polyhedra.jl](https://github.com/JuliaPolyhedra/Polyhedra.jl)
  2. Polynomial Relations (aka algebraic or semialgebraic relations) [https://www.juliahomotopycontinuation.org/](https://www.juliahomotopycontinuation.org/)
  3. Convex relations [https://juliareach.github.io/LazySets.jl/dev/](https://juliareach.github.io/LazySets.jl/dev/)






It seems reasonable that each of these could also use the DataFrames interface as a way of modelling themselves.







  * Linear relations elegantly express operations I would ordinarily phrase in terms of Schur complements, one of my favorite pieces of linear algebra. Projecting a linear relation is finding the effective or reduced system of equations.






In this manner, linear relations are related to Gaussian integrals, which are the canonical example of "integrating out" dynamics in physics. Multidimensional Gaussian integrals are ultimately basically linear algebra engines, giving a way to formulate the Schur complement operation.  I think linear relations would form a good core for an "exact" Gaussian integral library.







Quadratic Optimization with linear equality constraints is reducible to a linear relation. I used this for example in my LQR control example above. This is also related to Gaussians, since[ the method of steepest descent](https://en.wikipedia.org/wiki/Method_of_steepest_descent) approximates an integration problem by an optimization problem. Gaussian integrals in the presence of linear delta functions $ \delta(Ax-b)$ (which are important) convert under the steepest descent method to a quadratic optimization problem with linear equality constraints. All of this is completely ubiquitous in the connection between classical and quantum mechanics, and between statistical and thermodynamics. The Feynman integration over all paths becomes the principle of least action. The partition function integrals become free energy minimizations.







  * In the past, I've modeled relations in a Categorical style. This is still I think an excellent internal representation, but perhaps not the best user facing interface.






[Query optimization](https://en.wikipedia.org/wiki/Query_optimization) is a big topic in database theory.  The ordering of the joins and projections and the chosen points at which to change representations or indices can greatly change the time of the query. It is intriguing that such disparate seeming calculations may benefit from a unified relational query optimizer. I suggest that a categorical IR and the tools of Catlab [https://github.com/AlgebraicJulia/Catlab.jl](https://github.com/AlgebraicJulia/Catlab.jl) might be a way to do this.







  * Using sparse matrices would be a boon to linear relations (they tend to be very sparse), but we may have to roll our own DataFrame implementation to do so.
  * Should we allow columns to have width? Then variables can represent blocks of the matrix rather than just a single component. It feels like this has nice modelling power. It was also not convenient to do so with the stock DataFrame implementation


