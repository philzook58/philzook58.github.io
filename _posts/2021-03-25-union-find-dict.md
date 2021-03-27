---
author: Philip Zucker
date: 2021-03-27
layout: post
title: "Union Find Dicts: Dictionaries Keyed on Equivalence Classes"
categories: julia
tags: julialang julia datastructures
---

Dictionary/map data structures usually have a set-like counter part. You get a Set data structure over the keys of a dict by just storing some dummy value such as `()`.

- Inserting element `k` in the set is dictionary insertion `d[k] = ()`
- Key lookup is the same thing as check set membership. `haskey(d,k)`
- Set union is dictionary merge.
- Enumerating elements of the set is enumerating the keys of the dict.

Not every set data structure is derived this way. BitSets for example are not really a dict you ignore the value in.
Nevertheless, hash and binary tree based Maps and Sets have this similarity to each other. They are largely the same except perhaps the set data structure is specialized to not even bothering to hold the default value.

The union find data structure is a way of storing disjoint unions of sets in such a way that the union operation remains fast. There is a pretty good explanation here <https://en.wikipedia.org/wiki/Disjoint-set_data_structure>

I want a version of union find that is a dictionary that stores values keyed on these equivalence classes. I mention why at the end (spoiler: [Egraphs](https://www.philipzucker.com/egraph-1/)).

I'm kind of surprised this abstract data structure interface is not commonly available. I couldn't find anything when I looked. It is only a very small addition to the regular union find.

## Basic Union Find Without Path Compression

You can find the DataStructures.jl version of the union find data structure with path compression here <https://github.com/JuliaCollections/DataStructures.jl/blob/master/src/disjoint_set.jl>. It's pretty readable, which is a nice aspect of Julia.

```julia
struct IntDisjointSet
    parents::Vector{Int64}
end
```
This stores and array of indices of the parents of the nodes.

```julia 
IntDisjointSet() = IntDisjointSet(Vector{Int64}[])
Base.length(x::IntDisjointSet) = length(x.parents)
```

Here we use a little trick, perhaps ill advised. When an item `j` is a root node, the storage at
x.parents[j] is redundant. One choice is to set `x.parents[j] = j` in this case. This is what the DataStructures.jl version does, and it does make some operations clean. Another is to use this space to store extra information. I used negatives numbers at the parent node pointer to represent the size of the tree. This allows union to easily place the smaller tree under the larger one. Hence creating a set of size 1 has a -1 put in its parents array here.

```julia
Base.push!(x::IntDisjointSet) = push!(x.parents, -1)
```

Here is a simple `find_root` loop. It traverses up the parent array. Here is a basic version of it where I stripped out path compression. Sacrilege you say? Perhaps. Path compression is kind of the cleverest and most confusing part.

```julia
function find_root(x::IntDisjointSet, i::Int64)
    while x.parents[i] >= 0
        i = x.parents[i]
    end
    return i
end
```

The union operation is almost interesting. It sets the parent of the smaller tree to the larger one. This has a tendency to keep the trees shallow. You could also use the rank of the subtree. In the absence of path compression, the rank is the height.

```julia
function Base.union!(x::IntDisjointSet, i::Int64, j::Int64)
    pi = find_root(x, i)
    pj = find_root(x, j)
    if pi != pj
        isize = -x.parents[pi]
        jsize = -x.parents[pj]
        if isize > jsize # swap to make size of i less than j
            pi, pj = pj, pi
            isize, jsize = jsize, isize
        end
        x.parents[pj] -= isize # increase new size of pj
        x.parents[pi] = pj # set parent of pi to pj
    end
    return pj
end
```

I have some suspicion for a use case that normalizing the parent pointers all at once in a batch might be kind of nice. Then further lookups are no longer mutating and can more easily be done in parallel and without a loop. Depends on your usage pattern.

```julia
function normalize!(x::IntDisjointSet)
    for i in length(x)
        pi = find_root(x, i)
        if pi != i
            x.parents[i] = pi
        end
    end
end

# If normalized we don't even need a loop here.
function _find_root_normal(x::IntDisjointSet, i::Int64)
    pi = x.parents[i]
    if pi < 0 # Is `i` a root?
        return i
    else
        return pi
    end
end
```


A question I had is if it was possible to make a dictionary structure that is keyed on equivalence classes. Yes, it is, With some caveats.

You need to define what you want to happen to the values when two equivalance class keys merge. I think a reasonable requirement is that values held in the are combined using an associative and commutative operation, since you are unlikely to be able to predict these orderings. It is tempting to think that this should be a semilattice (idempotent) but it is not necessary.
If you wanted to use arrays with array concatenation for example, expect the order of the array to be scrambled.


```julia
struct IntDisjointMap
    parents::Vector{Int64}
    values::Vector{Any}
    merge_fun
end

IntDisjointMap(merge_fun) = IntDisjointMap(Vector{Int64}[], [], merge_fun)
```

Most of the previous definitions stay the same. We do have to change the definition of union and we can add new definitions for retrieving and updating the dict.

```julia
Base.getindex(x::IntDisjointMap, i::Int64) = x.values[find_root(x,i)]
Base.setindex!(x::IntDisjointMap, v, i::Int64) = x.values[find_root(x,i)] = v


function Base.union!(x::IntDisjointMap, i::Int64, j::Int64)
    pi = find_root(x, i)
    pj = find_root(x, j)
    if pi != pj
        isize = -x.parents[pi]
        jsize = -x.parents[pj]
        if isize > jsize # swap to make size of i less than j
            pi, pj = pj, pi
            isize, jsize = jsize, isize
        end
        x.parents[pj] -= isize # increase new size of pj
        x.values[pj] = x.merge_fun(x.values[pj], x.values[pi])
        x.values[pi] = nothing # clear out unused storage
        x.parents[pi] = pj
    end
    return pj
end
```

Some usage storing integers in the Map using + as a merge operation

```julia
using Test
G = IntDisjointMap(+)
push!(G, 1)
@test G.parents == [-1]
@test G.values == [1]
push!(G,14)
@test G.parents == [-1, -1]
@test G.values == [1, 14]
@test G[1] == 1
@test G[2] == 14
union!(G,1,2)
@test G.parents == [2,-2]
@test G.values == [nothing, 15]
@test G[1] == 15
@test G[2] == 15
push!(G, 4)
@test find_root(G,1) == 2
@test find_root(G,2) == 2
@test find_root(G,3) == 3
union!(G,1,3)
@test G[3] == 19
@test find_root(G,3) == 2
@test find_root(G,1) == 2
@test G.parents == [2,-3,2]

G[3] = 42
@test G[2] == 42
```

### Why?

Well, I think the the IntDisjointMap is a missing obvious intersection of abstract data type interfaces.

I've been playing around with EGraphs lately <https://www.philipzucker.com/egraph-1/>, and they involve a bipartite graph between Equivalence classes and ENodes, which are tern nodes with the children replaced by EClass Ids. A fairly minimal representation of such a structure would be an IntDisjointMap holding `ENode`s.

```julia
struct ENode
    head::Symbol
    args::Vector{Int64}
end
```

I'm kind of hoping to make a very minimal, perhaps inefficient implementation of the essence of egraphs.


### Notes

Structures mapping equivalence classes to terms also show up in unification.

There is no impediment to implementing this interface over a full path compressed union find.
It is also possible to implement this as a wrapper over a normal union find, at the expense of some unnecessary find operations

```julia
struct IntDisjointMap
    unionfind::IntDisjointSet
    values::Vector{Int64}
    merge_fun
end
```

I think that perhaps using Parametric types like so may give a speed boost as Julia specializes on types.

```julia
struct IntDisjointMap{V}
    parents::Vector{Int64}
    values::Vector{V}
    merge_fun
end
```

Even further, putting a tag of the merge_fun in the type might do something good specializing in that function call.

```julia
struct IntDisjointMap{V, merge_fun}
    parents::Vector{Int64}
    values::Vector{V}
end
```

