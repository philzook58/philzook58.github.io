Graph matching in the list monad style.
Brute force with pruning, just like everythign else.
I had the suggestion of graph matching via SAT solver. This is not as ridiculous as I first though.
A match is a relation between vertices and edges. V^2 + E^2 variables. 
We can perhaps suppress some of the variables (in exchange for clause complication)
For every vertex in pattern,
a_{vv'} =>


You can pattern match over trees.
Patterns match over dags
Over graphs.
A different dimension is pattern matching lambda terms.

Patterns themselves can have different aspects. You can have linear and nonlinear patterns. Guards.
Views maybe even

Ordered neighbors / children vs unordered. ML style pattern matching has ordered children

planar graphs are their own animal.

ullmann bitvector algorithms for binary constraint satisfcation
http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.681.8766&rep=rep1&type=pdf

https://stackoverflow.com/questions/17480142/is-there-any-simple-example-to-explain-ullmann-algorithm?rq=1

https://stackoverflow.com/questions/6743894/any-working-example-of-vf2-algorithm/6744603#6744603

VF2
http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.101.5342&rep=rep1&type=pdf

https://depth-first.com/articles/2008/11/13/one-of-these-things-is-not-like-the-other/
VFLib

Is this describing sparse set techniques like from the constraint satisifcation course?

https://networkx.org/documentation/stable/reference/algorithms/isomorphism.vf2.html

So is vf2 a bottom up partial match collecting algorithm?

Given patterns a priori, perhaps I can compile them to a datalog program.
Since I believe given a fixed pattern it is poly time with an expoenent that depends on the
pattern. This must be true right? Because brute force can be done with n loops.

Hmm. So maybe encoding to SAT is ridiculous? Oh and encoding to datalog isn't? THAT'S RICH

Actually, I think graph matching corresponds quite cleanly to a datalog query / clause (edited) 
subgraph_iso(v1,v2,v3,v4....) :- edge(v1, v3), edge(v2, v3), ...  .
For every edge in the pattern, have a edge predciate on the rhs
Very every vertex in the pattern, have a "v" variable in scope
And then have the graph you're seeking patterns in encoded in the edge predicate

For a fixed pattern, it is poly time.

Push vs pull. the naive loop
for v in allverts
  for v2 in allverts
     for v3 in allverts
        check_edge(v1,v3)
        ...
        yield (v1,v2,v3)

versus using the niehgbor lists.
You probably want to expand the highest edge count in the vertices first

Would datalog atuomatically find shared sub queries?  It might! Depends

CSV to souffle to CSV
dataframe or pandas.

But I also want to construct datalog programs
Var("s")
R = Relation("name" , t1,t2, t3  )

Basically julog syntax
R(x,y,z) << & & & 

program. 

If you have ordered nodes, instead of an edge relation you can have named node styles
named ports?

addnode(up, left, right)
mulnode(up, left, right)

Yeah.

https://www.red-gate.com/simple-talk/sql/t-sql-programming/binary-trees-in-sql/

ben in pandas

https://colab.research.google.com/drive/1rf5IMYxyCTD9w14rHgR4J3Ro3llz029F?usp=sharing
recursive common table rexpression


Graph matching 
The ematching I did was not special to egraphs really. It is all general graph matching

I don't super understand by subgraph isomorphism is considered hard
For small patterns it's not bad.
Yes for big loops and big complete graphs it is equivalent to problems that seem hard

Planar graphs - is this actually useful?
Circle packing
Feynamn diagramws and hashing subgraphs.

Ben's notebook. Using pandas
https://colab.research.google.com/drive/1rf5IMYxyCTD9w14rHgR4J3Ro3llz029F?usp=sharing#scrollTo=WDVu1zQjHPLx