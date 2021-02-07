

The word problem is figuring out if two strings can be made equal to each other with a pile of allowable replacements.
It can be thought of in different ways and shows up in different domains. One way to talki about it is as figuring out equiavlaence for a finite presentation of a monoid. A finite presentation gives generators a,b,c let's say. The free monoid of these generators is just the strings you can make out these characters. The identity is the empty string and the monoid product is string concatenation. In a finite presentation, you also specify some equations like $ab=c$. Now it isn't obvious when two strings are equal or not.

There is however an obvious strategy to find equality. Just search. You can consider each string a node in a graph and eahc application of an equality somewhere in the string to be an edge on that graph. Keep trying equalities using dijsktra's algorithm, A* or what have you and then if you find a path connecting the two words, you proved equality.

A more satisfactory solution is to use a completion algorithm like Knuth Bendix. If Knuth bendix succeeds (a big if), the problem is in some sense solved for all words on the system. The output of the algorithm is a set of rewrite rules that bring words to a canonical form. You can just canonize words and compare to determine equality or disequality.

There are different approaches one might be inclined to take when modelling monoids in Z3. Z3 has a built in theory of strings, perhaps one could use arrays somehow, or one might axiomatize the theory using an uninterpeted sort.

Axiomaitizing the sort literally transcribes the axioms of a monoid. The thing that isn't great about this is that the associativity law of the monoid is a derivation and you're going to waste Z3's energy on reasoning about trivial facts of associativity. It is prefeably to have Z3 reason about something that is associative on the nose.

Well there is a neat trick. The big thing that is associative on the nose is function composition. Instead of representing monoid elements as objects, we represent them by a partial application of the monoid product. We can always turn this representation back by applying it to the identity of the monoid.
This representation is associative on the nose for Z3.




This trick extends to categories. In the context of Categories it is the Yoneda Embedding.

The trick can also extend to groups, although dealing with the inverse operation of the group ruins the cleanliness.

The paths through a surface form a category with vertices as objects and paths as morphisms. Homotopically equaivalent paths also form a category, a groupoid even.
There is something very tickling about using Z3 equality to express homotopy equivalence. It is very loosely reminisent of Homotopy Type Theory at a high level.


# Bits and Bobbles

- The underlying data structure here is the Egraph. Specializing EGraphs
- How to deal with higher homotopies?





