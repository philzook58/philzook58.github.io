


There's a new sheriff in town.

About a year ago, I was tinkering with a prototype egglog0. On parallel lines Yihong, Max, Remy, Eli, and Zach were developing

It has 

# What can you do with it?


# What is it?
The core capability is term rewriting.

Traditional term rewriting 
Set-term rewriting

Not multiset rewriting. CHR has a notion of resource that we do not.

An egraph _is_ basically a data structure set of terms with a notion of equality between them. It consists of a bipartite graph of enodes and eclasses. 
Forests can share subtrees easily just by sharing the pointer to a child. Then the tree becomes a DAG. This optimization is sometimes called hash-consing.

Conversely, if you 

The indirection that 





# How does it work?

First off, egglog is in essence basically a datalog.

Here are some introductory materials on datalog. Diehl, Datafun thesis, my mdbook


# Optimization
The big draw of the equality saturation work is the promise of reliable term rewriting systems.
Program optimizers usually have some kind of simplifier in them.


# Relationship to SMT

THe big weakness of SMT is the questions you can ask it.

Gas, triggers, ad multipatterns.

SMT makes non justifiable guesses.



# Justifiable Automated Theorem Proving

The thing that is most appealing to me is that egglog represents the core of a justifiable theorem prover.
It share this proprty with datalog. Datalog rules are inference rules. The execution trace of a datalog engine is exactly forward inference theorem proving. This trace /proof/provenance can be stored and extracted efficiently.

Traditional datalog is so weak to be almost unusable to talk about typical algebraic mathemtical statements (for better and worse). The addition

Dependent types and higher order logic are all the rage

"you can play computer"

In a theorem prover based fundamentally in total functions and classical logic, you need to make sure you're encoding accounts for every possibility. This is hard. The thing is sneaky. One is tempted to take a semi-operational viewpoint of your axioms.

 



There are many convergent threads from independent angles.
There seems to be something in the air with regards to flattened datalog. 
I was recently surprised and disturbed to find another project going along parallel lines Eqlog.
